(**
   Langages, sémantiques et modèles d'exécution.
   Thibaut Balabonski @ Université Paris-Sud, 2018

   TP types, sous-types, polymorphisme et inférence.
   L'objectif de ce TP est de réaliser un système de typage pour un langage
   mélangeant des traits fonctionnels et impératifs.
*)

(**
   Exercice 1 : vérification des types simples.

   Langage de départ :
     lambda-calcul + constantes + paires + références + structures de contrôle
   avec annotations de types.

   Objectif : vérification des types.
*)

(** Types simples *)
module SimpleTypes = struct

  type typ =
    | TVar of string      (** Variables de type ['a] *)
    | TInt                (** Entiers [int]          *)
    | TBool               (** Booléens [bool]        *)
    | TUnit               (** Unité [unit]           *)
    | TFun  of typ * typ  (** Fonctions [T₁ ⟶ T₂]   *)
    | TPair of typ * typ  (** Paires [T₁ * T₂]       *)
    | TRef  of typ        (** Références [ref T]     *)

end

(** Expressions avec annotations de types *)
module BaseAST = struct

  type expression =
    | Int    of int    (** Entier [n]    *)
    | Bool   of bool   (** Booléen [b]   *)
    | Unit             (** Unité [()]    *)
    | Var    of string (** Variable  [x] *)
    | App    of expression * expression
                       (** Application [e₁ e₂] *)
    | Fun    of string * SimpleTypes.typ * expression
                       (** Fonction [fun x:T -> e] *)
    | Let    of string * expression * expression
                       (** Liaison [let x=e₁ in e₂] *)
    | Op     of string (** Opérateur *)
    | Pair   of expression * expression
                       (** Paire [(e₁, e₂)] *)
    | NewRef of expression
                       (** Création d'une référence initialisée [ref e] *)
    | Sequence of expression * expression
                       (** Séquence d'expressions [e₁; e₂] *)
    | If     of expression * expression * expression
                       (** Conditionnelle [if c then e₁ else e₂] *)
    | While  of expression * expression
                       (** Boucle [while c do e done] *)

  (**
      Ensemble minimal d'opérateurs à prévoir pour le constructeur [Op]
      - arithmétique et logique :  "+", "<", "&&"
      - paires "fst", "snd"
      - références "deref", "setref"
  *)
end

(**
   Vérificateur de types.
*)
module BaseTypeChecker = struct
  open SimpleTypes
  open BaseAST

  module Env = Map.Make(String)
  type type_env = SimpleTypes.typ Env.t

  (**
      Objectif : compléter la fonction suivante de typage d'une expression.
      Un appel [type_expression env e] doit :
      - renvoyer le type de [e] dans l'environnement [env] si [e] est bien typée
      - déclencher une exception sinon
  *)
  let rec type_expression (env: type_env) (e: expression) : typ =

    let te = type_expression env in
    let find_typ name = Env.find name env in
    let add_var name typ = Env.add name typ env in

    match e with
    | Int       _  -> TInt          | Bool      _  -> TBool
    | Unit         -> TUnit         | Var       n  -> find_typ n
    | Op        op -> find_typ op   | NewRef    e  -> TRef  (te e)
    | Fun       (_, ta, e) -> TFun (ta, te e)
    | Pair      (e1, e2)   -> TPair (te e1, te e2)
    | Sequence  (e1, e2)   -> let _ = te e1 in te e2
    | While     (c, e)     -> let _ = te c and _ = te e in TUnit

    | If (c, et, ef) ->
      if not ((te c) == TBool)
      then  failwith "HADOUKEN"
      else  let tt = te et and tf = te ef in
            if not (tt == tf)
              then failwith "KAMEHAMEHA"
              else tt

    | App (e1, e2) ->
      let tf = te e1 and te = te e2 in
      (match tf with
      | TFun (targ, tret) when targ == te -> tret
      | _ -> failwith "Nooope, Chuck Testa."
      )

    | Let (vname, e1, e2) ->
      let nenv = add_var vname (te e1) in
      type_expression nenv e2

end

(**
    Exercice 2 : inférence des types simples.

    Ci-dessous, une syntaxe quasi-identique à [BaseAST].
    A disparu : l'annotation du paramètre formel d'une fonction par son type.

    Objectif : inférence de types.
*)
module RawAST = struct
  open SimpleTypes

  (** Expressions *)
  type expression =
    | Int    of int    (** Entier [n]    *)
    | Bool   of bool   (** Booléen [b]   *)
    | Unit             (** Unité [()]    *)
    | Var    of string (** Variable  [x] *)
    | App    of expression * expression
                       (** Application [e₁ e₂] *)
    | Fun    of string * expression
                       (** Fonction [fun x -> e] *)
    | Let    of string * expression * expression
                       (** Liaison [let x=e₁ in e₂] *)
    | Op     of string (** Opérateur *)
    | Pair   of expression * expression
                       (** Paire [(e₁, e₂)] *)
    | Newref of expression
                       (** Création d'une référence initialisée [ref e] *)
    | Sequence of expression * expression
                       (** Séquence d'expressions [e₁; e₂] *)
    | If     of expression * expression * expression
                       (** Conditionnelle [if c then e₁ else e₂] *)
    | While  of expression * expression
                       (** Boucle [while c do e done] *)

end

(**
   Moteur d'inférence de types
*)
module BaseTypeReconstruction = struct
  open SimpleTypes
  open RawAST

  module Env = Map.Make(String)
  type type_env = typ Env.t
  exception UnifRec of (type_env * type_env)

  (* Remplace les TVar(s) récursivement dans un type donné *)
  let rec replace_in_type s new_t elmt =
    let ret = replace_in_type s new_t in
    match elmt with
    (* Remplacement *)
    | TVar str when str == s -> new_t
    (* Récursions *)
    | TFun  (t1, t2) -> TFun  (ret t1, ret t2)
    | TPair (t1, t2) -> TPair (ret t1, ret t2)
    | TRef  t        -> TRef  (ret t)
    (* Rien à remplacer... *)
    | _ -> elmt

  and replace_in_env env s new_t = Env.map (replace_in_type s new_t) env

  (* Fonction d'unification *)
  and unif env1 env2 =
    try
      Env.fold (fun key elmt1 env_acc ->
        match Env.find_opt key env_acc with
        (* Ajout d'un type manquant dans env_acc (construit à partir d'env2) *)
        | None -> Env.add key elmt1 env_acc

        (* Confrontation, on vérifie si les types sont les mêmes,
         * si l'un d'eux est TVar s ou s'ils sont conflictuels *)
        | Some elmt2 ->
          let restart_with arg1 arg2 = raise ( UnifRec (arg1, arg2) ) in
          (match elmt1, elmt2 with

          (* Types identiques, aucun changement *)
          | a, b when a == b -> env_acc

          (* L'un d'eux est TVar s, on unifie *)
          | TVar s, t | t, TVar s ->
            restart_with (replace_in_env env1    s  t)
                         (replace_in_env env_acc s  t)

          (* Sinon il y a conflit, donc erreur *)
          | _ -> failwith "Conflicting types"
          )
      ) (* Iter on : *) env1 (* Acc : *) env2
    (* Récursion lors d'une exception de type UnifRec *)
    with UnifRec (nenv1, nenv2) -> unif nenv1 nenv2

  (**
      Objectif : compléter la fonction suivante de typage d'une expression.
      Un appel [type_expression e] doit :
      - renvoyer le type de [e] dans l'environnement [env] si [e] est bien typée
      - déclencher une exception sinon

      Procéder en deux étapes : génération de contraintes sur les types,
      puis résolution par unification.
  *)
  let rec type_expression (env: type_env) (e: expression) : (type_env * typ) =
    (* Funlets *)

    let te = type_expression env
    and find_typ name = Env.find name env
    in

    match e with
    (* Cas triviaux *)
    | Int    _  -> env, TInt        | Bool _ -> env, TBool
    | Unit      -> env, TUnit       | Var  n -> env, find_typ n
    | Op     op -> env, find_typ op
    | Newref e  -> let nenv, t = te e in nenv, TRef(t)

    (* Require unification *)

    (* Special case of unification *)
    | Pair (e1, e2) ->
      let nenv1, t1 = te e1 and nenv2, t2 = te e2 in
      let nenv = unif nenv1 nenv2 in
      (match type_expression nenv e1 , type_expression nenv e2 with

        (* Les types n'ont pas changé, on renvoie après unification *)
      | (ne1, nt1), (ne2, nt2) when (t1 == nt1) && (t2 == nt2) ->
        unif ne1 ne2, TPair(nt1, nt2)

        (* Sinon on recalcule (jusqu'à ce que les types ne changent plus) *)
      | (ne1, nt1), (ne2, nt2) -> type_expression (unif ne1 ne2) e
      )

    | Sequence (e1, e2) ->
      let (env1, _ ) = te e1 and (env2, _) = te e2
      in type_expression (unif env1 env2) e2

    | While (c, e) ->
      let envc , _ = te c
      and enve , _ = te e in
      let nenv = (unif envc enve) in
      (match type_expression nenv c with
      | _, TBool -> nenv, TUnit
      | _ -> failwith "Condition expression is not boolean."
      )

    | If (c, e1, e2) ->
      let envc, _ = te c
      and env1, _ = te e1
      and env2, _ = te e2 in
      let nenv = unif (unif env1 env2) envc in
      (match type_expression nenv c , type_expression nenv e1
                                    , type_expression nenv e2 with
      | (_, TBool) , (_, t1) , (_, t2) when t1 == t2 -> nenv, t1
      | _ ->
        failwith "Condition is not a boolean or incompatible branche types."
      )

    | Let (name, e_bind, e) ->
      let enve, te_bind = te e_bind in
      let nenv = Env.add name te_bind enve in
      type_expression nenv e

    | App (e1, e2) ->
      let env1, _ = te e1
      and env2, _ = te e2 in
      let nenv    = unif env1 env2 in
      (match type_expression nenv e1 , type_expression nenv e2 with
      | (_, TFun(targ, tret)) , (_, t2) when targ == t2 -> nenv, tret
      | _ -> failwith "Bad application"
      )

    | Fun (n, e) ->
      (match te e with
      | nenv, t when t == (Env.find n nenv) -> nenv, t
      | _ -> failwith "ok"
      )

end

(** Bonus : version polymorphe *)


(**
   Exercice 3 : sous-typage.

   On ajoute un type optionnel [T?] désignant des valeurs de type [T]
   éventuellement non définies (contrairement au type [T] lui-même pour
   lequel la valeur est à coup sûr définie.

   On a donc la relation de sous-typage [T <: T?], de laquelle on déduit
   une relation plus générale avec les règles habituelles.
*)
module OptionTypes = struct

  (** Les types simples + un type optionnel *)
  type typ =
    | TVar of string      (** Variables de type ['a] *)
    | TInt                (** Entiers [int]          *)
    | TBool               (** Booléens [bool]        *)
    | TUnit               (** Unité [unit]           *)
    | TFun  of typ * typ  (** Fonctions [T₁ ⟶ T₂]  *)
    | TPair of typ * typ  (** Paires [T₁ * T₂]       *)
    | TRef  of typ        (** Références [ref T]     *)

    | TMaybe of typ       (** Type option [T?]       *)

end

(**
   Parallèlement à l'introduction du type optionnel, on modifie l'opérateur
   de création de référence, qui crée une référence non initialisée sur un
   type [T] donné en paramètre.
   L'expression [newref T] aura donc le type [ref T?].

   On crée également un opérateur ["isNull"] testant si une valeur donnée
   est indéfinie.
*)
module SubAST = struct

  type expression =
    | Int    of int    (** Entier [n]    *)
    | Bool   of bool   (** Booléen [b]   *)
    | Unit             (** Unité [()]    *)
    | Var    of string (** Variable  [x] *)
    | App    of expression * expression
                       (** Application [e₁ e₂] *)
    | Fun    of string * OptionTypes.typ * expression
                       (** Fonction [fun x:T -> e] *)
    | Let    of string * expression * expression
                       (** Liaison [let x=e₁ in e₂] *)
    | Op     of string (** Opérateur *)
    | Pair   of expression * expression
                       (** Paire [(e₁, e₂)] *)
    | NewRef of OptionTypes.typ
                       (** Création d'une référence non initialisée [newref T] *)
    | Sequence of expression * expression
                       (** Séquence d'expressions [e₁; e₂] *)
    | If     of expression * expression * expression
                       (** Conditionnelle [if c then e₁ else e₂] *)
    | While  of expression * expression
                       (** Boucle [while c do e done] *)

end

(**
   Vérification de types avec sous-typage.

   Ajouter du sous-typage au vérificateur de types simples, avec la règle
   algorithmique standard : le paramètre effectif d'un appel de fonction peut
   être un sous-type du type du paramètre formel.

   On ajoutera les particularités suivantes :
   - Tout opérateur travaillant sur des valeurs concrètes nécessitera des
     opérandes dont le type *n'est pas* un type optionnel.
   - Dans une expression de la forme [if isNull a then e₁ else e₂] avec [a] de
     type [T?], on pourra donner à [a] le type [T] dans la branche [e₂].
*)
module SubTypeChecker = struct
  open OptionTypes
  open SubAST

  module Env = Map.Make(String)
  type type_env = typ Env.t
  exception UnifRec of (type_env * type_env)

  (* Remplace les TVar(s) récursivement dans un type donné *)
  let rec replace_in_type s new_t elmt =
    let ret = replace_in_type s new_t in
    match elmt with
    (* Remplacement *)
    | TVar str when str == s -> new_t

    (* Récursions *)
    | TFun   (t1, t2) -> TFun   (ret t1, ret t2)
    | TPair  (t1, t2) -> TPair  (ret t1, ret t2)
    | TRef   t -> TRef   (ret t)
    | TMaybe t -> TMaybe (ret t)

    (* Rien à remplacer... *)
    | _ -> elmt

  and replace_in_env env s new_t = Env.map (replace_in_type s new_t) env

  (* Fonction d'unification *)
  and unif env1 env2 =
    try
      Env.fold (fun key elmt1 env_acc ->
        match Env.find_opt key env_acc with
        (* Ajout d'un type manquant dans env_acc (construit à partir d'env2) *)
        | None -> Env.add key elmt1 env_acc

        (* Confrontation, on vérifie si les types sont les mêmes,
         * si l'un d'eux est TVar s ou s'ils sont conflictuels *)
        | Some elmt2 ->
          let restart_with arg1 arg2 = raise ( UnifRec (arg1, arg2) ) in
          (match elmt1, elmt2 with

          (* Types identiques, aucun changement *)
          | a, b when a == b -> env_acc

          (* L'un d'eux est TVar s, on unifie *)
          | TVar s, t | t, TVar s ->
            restart_with (replace_in_env env1    s  t)
                         (replace_in_env env_acc s  t)

          (* Sinon il y a conflit, donc erreur *)
          | _ -> failwith "Conflicting types"
          )
      ) (* Iter on : *) env1 (* Acc : *) env2
    (* Récursion lors d'une exception de type UnifRec *)
    with UnifRec (nenv1, nenv2) -> unif nenv1 nenv2

  (**
      Objectif : compléter la fonction suivante de typage d'une expression.
      Un appel [type_expression e] doit :
      - renvoyer le type de [e] dans l'environnement [env] si [e] est bien typée
      - déclencher une exception sinon

      Procéder en deux étapes : génération de contraintes sur les types,
      puis résolution par unification.
  *)
  let rec type_expression (env: type_env) (e: expression) : (type_env * typ) =
    (* Funlets *)

    let te = type_expression env
    and find_typ name = Env.find name env
    in

    match e with
    (* Cas triviaux *)
    | Int    _  -> env, TInt        | Bool _ -> env, TBool
    | Unit      -> env, TUnit       | Var  n -> env, find_typ n
    | Op     op -> env, find_typ op

    | NewRef t  -> failwith "Not implemented"

    (* Require unification *)

    (* Special case of unification *)
    | Pair (e1, e2) ->
      let nenv1, t1 = te e1 and nenv2, t2 = te e2 in
      let nenv = unif nenv1 nenv2 in
      (match type_expression nenv e1 , type_expression nenv e2 with

        (* Les types n'ont pas changé, on renvoie après unification *)
      | (ne1, nt1), (ne2, nt2) when (t1 == nt1) && (t2 == nt2) ->
        unif ne1 ne2, TPair(nt1, nt2)

        (* Sinon on recalcule (jusqu'à ce que les types ne changent plus) *)
      | (ne1, nt1), (ne2, nt2) -> type_expression (unif ne1 ne2) e
      )

    | Sequence (e1, e2) ->
      let (env1, _ ) = te e1 and (env2, _) = te e2
      in type_expression (unif env1 env2) e2

    | While (c, e) ->
      let envc , _ = te c
      and enve , _ = te e in
      let nenv = (unif envc enve) in
      (match type_expression nenv c with
      | _, TBool -> nenv, TUnit
      | _ -> failwith "Condition expression is not boolean."
      )

    | If (c, e1, e2) ->
      let envc, _ = te c
      and env1, _ = te e1
      and env2, _ = te e2 in
      let nenv = unif (unif env1 env2) envc in
      (match type_expression nenv c , type_expression nenv e1
                                    , type_expression nenv e2 with
      | (_, TBool) , (_, t1) , (_, t2) when t1 == t2 -> nenv, t1
      | _ ->
        failwith "Condition is not a boolean or incompatible branche types."
      )

    | Let (name, e_bind, e) ->
      let enve, te_bind = te e_bind in
      let nenv = Env.add name te_bind enve in
      type_expression nenv e

    | App (e1, e2) ->
      let env1, _ = te e1
      and env2, _ = te e2 in
      let nenv    = unif env1 env2 in
      (match type_expression nenv e1 , type_expression nenv e2 with
      | (_, TFun(targ, tret)) , (_, t2) when targ == t2 -> nenv, tret
      | _ -> failwith "Bad application"
      )

    | Fun (n, t, e) -> failwith "Not implemented"

end
