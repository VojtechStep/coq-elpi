(* Binary parametricity translation.

   license: GNU Lesser General Public License Version 2.1 or later
   ------------------------------------------------------------------------- *)
From elpi.apps.derive.elpi Extra Dependency "paramX_lib.elpi" as paramX.
From elpi.apps.derive.elpi Extra Dependency "param2.elpi" as param2.
From elpi.apps.derive.elpi Extra Dependency "derive_hook.elpi" as derive_hook.
From elpi.apps.derive.elpi Extra Dependency "derive_synterp_hook.elpi" as derive_synterp_hook.

From elpi Require Import elpi.
From elpi.apps Require Import derive.

(* To be removed *)
Class param_db {X X1 XR : Type} (x : X) (x : X1) (xR : XR) := store_param {}.
Class param {X : Type} {XR : X -> X -> Type} (x : X) (xR : XR x x) := Param {}.

Register store_param as param2.store_param.

(* Links a term (constant, inductive type, inductive constructor, record type,
   projection) with its parametricity translation *)
Elpi Db derive.param2.db lp:{{
    :index(3)
    % param (t : T) is a function that returns t' and tr such that tr : [| T |] t t'
    func param term -> term, term.

    % param.gref implements param for global references.
    % It is introduced to handle param on universe polymorphic definitions
    func param.gref gref -> gref, gref.

    % a database to store triples t, t', tr, such that tr : [| T |] t t'.
    type paramR term -> term -> term -> prop.
    pred param-done i:gref.
}}.
#[superglobal] Elpi Accumulate derive.param2.db lp:{{

    % TODO: Remove when legacy inductive translation is removed
    % helper to lift undeclared grefs to terms.
    func global-gref gref, gref -> term.
    global-gref (const _) GRR TR :- !,
      coq.env.global GRR TR.
    % GRR is the yet undeclared param translation of _GT.
    global-gref _GT GRR (global GRR) :- !.

    % queries param.gref and lifts answer to terms.
    func dispatch-gref gref -> term,term.
    dispatch-gref GRT U TR :-
      param.gref GRT GRU GRR,
      coq.env.global GRU U,
      global-gref GRT GRR TR.

    :name "param:gref"
    param T U TR :-
      coq.env.global GRT T, !,
      dispatch-gref GRT U TR.

    :name "paramR:gref"
    paramR T U TR :-
      coq.env.global GRT T, !,
      dispatch-gref GRT U TR.

    :name "param:fail"
    param X _ _ :-
      M is "derive.param2: No binary parametricity translation for " ^
              {coq.term->string X},
      stop M.

    :name "paramR:fail"
    paramR T T1 TR :-
      M is "derive.param2: No binary parametricity translation linking " ^
              {coq.term->string T} ^ " and " ^ {coq.term->string T1} ^ " and " ^ {coq.term->string TR},
      stop M.
}}.


Elpi Command derive.param2.
Elpi Accumulate File derive_hook.
Elpi Accumulate File paramX.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate lp:{{
  main [str I] :- !, coq.locate I GR, derive.param2.main GR "" _.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param2 <object name>".
}}.

Inductive nat_R : nat -> nat -> Type :=
| O_R : nat_R O O
| S_R : forall n m, nat_R n m -> nat_R (S n) (S m).

Elpi Query lp:{ (indt N) = {{:gref nat}}, coq.env.indt-decl N I, (indt NR) = {{:gref nat_R}}, coq.env.indt-decl NR IR }. (* !!! *)

Set Universe Polymorphism.
Inductive eqT [A] (x : A) : A -> Type :=
| refl : eqT x.
Check refl.

Inductive eqT_R | (A A' : Type) (A_R : A -> A' -> Type) x x' (x_R : A_R x x') : forall y y' (y_R : A_R y y'), eqT x y -> eqT x' y' -> Type :=
| refl_R : eqT_R A A' A_R x x' x_R x x' x_R (refl x) (refl x').
Check refl_R.

Elpi derive.param2 eqT.
Elpi derive.param2 list.

Elpi Query lp:{ (indt N) = {{:gref eqT}}, coq.env.indt-decl N I , (indt NR) = {{:gref eqT_R}}, coq.env.indt-decl NR IR }. (* !!! *)

(* Elpi derive.param2 nat. *)
Definition fa := 0.
Definition fb := fa.

Inductive Foo | (A : Type) := foo : Foo nat -> Foo A -> Foo A.
Elpi Query lp:{ (indt N) = {{:gref Foo}}, coq.env.indt-decl N Decl_ }.
(* Inductive FooR (A A' : Type) (A_R : A -> A' -> Type) : Foo A -> Foo A' -> Type := *)
(* | foo_R :  *)
Check foo.
Elpi derive.param2 nat.

Elpi derive.param2 Foo.
Print Foo_R.

Set Primitive Projections.
Record Wrap (A : Type) : Type := mkWrap {
    wrap : A
  }.
About Wrap.

Elpi Trace Browser.
Elpi derive.param2 Wrap.
About Wrap_R.

Elpi Command derive.param2.register.
Elpi Accumulate File paramX.
Elpi Accumulate Db Header derive.param2.db.
Elpi Accumulate File param2.
Elpi Accumulate Db derive.param2.db.
Elpi Accumulate lp:{{
  main [str I, str R] :- !, coq.locate I GRI, coq.locate R GRR,
    derive.param2.main_register GRI GRR.
  main _ :- usage.

  usage :- coq.error "Usage: derive.param2.register <name> <name_R>".
}}.


(* hook into derive *)
Elpi Accumulate derive File paramX.
Elpi Accumulate derive Db Header derive.param2.db.
Elpi Accumulate derive File param2.
Elpi Accumulate derive Db derive.param2.db.

#[synterp] Elpi Accumulate derive lp:{{
  derivation _ _ (derive "param2" (cl\ cl = []) true).
}}.

Elpi Accumulate derive lp:{{

derivation T N ff (derive "param2" (derive.param2.main T N) (param-done T)).

}}.
