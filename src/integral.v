(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect all_algebra.
(* ------- *) Require Import reals.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.

Local Open Scope ring_scope.
Local Open Scope real_scope.

(* -------------------------------------------------------------------- *)
Notation "{ 'set' E }" := (pred E) : type_scope.

(* -------------------------------------------------------------------- *)
Parameter R : realType.
Parameter Ω : Type.

(* -------------------------------------------------------------------- *)
Parameter isint : (Ω -> R) -> {set Ω} -> option {ereal R}.

Definition int f E := odflt \-inf (isint f E).

Parameter diff   : (Ω -> R) -> Ω -> Ω -> R.
Parameter isdiff : {set Ω} -> pred (Ω -> R).
Parameter linear : pred (Ω -> R).

Axiom linear_diff : forall f x, linear (diff f x).
