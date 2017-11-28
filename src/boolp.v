(* -------------------------------------------------------------------- *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype choice.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Record mextentionality := {
  _ : forall (P : Prop), P = True \/ P = False;
  _ : forall {T U : Type} (f g : T -> U),
        (forall x, f x = g x) -> f = g;
}.
Record mclassic := {
  _ : forall (P : Prop), {P} + {~P};
}.

Axiom classic : mclassic.
Axiom extentionality : mextentionality.

(* -------------------------------------------------------------------- *)
Lemma pselect (P : Prop): {P}+{~P}.
Proof. by case: classic. Qed.

Lemma pdegen (P : Prop): P = True \/ P = False.
Proof. by case: extentionality. Qed.

Lemma propeqE (P Q : Prop) : (P = Q) = (P <-> Q).
Proof.
gen have wpropext: P Q / (P <-> Q) -> (P = Q); last first.
  by apply: (wpropext); split=> [->|/wpropext].
by have [[]-> []->] // := (pdegen P, pdegen Q); tauto.
Qed.

Lemma lem (P : Prop): P \/ ~P.
Proof. by case: (pselect P); tauto. Qed.

Lemma funext {T U : Type} (f g : T -> U) : (f =1 g) -> f = g.
Proof. by case: extentionality=> _; apply. Qed.

Lemma funeqE {T U : Type} (f g : T -> U) : (f = g) = (f =1 g).
Proof. by rewrite propeqE; split=> [->//|/funext]. Qed.

Lemma funeq2E {T U V : Type} (f g : T -> U -> V) : (f = g) = (f =2 g).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite funeqE.
Qed.

Lemma funeq3E {T U V W : Type} (f g : T -> U -> V -> W) :
  (f = g) = (forall x y z, f x y z = g x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> x y; rewrite funeqE.
Qed.

Lemma predeqE {T} (P Q : T -> Prop) : (P = Q) = (forall x, P x <-> Q x).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeqE=> x; rewrite propeqE.
Qed.

Lemma predeq2E {T U} (P Q : T -> U -> Prop) :
   (P = Q) = (forall x y, P x y <-> Q x y).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq2E=> ??; rewrite propeqE.
Qed.

Lemma predeq3E {T U V} (P Q : T -> U -> V -> Prop) :
   (P = Q) = (forall x y z, P x y z <-> Q x y z).
Proof.
by rewrite propeqE; split=> [->//|?]; rewrite funeq3E=> ???; rewrite propeqE.
Qed.

(* -------------------------------------------------------------------- *)
Lemma trueE : true = True :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma falseE : false = False :> Prop.
Proof. by rewrite propeqE; split. Qed.

Lemma propT (P : Prop) : P -> P = True.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma propF (P : Prop) : ~ P -> P = False.
Proof. by move=> p; rewrite propeqE; tauto. Qed.

Lemma eq_forall T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (forall x, U x) = (forall x, V x).
Proof. by move=> e; rewrite propeqE; split=> ??; rewrite (e,=^~e). Qed.

Lemma eq_exists T (U V : T -> Prop) :
  (forall x : T, U x = V x) -> (exists x, U x) = (exists x, V x).
Proof.
by move=> e; rewrite propeqE; split=> - [] x ?; exists x; rewrite (e,=^~e).
Qed.

Lemma reflect_eq (P : Prop) (b : bool) : reflect P b -> P = b.
Proof. by rewrite propeqE; exact: rwP. Qed.

Definition asbool (P : Prop) :=
  if pselect P then true else false.

Notation "`[< P >]" := (asbool P) : bool_scope.

Lemma asboolE (P : Prop) : `[<P>] = P :> Prop.
Proof. by rewrite propeqE /asbool; case: pselect; split. Qed.

Lemma asboolP (P : Prop) : reflect P `[<P>].
Proof. by apply: (equivP idP); rewrite asboolE. Qed.

Lemma asboolPn (P : Prop) : reflect (~ P) (~~ `[<P>]).
Proof. by rewrite /asbool; case: pselect=> h; constructor. Qed.

Lemma asboolW (P : Prop) : `[<P>] -> P.
Proof. by case: asboolP. Qed.

(* Shall this be a coercion ?*)
Lemma asboolT (P : Prop) : P -> `[<P>].
Proof. by case: asboolP. Qed.

Lemma asboolF (P : Prop) : ~ P -> `[<P>] = false.
Proof. by apply/introF/asboolP. Qed.

Lemma is_true_inj : injective is_true.
Proof. by move=> [] []; rewrite ?(trueE, falseE) ?propeqE; tauto. Qed.


(* -------------------------------------------------------------------- *)
Lemma asbool_equiv_eq {P Q : Prop} : (P <-> Q) -> `[<P>] = `[<Q>].
Proof. by rewrite -propeqE => ->. Qed.

Lemma asbool_equiv_eqP {P Q : Prop} QQ : reflect Q QQ -> (P <-> Q) -> `[<P>] = QQ.
Proof.
move=> Q_QQ [hPQ hQP]; apply/idP/Q_QQ=> [/asboolP//|].
by move=> hQ; apply/asboolP/hQP.
Qed.

Lemma asbool_equiv {P Q : Prop} : (P <-> Q) -> (`[<P>] <-> `[<Q>]).
Proof. by move/asbool_equiv_eq->. Qed.

Lemma asbool_eq_equiv {P Q : Prop} : `[<P>] = `[<Q>] -> (P <-> Q).
Proof.
by move=> eq; split=> /asboolP; rewrite (eq, =^~ eq) => /asboolP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma and_asboolP (P Q : Prop) : reflect (P /\ Q) (`[<P>] && `[<Q>]).
Proof.
apply: (iffP idP); first by case/andP=> /asboolP hP /asboolP hQ.
by case=> /asboolP-> /asboolP->.
Qed.

Lemma or_asboolP (P Q : Prop) : reflect (P \/ Q) (`[<P>] || `[<Q>]).
Proof.
apply: (iffP idP); first by case/orP=> /asboolP; [left | right].
by case=> /asboolP-> //=; rewrite orbT.
Qed.

Lemma asbool_neg {P : Prop} : `[<~ P>] = ~~ `[<P>].
Proof. by apply/idP/asboolPn=> [/asboolP|/asboolT]. Qed.

Lemma asbool_or {P Q : Prop} : `[<P \/ Q>] = `[<P>] || `[<Q>].
Proof. exact: (asbool_equiv_eqP (or_asboolP _ _)). Qed.

Lemma asbool_and {P Q : Prop} : `[<P /\ Q>] = `[<P>] && `[<Q>].
Proof. exact: (asbool_equiv_eqP (and_asboolP _ _)). Qed.

(* -------------------------------------------------------------------- *)
Lemma imply_asboolP {P Q : Prop} : reflect (P -> Q) (`[<P>] ==> `[<Q>]).
Proof.
apply: (iffP implyP)=> [PQb /asboolP/PQb/asboolW //|].
by move=> PQ /asboolP/PQ/asboolT.
Qed.

Lemma asbool_imply {P Q : Prop} : `[<P -> Q>] = `[<P>] ==> `[<Q>].
Proof. exact: (asbool_equiv_eqP imply_asboolP). Qed.

Lemma imply_asboolPn (P Q : Prop) : reflect (P /\ ~ Q) (~~ `[<P -> Q>]).
Proof.
apply: (iffP idP).
by rewrite asbool_imply negb_imply -asbool_neg => /and_asboolP.
by move/and_asboolP; rewrite asbool_neg -negb_imply asbool_imply.
Qed.

(* -------------------------------------------------------------------- *)
Lemma forall_asboolP {T : Type} (P : T -> Prop) :
  reflect (forall x, `[<P x>]) (`[<forall x, P x>]).
Proof.
apply: (iffP idP); first by move/asboolP=> Px x; apply/asboolP.
by move=> Px; apply/asboolP=> x; apply/asboolP.
Qed.

Lemma exists_asboolP {T : Type} (P : T -> Prop) :
  reflect (exists x, `[<P x>]) (`[<exists x, P x>]).
Proof.
apply: (iffP idP); first by case/asboolP=> x Px; exists x; apply/asboolP.
by case=> x bPx; apply/asboolP; exists x; apply/asboolP.
Qed.

(* -------------------------------------------------------------------- *)
Lemma contrap (Q P : Prop) : (Q -> P) -> ~ P -> ~ Q.
Proof.
move=> cb /asboolPn nb; apply/asboolPn.
by apply: contra nb => /asboolP /cb /asboolP.
Qed.

Definition contrapNN := contra.

Lemma contrapL (Q P : Prop) : (Q -> ~ P) -> P -> ~ Q.
Proof.
move=> cb /asboolP hb; apply/asboolPn.
by apply: contraL hb => /asboolP /cb /asboolPn.
Qed.

Definition contrapTN := contrapL.

Lemma contrapR (Q P : Prop) : (~ Q -> P) -> ~ P -> Q.
Proof.
move=> cb /asboolPn nb; apply/asboolP.
by apply: contraR nb => /asboolP /cb /asboolP.
Qed.

Definition contrapNT := contrapR.

Lemma contrapLR (Q P : Prop) : (~ Q -> ~ P) -> P -> Q.
Proof.
move=> cb /asboolP hb; apply/asboolP.
by apply: contraLR hb => /asboolP /cb /asboolPn.
Qed.

Definition contrapTT := contrapLR.

Lemma contrapT P : ~ ~ P -> P.
Proof.
by move/asboolPn=> nnb; apply/asboolP; apply: contraR nnb => /asboolPn /asboolP.
Qed.

Lemma wlog_neg P : (~ P -> P) -> P.
Proof. by move=> ?; case: (pselect P). Qed.

Lemma notT (P : Prop) : P = False -> ~ P. Proof. by move->. Qed.

Lemma notTE (P : Prop) : (~ P) -> P = False. Proof. by case: (pdegen P)=> ->. Qed.
Lemma notFE (P : Prop) : (~ P) = False -> P.
Proof. move/notT; exact: contrapT. Qed.

Lemma notK : involutive not.
Proof.
move=> P; case: (pdegen P)=> ->; last by apply: notTE; intuition.
by rewrite [~ True]notTE //; case: (pdegen (~ False)) => // /notFE.
Qed.

Lemma not_inj : injective not. Proof. exact: can_inj notK. Qed.
Lemma notLR P Q : (P = ~ Q) -> (~ P) = Q. Proof. exact: canLR notK. Qed.

Lemma notRL P Q : (~ P) = Q -> P = ~ Q. Proof. exact: canRL notK. Qed.

(****** to reorganize ********)

Definition dep_arrow_eq (T : eqType) (T' : T -> eqType)
   (f g : forall x : T, T' x) := `[<f = g>].
Lemma dep_arrow_eqP (T : eqType) (T' : T -> eqType) : Equality.axiom (@dep_arrow_eq T T').
Proof.
by move=> f g; apply: (iffP idP) => [/asboolP|->]; last by apply/asboolP.
Qed.

Definition dep_arrow_eqMixin (T : eqType) (T' : T -> eqType) := EqMixin (@dep_arrow_eqP T T').
Definition dep_arrow_eqType  (T : eqType) (T' : T -> eqType) :=
  EqType (forall x : T, T' x) (@dep_arrow_eqMixin T T').
Canonical arrow_eqType (T : eqType) (T' : eqType) :=
  EqType (T -> T') (@dep_arrow_eqMixin T _).

Axiom arrow_choiceMixin : forall T T' : Type, Choice.mixin_of (T -> T').
Canonical arrow_choiceType (T : choiceType) (T' : choiceType) :=
  ChoiceType (T -> T') (@arrow_choiceMixin T T').

Reserved Notation "A `&` B"  (at level 48, left associativity).
Reserved Notation "A `*` B"  (at level 46, left associativity).
Reserved Notation "A `+` B"  (at level 54, left associativity).
Reserved Notation "A +` B"  (at level 54, left associativity).
Reserved Notation "A `|` B" (at level 52, left associativity).
Reserved Notation "a |` A" (at level 52, left associativity).
Reserved Notation "A `\` B" (at level 50, left associativity).
Reserved Notation "A `\ b" (at level 50, left associativity).

Definition set A := A -> Prop.
Definition in_set T (P : set T) : pred T := [pred x | `[<P x>]].
Canonical set_predType T := @mkPredType T (set T) (@in_set T).

Lemma in_setE T (P : set T) x : x \in P = P x :> Prop.
Proof. by rewrite propeqE; split => [] /asboolP. Qed.

Bind Scope classical_set_scope with set.
Local Open Scope classical_set_scope.

Notation "[ 'set' x : T | P ]" := ((fun x => P) : set T)
  (at level 0, x at level 99, only parsing) : classical_set_scope.
Notation "[ 'set' x | P ]" := [set x : _ | P]
  (at level 0, x, P at level 99, format "[ 'set'  x  |  P ]") : classical_set_scope.

Notation "[ 'set' E | x 'in' A ]" := [set y | exists2 x, A x & E = y]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A ] ']'") : classical_set_scope.
Notation "[ 'set' E | x 'in' A & y 'in' B ]" := [set z | exists2 x, A x & exists2 y, B y & E = z]
  (at level 0, E, x at level 99,
   format "[ '[hv' 'set'  E '/ '  |  x  'in'  A  &  y  'in'  B ] ']'") : classical_set_scope.

Definition image {A B} (f : A -> B) (X : set A) : set B :=
  [set f a | a in X].

Definition preimage {A B} (f : A -> B) (X : set B) : set A := [set a | X (f a)].
Arguments preimage A B f X / a.

Definition setT {A} := [set _ : A | True].
Definition set0 {A} := [set _ : A | False].
Definition set1 {A} (x : A) := [set a : A | a = x].
Definition setI {A} (X Y : set A) := [set a | X a /\ Y a].
Definition setU {A} (X Y : set A) := [set a | X a \/ Y a].
Definition nonempty {A} (X : set A) := exists x, X x.
Definition setC {A} (X : set A) := [set a | ~ X a].
Definition setD {A} (X Y : set A) := [set a | X a /\ ~ Y a].
Definition setM {A B} (X : set A) (Y : set B) := [set x | X x.1 /\ Y x.2].
Definition fst_set {A B} (X : set (A * B)) := [set x | exists y, X (x, y)].
Definition snd_set {A B} (X : set (A * B)) := [set y | exists x, X (x, y)].

Notation "[ 'set' 'of' F ]" := [set F i | i in setT]
  (at level 0,
   format "[ 'set'  'of'  F ]") : classical_set_scope.

Notation "[ 'set' a ]" := (set1 a)
  (at level 0, a at level 99, format "[ 'set'  a ]") : classical_set_scope.
Notation "[ 'set' a : T ]" := [set (a : T)]
  (at level 0, a at level 99, format "[ 'set'  a   :  T ]") : classical_set_scope.
Notation "A `|` B" := (setU A B) : classical_set_scope.
Notation "a |` A" := ([set a] `|` A) : classical_set_scope.
Notation "[ 'set' a1 ; a2 ; .. ; an ]" := (setU .. (a1 |` [set a2]) .. [set an])
  (at level 0, a1 at level 99,
   format "[ 'set'  a1 ;  a2 ;  .. ;  an ]") : classical_set_scope.
Notation "A `&` B" := (setI A B) : classical_set_scope.
Notation "A `*` B" := (setM A B) : classical_set_scope.
Notation "A .`1" := (fst_set A)
  (at level 2, left associativity, format "A .`1") : classical_set_scope.
Notation "A .`2" := (snd_set A)
  (at level 2, left associativity, format "A .`2") : classical_set_scope.
Notation "~` A" := (setC A) (at level 35, right associativity) : classical_set_scope.
Notation "[ 'set' ~ a ]" := (~` [set a])
  (at level 0, format "[ 'set' ~  a ]") : classical_set_scope.
Notation "A `\` B" := (setD A B) : classical_set_scope.
Notation "A `\ a" := (A `\` [set a]) : classical_set_scope.

Definition bigsetI A I (P : set I) (X : I -> set A) :=
  [set a | forall i, P i -> X i a].
Definition bigsetU A I (P : set I) (X : I -> set A) :=
  [set a | exists2 i, P i & X i a].

Notation "\bigcup_ ( i 'in' P ) F" :=
  (bigsetU P (fun i => F))
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcup_ ( i  'in'  P ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcup_ ( i : T ) F" :=
  (\bigcup_(i in @setT T) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcup_ ( i  :  T ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcup_ i F" :=
  (\bigcup_(i : _) F)
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcup_ i '/  '  F ']'")
 : classical_set_scope.

Notation "\bigcap_ ( i 'in' P ) F" :=
  (bigsetI P (fun i => F))
  (at level 41, F at level 41, i, P at level 50,
           format "'[' \bigcap_ ( i  'in'  P ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcap_ ( i : T ) F" :=
  (\bigcap_(i in @setT T) F)
  (at level 41, F at level 41, i at level 50,
           format "'[' \bigcap_ ( i  :  T ) '/  '  F ']'")
 : classical_set_scope.
Notation "\bigcap_ i F" :=
  (\bigcap_(i : _) F)
  (at level 41, F at level 41, i at level 0,
           format "'[' \bigcap_ i '/  '  F ']'")
 : classical_set_scope.

Definition subset {A} (X Y : set A) := forall a, X a -> Y a.

Notation "A `<=` B" := (subset A B) (at level 70, no associativity)
 : classical_set_scope.
Notation "A `<=>` B" := ((A `<=` B) /\ (B `<=` A)) (at level 70, no associativity)
 : classical_set_scope.
Notation "f @^-1` A" := (preimage f A) (at level 24) : classical_set_scope.
Notation "f @` A" := (image f A) (at level 24) : classical_set_scope.
Notation "A !=set0" := (nonempty A) (at level 80) : classical_set_scope.

Lemma imageP {A B} (f : A -> B) (X : set A) a : X a -> (f @` X) (f a).
Proof. by exists a. Qed.

Lemma sub_image_setI {A B} (f : A -> B) (X Y : set A) :
  f @` (X `&` Y) `<=` f @` X `&` f @` Y.
Proof. by move=> b [x [Xa Ya <-]]; split; apply: imageP. Qed.
Arguments sub_image_setI {A B f X Y} a _.

Lemma nonempty_image {A B} (f : A -> B) (X : set A) :
  f @` X !=set0 -> X !=set0.
Proof. by case=> b [a]; exists a. Qed.

Lemma nonempty_preimage {A B} (f : A -> B) (X : set B) :
  f @^-1` X !=set0 -> X !=set0.
Proof. by case=> [a ?]; exists (f a). Qed.

Lemma subset_empty {A} (X Y : set A) : X `<=` Y -> X !=set0 -> Y !=set0.
Proof. by move=> sXY [x Xx]; exists x; apply: sXY. Qed.

Lemma subset_trans {A} (Y X Z : set A) : X `<=` Y -> Y `<=` Z -> X `<=` Z.
Proof. by move=> sXY sYZ ? ?; apply/sYZ/sXY. Qed.

Lemma nonempty_preimage_setI {A B} (f : A -> B) (X Y : set B) :
  (f @^-1` (X `&` Y)) !=set0 <-> (f @^-1` X `&` f @^-1` Y) !=set0.
Proof. by split; case=> x ?; exists x. Qed.

Lemma subsetC {A} (X Y : set A) : X `<=` Y -> ~` Y `<=` ~` X.
Proof. by move=> sXY ? nYa ?; apply/nYa/sXY. Qed.

Lemma subsetU {A} (X Y Z : set A) : X `<=` Z -> Y `<=` Z -> X `|` Y `<=` Z.
Proof. by move=> sXZ sYZ a; apply: or_ind; [apply: sXZ|apply: sYZ]. Qed.

Lemma setDE {A} (X Y : set A) : X `\` Y = X `&` ~` Y.
Proof. by []. Qed.

Definition is_prop {A} (X : set A) := forall x y, X x -> X y -> x = y.
Definition is_fun {A B} (f : A -> B -> Prop) := all (is_prop \o f).
Definition is_total {A B} (f : A -> B -> Prop) := all (nonempty \o f).
Definition is_totalfun {A B} (f : A -> B -> Prop) :=
  forall x, nonempty (f x) /\ is_prop (f x).

Definition xget {T : choiceType} x0 (P : set T) : T :=
  if pselect (exists x : T, `[<P x>]) isn't left exP then x0
  else projT1 (sigW exP).

Lemma xgetPex {T : choiceType} x0 (P : set T) : (exists x, P x) -> P (xget x0 P).
Proof.
rewrite /xget; case: pselect => [|nexP [x Px]]; last first.
  by exfalso; apply: nexP; exists x; apply/asboolP.
by move=> p; case: sigW=> {p} /= x /asboolP.
Qed.

Lemma xgetP {T : choiceType} x0 (P : set T) (x : T): P x -> P (xget x0 P).
Proof. by move=> Px; apply: xgetPex; exists x. Qed.

Lemma xget_prop {T : choiceType} x0 (P : set T) (x : T) :
  P x -> is_prop P -> xget x0 P = x.
Proof. by move=> Px /(_ _ _ (xgetP x0 Px) Px). Qed.

Lemma xget_unique  {T : choiceType} x0 (P : set T) (x : T) :
  P x -> (forall y, P y -> y = x) -> xget x0 P = x.
Proof. by move=> /xget_prop gPx eqx; apply: gPx=> y z /eqx-> /eqx. Qed.

Lemma xgetPN {T : choiceType} x0 (P : set T) : (forall x, ~ P x) -> xget x0 P = x0.
Proof.
rewrite /xget; case: pselect => //= - [x p /(_ x)].
by have /asboolP q := p => /(_ q).
Qed.

Definition fun_of_rel {A} {B : choiceType} (f0 : A -> B) (f : A -> B -> Prop) :=
  fun x => xget (f0 x) (f x).

Lemma fun_of_relP {A} {B : choiceType} (f : A -> B -> Prop) (f0 : A -> B) a :
  nonempty (f a) ->  f a (fun_of_rel f0 f a).
Proof. by move=> [b fab]; rewrite /fun_of_rel; apply: xgetP fab. Qed.

Lemma fun_of_rel_uniq {A} {B : choiceType} (f : A -> B -> Prop) (f0 : A -> B) a :
  is_prop (f a) -> forall b, f a b ->  fun_of_rel f0 f a = b.
Proof. by move=> fa_prop b /xget_prop xgeteq; rewrite /fun_of_rel xgeteq. Qed.
