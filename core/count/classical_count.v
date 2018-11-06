From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import classical_cont count.
Require Import ClassicalChoice.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma exists_minsec Q (cnt: nat -> Q):
	cnt \is_surjective_function -> exists sec, minimal_section cnt sec.
Proof.
move => sur.
set R := make_mf (fun s n => cnt n = s /\ (forall m, cnt m = s -> n <= m)).
have Rtot: R \is_total by move => s; have [n]:= well_order_nat (sur s); exists n.
by have [sec]:= (choice _ Rtot); exists sec; split => s; have []:= p s.
Qed.

Lemma count_countMixin Q : Q \is_countable ->
  exists P : Countable.mixin_of Q, True.
Proof.
move => [cnt sur]; have [sec [issec min]] := exists_minsec sur.
unshelve eexists (@Countable.Mixin _ (sec \o some) cnt _) => //.
by move=> x /=; rewrite issec.
Qed.

Lemma classic_eqClass Q : exists P : Equality.class_of Q, True.
Proof.
have /choice[eq eqP]: forall q, exists b, (q.1 = q.2 :> Q) <-> (b = true).
  by move=> q; case: (classic (q.1 = q.2)) => ass; [exists true|exists false].
unshelve eexists (@Equality.Mixin _ (fun x y => eq (x, y)) _) => //.
by move=> x y; apply: (iffP idP) => [/eqP//|->]; apply/eqP.
Qed.

Lemma count_countClass Q  : Q \is_countable ->
  exists P : Countable.class_of Q, True.
Proof.
move=> /count_countMixin[cmQ _]; have [eqQ _] := classic_eqClass Q.
set QeqType := EqType Q eqQ.
set QchoiceType := ChoiceType QeqType (CountChoiceMixin cmQ).
by exists (Countable.class (CountType QchoiceType cmQ)).
Qed.

Lemma option_count T : T \is_countable -> (option T) \is_countable.
Proof.
move=> /count_countClass [cT _]; set T' : Type := Countable.Pack cT T.
by rewrite -[T]/T'; apply: countType_count.
Qed.

Lemma sum_count Q Q': Q \is_countable -> Q' \is_countable ->
  (Q + Q') \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
move=> /count_countClass [cQ' _]; set Q'C : Type := Countable.Pack cQ' Q'.
by rewrite -[Q]/QC -[Q']/Q'C; apply: countType_count.
Qed.

Lemma prod_count Q Q':
  Q \is_countable -> Q' \is_countable -> (Q * Q') \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
move=> /count_countClass [cQ' _]; set Q'C : Type := Countable.Pack cQ' Q'.
by rewrite -[Q]/QC -[Q']/Q'C; apply: countType_count.
Qed.

Lemma list_count Q: Q \is_countable -> (list Q) \is_countable.
Proof.
move=> /count_countClass [cQ _]; set QC : Type := Countable.Pack cQ Q.
by rewrite -[Q]/QC; apply: countType_count.
Qed.
