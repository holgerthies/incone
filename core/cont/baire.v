From mathcomp Require Import all_ssreflect.
From mpf Require Import all_mpf.
Require Import Morphisms FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "L '\is_sublist_of' K" := (List.incl L K) (at level 2).

Section L2SS.
Context (T: Type).

Lemma subl_refl: Reflexive (@List.incl T).
Proof. by move => L t. Qed.

Lemma subl_trans: Transitive (@List.incl T).
Proof. by move => L K M subl subl' t lstn; apply/subl'/subl. Qed.

Definition L2SS L:= make_subset (fun (t: T) => List.In t L).

Lemma L2SS_subs L K:
	L \is_sublist_of K <-> (L2SS L) \is_subset_of (L2SS K).
Proof. done. Qed.

Lemma L2SS_eq L K:
	(L2SS L) === (L2SS K) <-> L \is_sublist_of K /\ K \is_sublist_of L.
Proof. by rewrite set_eq_subs !L2SS_subs. Qed.
End L2SS.

Section coincide.
Context (Q A : Type).
(* Q is for questions, A is for answers*)
Notation B := (Q -> A).
(* The topology on Baire space is the topology of pointwise convergence the following are
the basic open ets (in the sens that for each finite list L and each element phi of Baire
space the set {psi | coin phi psi L} is a basic open set *)
Fixpoint coincide L (phi psi: B) :=
  match L with
    | nil => True
    | cons s K => (phi s = psi s) /\ (coincide K phi psi)
  end.

Notation "phi '\and' psi '\coincide_on' L" := (coincide L phi psi) (at level 2).

Definition ball phi := make_mf (fun L psi => phi \and psi \coincide_on L). 

Lemma restr_exte S T (f g: S ->> T) P P':
	P \is_subset_of P' -> f|_P' \extends g|_P' -> f|_P \extends g|_P.
Proof. by move => subs eq s t [Ps gst]; split => //; apply eq; split => //; apply/subs. Qed.

Lemma restr_equiv S T (f g: S ->> T) P P':
	P \is_subset_of P' -> f|_P' =~= g|_P' -> f|_P =~= g|_P.
Proof.
by rewrite !exte_equiv => subs [exte1 exte2]; split; apply/restr_exte; try apply/subs.
Qed.

(* coinciding on a finite list is an equivalence relation on the elemets of Baire space. *)
Lemma coin_ref L: Reflexive (coincide L).
Proof. by elim: L. Qed.

Lemma coin_sym L: Symmetric (coincide L).
Proof. by move => phi psi; elim: L => // q L ih [eq coin]; split; [rewrite eq | apply ih]. Qed.

Lemma coin_trans L: Transitive (coincide L).
Proof.
move => phi psi psi'.
by elim: L => // q L ih [] eq1 c1 [] eq2 c2; split; [rewrite eq1 eq2| apply: ih].
Qed.

Global Instance coin_equiv L: Equivalence (coincide L).
Proof. by split; [apply coin_ref | apply coin_sym | apply coin_trans]. Qed.

Lemma coin_lstn (phi psi: B) L:
	phi \and psi \coincide_on L <-> (forall q, List.In q L -> phi q = psi q).
Proof.
elim: L => //; split => [ [ass1 ass2] q' [<- | listin] | ass ] //; first by apply H.1.
by split; last (apply H.2; intros); apply ass; [left | right].
Qed.

Lemma coin_app (phi psi: B) L K:
	phi \and psi \coincide_on (L ++ K) <-> (phi \and psi \coincide_on L /\ phi \and psi \coincide_on K).
Proof.
split; first by elim: L => [| a L ih] //=; case => eq b; have []:= ih b; do 2 try split.
by elim: L => [[_ coin]| a L ih [/=[/=ass1 ass2] ass3]] => //=; split => //; apply ih.
Qed.

Lemma coin_subl phi psi L K:
	L \is_sublist_of K -> phi \and psi \coincide_on K -> phi \and psi \coincide_on L.
Proof. by rewrite !coin_lstn; intros; apply/H0/H. Qed.

Lemma coin_spec L phi psi:
	phi \and psi \coincide_on L <-> (F2MF phi)|_(L2SS L) =~= (F2MF psi)|_(L2SS L).
Proof.
split => [/coin_lstn coin | eq]; last by rewrite coin_lstn => q lstn; apply eq; split.
by split => [[Ls <-] | [Ls <-]]; split => //=; first symmetry; apply/coin.
Qed.
End coincide.
Notation "phi '\and' psi '\coincide_on' L" := (coincide L phi psi) (at level 2).

Lemma coin_funeq (T: eqType) S (L: seq T) (phi psi: T -> S):
	phi \and psi \coincide_on L <-> {in L, phi =1 psi}.
Proof.
rewrite /prop_in1 /in_mem /=; elim: L => // t L /=->.
split => [[eq coin] s /orP [/eqP -> | Ls] | prp]//; first exact/coin.
by split => [ | s Ls]; apply/prp/orP; [left | right].
Qed.

Section closures.
Context (Q A : Type).
Notation B := (Q -> A).

Definition closure (P: mf_subset.type B):=
	make_subset (fun phi => forall L, exists psi, phi \and psi \coincide_on L /\ P psi).

Lemma subs_clos P: P \is_subset_of (closure P).
Proof. by move => phi; exists phi; split => //; apply: coin_ref. Qed.
Arguments subs_clos (P) : clear implicits.

Lemma clos_subs P P': P \is_subset_of P' -> (closure P) \is_subset_of (closure P').
Proof.
move => subs phi cPphi L; have [psi []]:= cPphi L.
by exists psi; split => //; apply subs.
Qed.

Lemma clos_clos P: closure (closure P) === closure P.
Proof.
rewrite set_eq_subs; split; last exact/subs_clos.
move => phi ccPphi L; have [psi [coin cPpsi]] := ccPphi L; have [psi' [coin' Ppsi']] := cPpsi L.
by exists psi'; split => //; apply: coin_trans coin coin'.
Qed.
End closures.

Section sequences.
Context (Q A: Type).
Notation B := (Q -> A).
Notation sequence:= (nat -> B).

Definition image (phin: sequence) := make_subset (fun phi => exists n, phi = phin n).

Lemma img_subs phin P:
	(image phin \is_subset_of P) <-> (forall n, P (phin n)).
Proof. by split => H m; [apply/ H; exists m | move => [n ->]; apply H]. Qed.

(* The convergence relation belonging to the topology is given as follows *)
Definition lim :=
	make_mf (fun phin (psi: B) => forall L, exists n, forall m, n <= m -> psi \and (phin m) \coincide_on L).
Notation "psi '\is_limit_of' phin" := (lim phin psi) (at level 50).

Lemma lim_const phi: lim (fun _ => phi) phi.
Proof. move => L; exists 0 => m _; apply/coin_ref. Qed.

Lemma lim_sing: lim \is_singlevalued.
Proof.
move => phin phi psi lim lim'; apply functional_extensionality => q.
have [n /=prp]:= lim [:: q]; have [m /=prp']:= lim' [:: q].
have [-> _]:= prp (maxn n m) (leq_maxl n m).
by have [-> _]:= prp' (maxn n m) (leq_maxr n m).
Qed.

Lemma conv_cP P phin psi:
	lim phin psi /\ (image phin \is_subset_of P) -> psi \from closure P.
Proof.
rewrite img_subs; case => conv elts L; have [n prop]:= conv L.
by exists (phin n); split => //; apply (prop n).
Qed.
End sequences.
Arguments lim {Q} {A}.