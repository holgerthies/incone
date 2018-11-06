From mathcomp Require Import all_ssreflect.
Require Import all_core classical_mach all_cs_base cs_one.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section OPTIONSPACES.
Definition rep_opt (X: cs) :=
make_mf (fun phi (x: option X) => match x with
	| some x => (phi (inl star)).1 = some star
		/\
		 delta (fun q => (phi (inr q)).2) x
	| None => (phi (inl star)).1 = None
end).

Lemma rep_opt_sur X:
	(@rep_opt X) \is_cototal.
Proof.
move => [a | ]; last by exists (fun q => (None, somea X)).
have [phi phinx]:= get_description a.
by exists (fun q => (Some star, if q is inr q' then phi q' else somea X)).
Qed.

Definition cs_opt_assembly_mixin (X: cs):
	interview_mixin.type (one + questions X -> option one * answers X) (option X).
Proof. exists (@rep_opt X); exact/rep_opt_sur. Defined.

Lemma rep_opt_sing X:
	(@rep_opt X) \is_singlevalued.
Proof.
move => phi x y phinx phiny.
case: x phinx.
	case: y phiny; last by move => /= Nope a [eq phina]; rewrite eq in Nope.
	move => a/= [eq phina] b [eq' phinb].
	by rewrite (rep_sing (fun q => (phi (inr q)).2) a b).
case: y phiny => //.
move => /= a [eq phina] Nope.
by rewrite eq in Nope.
Qed.

Definition cs_opt_modest_set_mixin (X: cs):
	dictionary_mixin.type (interview.Pack (cs_opt_assembly_mixin X)).
Proof. split; exact/rep_opt_sing. Defined.

Canonical rep_space_opt (X: cs) := @continuity_space.Pack
	(one + questions X)
	(option one * answers X)
	(inl star)
	((None, somea X))
	(sum_count one_count (questions_countable X))
	(prod_count (option_count one_count) (answers_countable X))
	(dictionary.Pack (cs_opt_modest_set_mixin X)).

(*
Lemma Some_rec_fun (X: cs):
	(@Some X) \is_recursive_function.
Proof.
by exists (fun phi q => if q is inr q' then (Some star, phi q') else (Some star, some_answer X)).
Defined.

Lemma Some_rec (X: rep_space):
	(F2MF (@Some X)) \is_recursive.
Proof.
exact/rec_fun_rec/Some_rec_fun.
Defined.

Lemma None_rec_elt (X: rep_space):
	(@None X) \is_recursive_element.
Proof.
by exists (fun _ => (None, some_answer _)).
Defined.

Notation unsm phi:= (fun q => (phi (inr q)).2).

Definition Some_inv (X: rep_space) ox (x: X) := ox = some x.

Definition Some_inv_frlzr (X: rep_space) := fun (phi: names (rep_space_opt X)) (q: questions X) => unsm phi q.

Lemma Some_inv_frlzr_Some_inv (X: rep_space):
	(@Some_inv_frlzr X) \is_rec_realizer_of (@Some_inv X).
Proof.
rewrite rrlzr_rlzr.
move => phi [x [[ox [phinox eq]] _]].
rewrite eq in phinox. move: phinox => [/= stuff name].
split.
	exists x; split; first by exists (unsm phi).
	by move => psi <-; exists x.
move => t [[psi [<- phint]]].
rewrite (rep_sing _ (unsm phi) t x) => //.
split.
	exists ox; split => //; rewrite /rep_opt eq; first done.
move => s a; exists x.
rewrite (rep_sing _ phi s ox) => //.
by rewrite eq.
Qed.

Lemma Some_inv_rec (X: rep_space):
	(@Some_inv X) \is_recursive.
Proof.
exists (@Some_inv_frlzr X).
exact: Some_inv_frlzr_Some_inv.
Defined.

Lemma option_rs_rec_inv (X: rep_space) (Y: rep_space) (f: option X -> Y):
	f \is_recursive_function
	->
	(fun a => f (some a)) \is_recursive_function * (f None) \is_recursive_element.
Proof.
move => [M Mcmpt].
split.
	exists (fun phi => (M (fun q => match q with
		| inl str => (some star, some_answer X)
		| inr q => (some star, phi q)
		end))).
	by move => phi x phinx; apply Mcmpt.
by exists (M (fun _ => (None, some_answer X))); apply Mcmpt.
Defined.

Lemma option_rs_rec_ind (X: rep_space) (Y: rep_space) (f: option X -> Y):
	(fun a => f (some a)) \is_recursive_function -> (f None) \is_recursive_element
	-> f \is_recursive_function.
Proof.
move => [M Mcmpt] [N Ncmpt].
exists (fun phi => match (phi (inl star)).1 with
	| None => N
	| Some str => M (fun q => (phi (inr q)).2)
end).
abstract by move => phi x phinx; case: x phinx => [/=a [eq phina] |/= Nope];
	[rewrite eq; apply Mcmpt | rewrite Nope; apply Ncmpt].
Defined.

Lemma opt_sum (X: rep_space):
	wisomorphic (rep_space_opt X) (rep_space_sum X rep_space_one).
Proof.
exists (F2MF (fun ox => match ox with
	| some x => inl x
	| None => inr star
end)).
exists (F2MF (fun xs => match xs with
	| inl x => Some x
	| inr str => None
end)).
split.
	apply /rec_fun_cmpt /option_rs_rec_ind; first by apply inl_rec_fun.
	by apply rec_fun_rec_elt; [exists (fun _ => star) | apply inr_rec_fun].
split; last by rewrite !F2MF_comp/F2MF/=; split => s t; case: s => //; elim.
apply/rec_fun_cmpt/rec_fun_comp; [ | apply paib_rec_fun | ] => /=.
	apply/ sum_rec_fun; first exact: Some_rec_fun.
	by apply /cnst_rec_fun; first apply None_rec_elt.
by case.
Qed.*)
End OPTIONSPACES.
(*Notation unsm phi:= (fun q => (phi (inr q)).2).*)