From mathcomp Require Import ssreflect ssrfun seq ssrnat.
Require Import classical_count classical_cont classical_mach classical_func all_cs_base dscrt.
Require Import FunctionalExtensionality ClassicalChoice ChoiceFacts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section USIGPROD.
Definition rep_Iprod (I: Type) (X: cs) := make_mf
(fun phi (xn: I -> X) => forall i, (fun p => (phi (i,p))) \is_description_of (xn i)).

Lemma rep_Iprod_sur I X: (@rep_Iprod I X) \is_cototal.
Proof.
move => xn.
pose R n phi:= phi \is_description_of (xn n).
have [ | phi phiprp]:= choice R; last by exists (fun p => phi p.1 p.2).
by move => n; have [phi phinx]:= (get_description (xn n)); exists phi.
Qed.

Definition cs_Iprod_interview_mixin I X:
	interview_mixin.type (I * (questions X) -> answers X) (I -> X).
Proof. exists (rep_Iprod I X); exact/rep_Iprod_sur. Defined.

Lemma rep_Iprod_sing I X: (@rep_Iprod I X) \is_singlevalued.
Proof.
move => phi xn yn phinxn phinyn.
apply functional_extensionality => n.
by apply/ (rep_sing); [apply phinxn | apply phinyn ].
Qed.

Definition cs_Iprod_dictionary_mixin I X:
  dictionary_mixin.type (interview.Pack (cs_Iprod_interview_mixin I X)).
Proof. split; exact/rep_Iprod_sing. Defined.

Definition cs_Iprod I (somei: I) (Icount: I \is_countable) X:=
  continuity_space.Pack
    (somei, someq X)
    (somea X)
    (prod_count Icount (questions_countable X))
    (answers_countable X)
    (dictionary.Pack (cs_Iprod_dictionary_mixin I X)).
                  
Notation "X '\^w'" :=
  (cs_Iprod 0 nat_count X) (at level 35, format "X '\^w'").

Lemma Iprd_base (X: cs) (an: X\^w) (phi: names (X\^w)):
  phi \is_description_of an <-> forall n, (fun q => phi (n,q)) \is_description_of (an n).
Proof. done. Qed.

End USIGPROD.
Notation "X '\^w'" :=
  (cs_Iprod 0 nat_count X) (at level 35, format "X '\^w'").

Definition lim X: X\^w ->> X:= make_mf (fun xn x =>
  exists phin phi, phin \is_description_of xn
                   /\
                   phi \is_description_of x
                   /\
                   baire_limit (uncurry phin) phi).

Section pointwise_operations.
  Context I (somei: I) (I_count: I \is_countable).    
    
  Notation "X '\^' I" := (cs_Iprod somei I_count X) (at level 2, format "X '\^' I").

  Definition ptw R S T (op: R -> S -> T) (rs: I -> R) (ss: I -> S) i:=
    op (rs i) (ss i).

  Lemma ptwA R (op: R -> R -> R): associative op -> associative (ptw op).
  Proof.
    by move => ass x y z; apply/functional_extensionality => n; apply/ass.
  Qed.

  Lemma ptwC R (op: R -> R -> R): commutative op -> commutative (ptw op).
  Proof.
    by move => ass x y; apply/functional_extensionality => n; apply/ass.
  Qed.

  Lemma ptwDl R (op op': R -> R -> R):
    left_distributive op op' -> left_distributive (ptw op) (ptw op').
  Proof.
    by move => ass x y z; apply/functional_extensionality => n; apply/ass.
  Qed.

  Lemma ptwDr R (op op': R -> R -> R):
    right_distributive op op' -> right_distributive (ptw op) (ptw op').
  Proof.
    by move => ass x y z; apply/functional_extensionality => n; apply/ass.
  Qed.  
  
  Definition curry R S T (f: R -> S -> T) rs := f rs.1 rs.2.

  Definition cptw R S T op := curry (@ptw R S T (uncurry op)).

  Lemma cptw_sur R S T (op: R * S -> T):
    op \is_surjective -> (cptw op) \is_surjective.
  Proof.
    move => sur ti.
    have /choice [f prp]: forall i, exists rs, op rs = ti i by move => i; apply/sur.
    exists (fun i =>  fst (f i), fun i => snd (f i)).
    apply/functional_extensionality => i.
    by rewrite -prp/cptw/curry/uncurry/ptw/=; case: (f i).
  Qed.
  
  Lemma ptw_cont X (op: X \*_cs X -> X):
    op \is_continuous -> (cptw op: X\^I \*_cs X\^I -> X\^I) \is_continuous.
  Proof.
    move => [F [/rlzr_F2MF Frop Fcont]].
    pose np := (@name_pair X X: names X -> names X -> names (X \*_cs X)).
    exists (make_mf (fun (phi: names (_\^I \*_cs (_\^I))) psi => forall n,
	                 F (np (fun q => lprj phi (n, q)) (fun q => rprj phi (n, q))) (fun q => psi (n, q)))).
    rewrite rlzr_F2MF; split => [phi [xn yn] [/= phinxn phinyn] | ].
    - have nms n: (np (fun q : questions X => lprj phi (n, q))
		      (fun q : questions X => rprj phi (n, q)))
                    \is_description_of ((xn n, yn n): X \*_cs X).
      + by split => /=; [apply/phinxn | apply/phinyn].
      split => [ | psi FpsiFpsi n].
      + have fd n:= (Frop (np (fun q => lprj phi (n, q))
			      (fun q => rprj phi (n, q))) (xn n, yn n) (nms n)).1.
        have [Fphi Fphiprp]:= choice _ fd.
        by exists (fun nq => Fphi nq.1 nq.2) => n /=; apply Fphiprp.
      have val n:= (Frop (np (fun q => lprj phi (n, q))
		             (fun q => rprj phi (n, q)))
                         (xn n, yn n) (nms n)).2.
      by rewrite /ptw/=; apply/val.
    apply cont_choice => phi Fphi /=FphiFphi [n q].
    pose phin:= np (fun q => lprj phi (n, q)) (fun q => rprj phi (n, q)).
    have [ | Lf mod]:= Fcont phin (fun q' => Fphi (n, q')); first exact/FphiFphi.
    exists (map (fun q' => match q' with
	                   | inl q'' => inl (n, q'')
	                   | inr q'' => inr (n, q'')
	                   end) (Lf q)) => psi /coin_lstn coin Fpsi eq.
    apply/(mod q (fun q' => match q' with
	                    | inl q'' => ((psi (inl (n, q''))).1, somea _)
	                    | inr q'' => (somea _, (psi (inr (n, q''))).2)
                            end) _ (fun q => Fpsi (n, q))); last by apply eq.
    apply/coin_lstn => [[q' | q'] lstn].
    + rewrite /phin/= -(coin (inl (n,q'))) /lprj//.
      by elim: (Lf q) lstn => // a L ih /= [ -> | ]; [left | right; apply/ih].
    rewrite /phin/= -(coin (inr (n,q'))) /rprj//.
    by elim: (Lf q) lstn => // a L ih /= [ -> | ]; [left | right; apply/ih].
  Qed.
End pointwise_operations.

Section isomorphism.
Definition sig2fun (X: cs) (f: X\^w) := exist_c (nat_dscrt f): cs_nat c-> X.

Definition sig2fun_rlzrf (X: cs) (phi: names (X\^w)) Lq' := match Lq'.1 with
	| nil => inl [:: tt]
	| (n :: L) => inr (phi (n, Lq'.2))
end.

Definition sig2fun_rlzr (X: cs) := F2MF (@sig2fun_rlzrf X).

Lemma sig2fun_rlzr_spec (X: cs): (@sig2fun_rlzr X) \realizes (F2MF (@sig2fun X)).
Proof.
rewrite F2MF_rlzr_F2MF => phi xn phinxn.
rewrite /= rlzr_F2MF => nf /= n eq.
split; first by exists (fun q => phi (n, q)) => q'; exists 2; rewrite /U/= eq.
move => psi val.
suff <-: (fun q => phi (n, q)) = psi by apply/phinxn.
apply/functional_extensionality => q.
have [m eq']:= val q; case: m eq' => //m; case: m => //m.
have ->: U (sig2fun_rlzrf phi) m.+2 nf q = U (sig2fun_rlzrf phi) 2 nf q.
- elim: m => // m; rewrite -addn1 -addn1 /U /=.
  by case: (U_rec (sig2fun_rlzrf phi) (m + 1 + 1) nf q).
by rewrite /U/= eq => [[]].
Qed.

Lemma sig2fun_rlzr_cntop (X: cs): (@sig2fun_rlzr X) \is_continuous_operator.
Proof.
rewrite F2MF_cont_choice => phi Lq'.
case E: Lq'.1 => [ | n L]; first by exists [::] => psi _; rewrite /sig2fun_rlzrf E.
by exists ([:: (n, Lq'.2)]); rewrite /sig2fun_rlzrf E => psi [->].
Qed.

Lemma sig2fun_cont (X: cs): (@sig2fun X) \is_continuous.
Proof.
by exists (@sig2fun_rlzr X); split; [apply/sig2fun_rlzr_spec | apply/sig2fun_rlzr_cntop].
Qed.

Definition fun2sig (X: cs) (xn: cs_nat c-> X):= projT1 xn: X\^w.

Definition fun2sig_rlzr X:= make_mf (fun (psi: names cs_nat c-> X) phi =>
	forall n, \F_(U psi) (fun _ => n) (fun q => phi (n, q))).

Lemma fun2sig_rlzr_spec X: (@fun2sig_rlzr X) \realizes (F2MF (@fun2sig X)).
Proof.
rewrite rlzr_F2MF => psi xn /rlzr_F2MF rlzr.
split => [ | phin Fpsiphi n].
	have prp: forall (n: nat), exists phi: questions X -> answers X, forall q,
  exists c : nat, U psi c (fun _ : unit => n) q = Some (phi q).
  	move => n.
  	have [ | [phi val prp]]//:= rlzr (fun _ => n) n.
  	exists phi => q; apply/val.
  have [phin nm]:= choice _ prp.
  exists (fun nq => phin nq.1 nq.2).
  move => n q /=; apply nm.
have [ | [phi val prp]]//:= rlzr (fun _ => n) n.
apply/prp => q.
apply/Fpsiphi.
Qed.

Lemma fun2sig_rlzr_cntop X: (@fun2sig_rlzr X) \is_continuous_operator.
Proof.
apply/cont_choice.
rewrite /fun2sig_rlzr => psi phi Fpsiphi [n q'].
have [ | mf mod]:= @FM_val_cont _ _ _ _ (fun _ => n) psi (fun q => phi (n, q)); first exact/(Fpsiphi n).
exists (mf q') => psi' coin Fpsi' val.
exact/(mod q' psi' coin (fun q => Fpsi' (n, q)))/val.
Qed.

Lemma fun2sig_cont X: (@fun2sig X) \is_continuous.
Proof.
exists (fun2sig_rlzr X); split; [exact/fun2sig_rlzr_spec | exact/fun2sig_rlzr_cntop].
Qed.

Lemma sig_iso_fun X: X\^w ~=~ (cs_nat c-> X).
Proof.
exists (exist_c (sig2fun_cont X)).
exists (exist_c (fun2sig_cont X)).
by split => [f | f]; last apply/eq_sub; apply functional_extensionality => n /=.
Qed.
End isomorphism.