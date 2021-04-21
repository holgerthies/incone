From Coquelicot Require Import Coquelicot.
From mathcomp Require Import all_ssreflect.
From rlzrs Require Import all_rlzrs.
From metric Require Import reals.
Require Import all_cs_base classical_mach.
Require Import Reals Psatz FunctionalExtensionality ClassicalChoice.
Require Import axioms all_cs cs_mtrc metric_names hyper_spaces.
From metric Require Import all_metric reals standard Qmetric.
Require Import Ibounds IrealsZ.
Require Import search.
From Interval Require Import Interval_tactic.
From Interval Require Import Interval_specific_ops Interval_bigint_carrier Interval_stdz_carrier.
From Interval Require Import Interval_interval_float_full Interval_interval.
From Interval Require Import Interval_xreal.
Import BigN BigZ.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope Z_scope.
Import QArith.
Local Open Scope R_scope.
Import Interval_interval_float.

Definition to_pair d := if d is Float m e then (m, e) else (0%Z, 1%Z). 

Definition midpoint_errI I :=
  (to_pair (I.midpoint I), to_pair (SF2.sub Interval_definitions.rnd_UP 1%Z (I.upper I) (I.lower I))).

Definition make_iter T (rlzrf : T -> names_IR) phi m n :=
  if (rlzrf phi n) is Ibnd l u
  then
    if  (I.F'.le (SF2.sub_exact u l) (Float 1%Z (- (Z.of_nat m))%Z))
    then Ibnd l u
    else Inan
  else Inan.

Definition make_iter2 T (rlzrf : T -> names_IR) phi n := make_iter rlzrf phi 1 n.

Lemma bounded_non_nan I:
  bounded I -> exists u l, u <> Fnan /\ l <> Fnan /\ I = Ibnd u l.
Proof.
  rewrite /bounded => bnd.
  by case e: I bnd => [| l u]// /andP [lr ur]; exists l; exists u; case up: u ur; last case lp: l lr.
Qed.

Lemma make_iter_correct T (rlzrf : T -> B_(IR)) m phi x:
  rlzrf phi \is_name_of x -> (make_iter rlzrf phi m : B_(IR)) \is_name_of x. 
Proof.
  move => [phin1 phin2]; split => n.
  - by rewrite /make_iter2 /make_iter; case R: rlzrf => [| l u] //; case: ifP; try rewrite -R.
  case (phin2 (maxn n m)) => N Nprp.
  exists N => k kprp; rewrite /make_iter. 
  have [bnd] := Nprp k kprp.
  have [l [u [P1 [P2 ->/=]]]] := bounded_non_nan bnd => diam.
  suff ->: I.F'.le (SF2.sub_exact u l) (Float 1%Z (- (Z.of_nat m))%Z) = true.
  - have: /2^(maxn n m) <= /2^n by apply /tpmnP/leq_maxl.
    by split; simpl; try lra; first by case e: l; case e': u.
  rewrite /I.F'.le SF2.cmp_correct SF2.sub_exact_correct; case e: u; case e':l => //.
  rewrite !D2R_SF2toX -e -e' D2R_Float powerRZ2_neg_pos Rmult_1_l /Xcmp/Xsub /=.
  case cmp: (Raux.Rcompare (D2R u-D2R l) (/2^m)) => //; move: cmp => /Raux.Rcompare_Gt_inv.
  by have:/2^(maxn n m) <= /2^m; [apply /tpmnP/leq_maxr | lra].
Qed.

Definition Rmult_rlzrf' phi  := make_iter2 Rmult_rlzrf phi.
Definition Rplus_rlzrf' phi  := make_iter2 Rplus_rlzrf phi.
Definition Rdiv_rlzrf' phi  := make_iter2 Rdiv_rlzrf phi.
Definition Rminus_rlzrf' phi  := make_iter2 Rminus_rlzrf phi.

Notation "phi '\*' psi" := (Rmult_rlzrf' (pair (phi, psi)) : names_IR) (at level 3).
Notation "phi '\+' psi" := (Rplus_rlzrf' (pair (phi, psi)) : names_IR) (at level 4).
Notation "phi '\:' psi" := (Rdiv_rlzrf' (pair (phi, psi)) : names_IR) (at level 3).
Definition opp_rlzr phi := Rmult_rlzrf' (pair (FloattoIR (-1)%Z 0%Z,phi)).
Notation "phi '\-' psi" := (Rminus_rlzrf' (pair (phi, psi)) : names_IR) (at level 4).

Lemma mul_comp (phi psi : B_(IR)) (x y : R):
  phi \is_name_of x -> psi \is_name_of y -> (phi \* psi : B_(IR)) \is_name_of (x*y).
Proof.
  move => ? ?; have nm: pair (phi,psi) \describes (x,y) \wrt (IR \*_cs IR).
  - by rewrite prod_name_spec lprj_pair rprj_pair.
  by apply make_iter_correct; have /F2MF_rlzr sp := Rmult_rlzr_spec; apply (sp _ _ nm).
Qed.

Lemma plus_comp (phi psi : B_(IR)) (x y : R):
  phi \is_name_of x -> psi \is_name_of y -> (phi \+ psi : B_(IR)) \is_name_of (x+y).
Proof.
  move => ? ?; have nm: pair (phi,psi) \describes (x,y) \wrt (IR \*_cs IR).
  - by rewrite prod_name_spec lprj_pair rprj_pair.
  by apply make_iter_correct; have /F2MF_rlzr sp := Rplus_rlzr_spec; apply (sp _ _ nm).
Qed.

Lemma opp_comp phi (x : R): phi \is_name_of x -> (opp_rlzr phi: B_(IR)) \is_name_of -x.
Proof.
  move => phin; have -> : (-x = (-1)*x) by lra.
  by apply/mul_comp; first apply/FloattoIR_correct. 
Qed.

Lemma minus_comp phi psi (x y : R):
  phi \is_name_of x -> psi \is_name_of y -> (phi \- psi : B_(IR)) \is_name_of (x-y).
Proof.
  move => phin psin; have nm: pair (phi,psi) \describes (x,y) \wrt (IR \*_cs IR).
  - by rewrite prod_name_spec lprj_pair rprj_pair.
  by apply make_iter_correct; have /F2MF_rlzr sp := Rminus_rlzr_spec; apply (sp _ _ nm).
Qed.

Lemma div_comp phi psi (x y : R):
  y <> 0 -> phi \is_name_of x -> psi \is_name_of y -> (phi \: psi : B_(IR)) \is_name_of (x/y).
Proof.
  move => yneg0 phin psin.
  suff xyname : (pair (phi,psi) : B_(IR \*_cs IR)) \is_name_of (x,y).
  - apply make_iter_correct.
    have  :=  (Rdiv_rlzr_spec ).
    rewrite F2MF_slvs => sp.
    case (sp _ _  xyname) => [| xy [[_ /= xy_prop] P]]; first by exists (x/y).
    rewrite <- xy_prop.                                                              
    by apply P.                                                    
  rewrite prod_name_spec.
  by rewrite lprj_pair rprj_pair.
Qed.
Require Import Iextract.

Fixpoint logistic_map_cmp (phi r : names_IR)  N : IR_type:=
  match N with
  | 0%nat => phi
  | M.+1 => let P := memoize_real (logistic_map_cmp phi r M): names_IR in
           r \* P \* ((FloattoIR 1%Z 0%Z) \- P)
  end.

Definition log_map1 N m :=
  logistic_map_cmp (FloattoIR 1%Z (-1)%Z) (FloattoIR 15%Z (-2)%Z) N m.

Fixpoint pow n phi  :=
  match n with
  | 0%nat => FloattoIR 1%Z 0%Z
  | n'.+1 => phi \* (pow n' phi)
  end.

Fixpoint slowdown (phi : B_(IR)) m :=
  match m with
  | 0%nat => phi
  | m'.+1 => (FloattoIR 1%Z 0%Z) \* (slowdown phi m')
  end.

Definition pow_mu (phi : B_(IR)) (nm : nat * nat) := [:: nm.2].

Lemma pow_mu_is_mod : pow_mu \modulus_function_for (F2M (pow 100)).
Admitted.
Lemma pow_mu_is_mod_mod : pow_mu \modulus_function_for pow_mu.
Admitted.

Definition ass := (construct_associate.psi_FM (@Interval_interval_float.Inan (s_float Z Z): replies IR) 0%nat pow_mu (F2M (pow 50)) ).

Lemma logistic_map_cmp_is_name phi psi N (x0 r : R):
  phi \is_name_of x0 -> psi \is_name_of r ->
  exists x : R, (logistic_map_cmp phi psi N: B_(IR)) \is_name_of x.
Proof.
  move => phin psin.
  elim N => [| N' IH]; first by exists x0.
  rewrite /logistic_map_cmp memoize_real_correct.
  rewrite -/logistic_map_cmp.
  case IH => P Pprop.
  exists (r * P * (1 - P)).
  apply mul_comp.
  - by apply mul_comp.
  by apply minus_comp; try by apply FloattoIR_correct.
Qed.

Definition zero_seq nm := ((FloattoIR 1%Z (-Z.of_nat nm.1)%Z) nm.2). 
Definition lim := \F_limit_eff_rlzrM.
Definition speedup n s := (2 ^ (n+s))%nat.

Lemma speedup_gt s n : (n <= (speedup n s))%nat.
Proof.
  rewrite /speedup.
  elim n  => [ | n' IH]; first by apply /leP;lia.
  rewrite /addn /addn_rec.
  have -> : ((n'.+1 + s) = ((n'+s).+1))%coq_nat by rewrite /addn /addn_rec;lia.
  rewrite Nat.pow_succ_r'.
  have /leP := IH => IH'.
  apply /leP.
  have lt1 : (n'.+1 <= (2 ^ (n'+s)).+1)%coq_nat by lia.
  apply /Nat.le_trans.
  apply lt1.
  have -> : (2 * 2^ (n'+s))%coq_nat = (2^(n'+s) + 2 ^ (n'+s))%coq_nat by lia.
  suff : (1 <= 2^(n'+s))%coq_nat by lia.
  have {1}-> : (1%nat = (2 ^ 0)%nat)%coq_nat by auto.
  apply Nat.pow_le_mono_r; by lia.
Qed.

Definition one_half := (FloattoIR 1%Z (-1)%Z).
Fixpoint sqrt_approx x0 n x := match n with
                               | 0%nat => x0
                               | (S n') => let P := (sqrt_approx x0 n' x) in
                                          (/ 2) * (P + (x / P))
                               end.         
Fixpoint sqrt_approx_rlzr phi0 n phi :=
  match n with
  | 0%nat => phi0 
  | (S n') => let P := memoize_real (sqrt_approx_rlzr phi0 n' phi): names_IR in
             one_half \* (P \+ (phi \: P))
  end.

Definition two := (FloattoIR 1%Z 1%Z).
Definition one := (FloattoIR 1%Z 0%Z).

Lemma one_describes_one : (one \is_name_of 1).
Proof.
  suff <- : (D2R (Float 1%Z 0%Z)) = 1 by apply FloattoIR_correct.
  by rewrite D2R_Float //=;lra.
Qed.


Lemma speedup_correct (x : IR) (phi : B_(IR)) s:
  phi \is_name_of x -> (fun (p : Q_(IR)) => phi (speedup p s)) \is_name_of x.
Proof.
  move => [phin1 phin2].
  split => n; first by apply phin1.
  case (phin2 n) => N Nprp.
  exists N => k kprp.
  apply (Nprp (speedup k s)).
  rewrite /speedup /addn /addn_rec.
  apply /leP.
  move /leP :  kprp => kprp.
  apply /Nat.le_trans.
  apply kprp.
  elim k => [| k' IH]; first by lia.
  simpl.
  rewrite Nat.add_0_r.
  suff : (0 < 2 ^ (k'+s)%coq_nat)%coq_nat by lia.
  apply Nat.Private_NZPow.pow_pos_nonneg; by lia.
Qed.
Definition IR2Qmf := \F_(IR_RQ_rlzrM').
Lemma pwr2gt : forall n, (n <= (2 ^ (n+0)))%nat.
Proof.
  move => n.
  rewrite /addn/addn_rec Nat.add_0_r.
  move : n.
  elim => [ | n IH].
  apply /leP;lia.
  rewrite Nat.pow_succ_r'.
  have /leP := IH => IH'.
  apply /leP.
  have lt1 : (n.+1 <= (2 ^ n).+1)%coq_nat by lia.
  apply /Nat.le_trans.
  apply lt1.
  have -> : (2 * 2^ n)%coq_nat = (2^n + 2 ^ n)%coq_nat by lia.
  suff : (1 <= 2^n)%coq_nat by lia.
  have {1}-> : (1%nat = (2 ^ 0)%nat)%coq_nat by auto.
  apply Nat.pow_le_mono_r; by lia.
Qed.

Lemma logistic_map_in_dom phi psi N (x0 r : R) :(phi \is_name_of x0) -> (psi \is_name_of r) -> (logistic_map_cmp phi psi N) \from dom IR2Qmf.
Proof.
  move => phin psin.
  case (logistic_map_cmp_is_name N phin psin ) => x xprp.
  apply (F_M_realizer_IR_RQ (speedup_gt _) xprp).
  by apply F2MF_dom.
Qed.

Lemma log_map1_in_dom N : \Phi_(IR_RQ_rlzrM' (log_map1 N)) \is_total.
Proof.
  apply FM_dom.
  by apply (logistic_map_in_dom _ (FloattoIR_correct 1%Z (-1)%Z) (FloattoIR_correct 15%Z (-2)%Z)). 
Qed.


Eval vm_compute in (log_map1 5%nat 20%nat).
Definition diag_rlzrf X (phi : B_ X) := (pair (phi,phi)).

Lemma diag_rlzrf_spec X : (F2MF (@diag_rlzrf X)) \solves mf_diag.
  rewrite F2MF_slvs => phi x phin.
  case => t /=tprp.
  exists (x,x); split; first by auto.
  exists (phi,phi).
  split; by [apply pairK | split].
Qed.  


Definition tpnIR n := (FloattoIR 1%Z n).

Lemma tpnIR_spec n : (tpnIR n) \is_name_of (powerRZ 2 n).
Proof.
  rewrite /tpnIR.
  suff -> : (powerRZ 2 n) = (D2R (Float 1%Z n)) by apply FloattoIR_correct.
  by rewrite D2R_Float;lra.
Qed.

Definition tpmnIR_rlzr phi := (tpnIR (-(Z.of_nat (phi tt)))%Z).

Lemma tpmnIR_rlzr_spec : (F2MF tpmnIR_rlzr) \realizes (fun (n : nat) => (/ 2 ^ n)).
Proof.
  rewrite F2MF_rlzr => phi n phin.
  rewrite /tpmnIR_rlzr phin.
  rewrite <- powerRZ2_neg_pos.
  by apply tpnIR_spec.
Qed.

Definition QtoIR' q := (fun n => (QtoIR (nat2p n) q)) : B_(IR).

Lemma QtoIR'_correct q :((QtoIR' q) \is_name_of ((Qreals.Q2R q) : IR)).
Proof.
  split => n; first by apply QtoIR_correct.
  Search _ QtoIR.
  case (powerRZ_bound (Qreals.Q2R q)) => K [Kprp1 Kprp2].
  have Kprp3 : (1 < K+2+(Z.of_nat n))%Z by lia.
  apply IZR_lt in Kprp3.
  suff : exists (z : Z),(1 < z) /\ forall (k : Z), (z <= k ) -> (diam (QtoIR k q)) <= (powerRZ 2 (-(Z.of_nat n))%Z).
  - case => z [zprp1 zprp2].
    exists (Z.to_nat z).
    move => k kprp.
    split; first by apply QtoIR_bounded.
    rewrite /QtoIR'.
    have := (zprp2 (Z.of_nat k)).
    rewrite powerRZ2_neg_pos.
    move => H.
    have e : (z <= Z.of_nat k).
    rewrite <- (Z2Nat.id z); last by apply le_IZR;lra.
    apply IZR_le.
    apply inj_le.
    by apply /leP.
    have := (H e).
    suff -> : (Z.of_nat k) = (nat2p k) by auto.
    have : (Z.to_nat 1 < Z.to_nat z)%coq_nat by apply Z2Nat.inj_lt; by (try apply le_IZR; try apply lt_IZR;lra).
    move /leP : kprp.
    rewrite /nat2p.
    case k => [| k' _ _]; first by lia.
     by rewrite <- Pos.of_nat_succ, Zpos_P_of_succ_nat;lia.
  exists ((K+2+(Z.of_nat n))%Z).
  split => // k kprp.
  Search _ QtoIR.
  have p : (1 < k)%Z by apply lt_IZR; lra.
  apply /Rle_trans.
  apply (QtoIR_diam p Kprp2).
  rewrite !powerRZ_Rpower; try by lra.
  apply Rle_Rpower; try by lra.
  apply IZR_le.
  apply le_IZR in kprp.
  by lia.
Qed.


Lemma IR_RQ_RlzrM'_dom phi (x : IR) : (phi \is_name_of x) -> \Phi_(IR_RQ_rlzrM' phi) \is_total.
Proof.
  move => phin.
  apply FM_dom.
  rewrite /IR_RQ_rlzrM' /=.
  apply (F_M_realizer_IR_RQ (speedup_gt _) phin).
  by exists x.
Qed.

Definition qtoPair q := match q with
                          (q1 # q2) => (q1, q2)
                          end.
Definition print_interval d := ((to_pair (lower d)), (to_pair (upper d)), (qtoPair (diamQ d))).
Definition print_interval' I := match I with
                                 | None => (print_interval (two 0%nat))
                                 | Some d => (print_interval d)
                                  end.
(* (* Definition sqrt2' (p : nat):= (print_interval (sqrt2 p)). *) *)
(* Definition sqrt2'' m p := (print_interval' (use_first limit_eff_rlzrM sqrt2_approx (m,p)%nat)). *)
Definition log_map_Q N := (evaluate (log_map1_in_dom N)).
(* Compute ((FloattoIR 1%Z (-1)%Z) \: (FloattoIR 5%Z (-10)%Z) 10%nat). *)
Definition logistic_map_mp_rlzr' (N :nat) (p : BinPos.positive):= log_map_Q N (1#(10 ^ p)).

Extract Inlined Constant memoize_real => "Data.Function.Memoize.memoize".
Extraction "logisticC" cmp_float mantissa_shr logistic_map_mp_rlzr'.
