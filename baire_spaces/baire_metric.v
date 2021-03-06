(** This file considers spaces of the form Q -> A where Q is countable.
    Given an enumeration of Q it defines a metric and proves that the
    notions of continuity for functions on Baire space and functions
    of the constructed metric space coincide. **)
From mathcomp Require Import all_ssreflect.
From metric Require Import reals metric standard.
From Coquelicot Require Import Coquelicot.
Require Import all_count all_cont baire iseg classical_cont classical_count seq_cont.
Require Import Reals Psatz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope metric_scope.
Local Open Scope baire_scope.

Section baire_metric.
  Context Q (cnt: nat -> Q).
  Hypothesis sur: cnt \is_surjective.
  Context (A: eqType).
  Notation B := (Q -> A).
  Implicit Types (phi psi: B).

  Lemma coin_has phi psi n: phi \and psi \coincide_on (iseg cnt n) <->
                            ~~ has (fun i => phi (cnt i) != psi (cnt i)) (init_seg n).
  Proof.
    elim: n => // n ih /=.
    rewrite ih.
    split => [[eq /negP hs'] | /orP hs].
    - by apply/negP => /orP [/negP neq| hs]; [apply/neq/eqP | apply/hs'].
    split; first by apply/eqP/negP => neq; apply/hs; left; apply/negP.
    by apply/negP => hs'; apply/hs; right.
  Qed.

  Lemma inP (T: eqType) q (L: seq T): reflect (List.In q L) (q \in L).
  Proof.
    elim: L => [ | t L ih]; first by apply/ReflectF.
    case E: (q \in t :: L).
    - rewrite seq.inE in E.
      by apply/ReflectT; case/orP: E => [/eqP -> | /ih ]; [left | right].
    apply/ReflectF => [/= [eq | lstn]]; suff: false by trivial.
    - by rewrite -E seq.inE; apply/orP; left; rewrite eq.
    by rewrite -E seq.inE; apply/orP; right; apply/ih.
  Qed.  

  Definition baire_val_seq phipsi n :=
    search (fun i => (phipsi.1 (cnt i): A) != phipsi.2 (cnt i)) n.

  Lemma bvls_spec phi psi n:
    (forall m, (m < n)%nat -> phi (cnt m) = psi (cnt m)) <->
    baire_val_seq (phi, psi) n = n.
  Proof.
    split => [prp | eq m ineq].
    - rewrite/baire_val_seq /=.
      apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/search_le.
      rewrite leqNgt search_find -{2}(size_iota 0 n) -has_find.
      apply/negP => /hasP [m]; rewrite mem_iota add0n => /andP [_ ineq] /negP prp'.
      exact/prp'/eqP/prp.
    apply/eqP/negP => /negP neq.
    suff: (baire_val_seq (phi, psi) n < n)%nat by rewrite eq => /leP; lia.
    rewrite /baire_val_seq search_find -{2}(size_iota 0 n) -has_find; apply/hasP.
    by exists m => //; rewrite mem_iota add0n; apply/andP.  
  Qed.

  Lemma bvls_ext phi psi n:
    (forall m, (m < n)%nat -> phi (cnt m) = psi (cnt m)) ->
    baire_val_seq (phi, psi) n = n.
  Proof. by move => /bvls_spec. Qed.

  Lemma bvls_geq phi psi n: (baire_val_seq (phi, psi) n <= n)%nat.
  Proof. exact/search_le. Qed.

  Lemma bvls_eq_coin phi psi n:
    baire_val_seq (phi, psi) n = n <-> phi \and psi \coincide_on (iseg cnt n).
  Proof.
    rewrite coin_lstn -bvls_spec.
    split => [prp q /lstn_iseg [m [ineq <-]] | prp m ineq]; first exact/prp.
    by apply/prp/lstn_iseg; exists m.
  Qed.
    
  Lemma coin_bvls phi psi n: phi \and psi \coincide_on (iseg cnt (baire_val_seq (phi, psi) n)).
  Proof.
    elim: n => // n ih.
    rewrite /baire_val_seq searchS.
    case: ifP => // /eqP eq.
    case: ifP => /= [neq | /eqP eq']; first by rewrite -eq; apply/ih.
    by split; last by rewrite -eq; apply/ih.
  Qed.

  Lemma max_min n m: Rmax (/2^n) (/2^m) = /2^(minn n m).
  Proof.
    case E: (n <= m)%nat.
    - have ->:= minn_idPl E.
      by rewrite Rmax_left //; apply/tpmnP/E.
    move: E => /negP/negP.
    rewrite -ltnNge => ineq.
    have ineq': (m <= n)%nat by apply/leq_trans/ineq.
    have ->:= minn_idPr ineq'.
    by rewrite Rmax_right //; apply/tpmnP.
  Qed.

  Lemma search_correct_le (p: pred nat) n m: p m -> (m <= n)%nat -> p (search p n).
  Proof.
    move => pm ineq.
    rewrite -(search_eq pm ineq).
    exact/search_correct.
  Qed.

  Lemma bvls_inc phi psi n m:
    (n <= m)%nat -> (baire_val_seq (phi, psi) n <= baire_val_seq (phi, psi) m)%nat.
  Proof. exact/search_inc. Qed.

  Lemma bvls_lt phi psi i n:
    (i <= n)%nat -> (i < baire_val_seq (phi, psi) n)%nat -> phi (cnt i) = psi (cnt i).
  Proof.
    rewrite ltnNge => iln /negP ineq.
    apply/eqP/negP => /negP neq.
    exact/ineq/search_min.
  Qed.

  Lemma bvls_trngl phi psi psi' n:
     (minn (baire_val_seq (phi, psi') n) (baire_val_seq (psi', psi) n) <= baire_val_seq (phi, psi) n)%nat.
  Proof.    
    case eq: (baire_val_seq (phi, psi) n == n).
    - move: eq => /eqP ->.
      by rewrite geq_min; apply/orP; left; apply/bvls_geq.
    move: eq => /eqP neq.
    rewrite leqNgt leq_min; apply/negP => /andP [ineq ineq'].
    pose k := baire_val_seq (phi, psi) n.
    apply/neq.
    rewrite -bvls_spec => m mln.
    apply/eqP/negP => /negP neq'.
    have /negP bvneq: phi (cnt k) != psi (cnt k).
    - apply/(@search_correct_le (fun i => phi (cnt i) != psi (cnt i))).
      apply/neq'.
      exact/leq_trans/mln.
    have eq: phi (cnt k) = psi' (cnt k) by apply/bvls_lt/ineq/search_le.
    have eq': psi' (cnt k) = psi (cnt k) by apply/bvls_lt/ineq'/search_le.
    by apply/bvneq/eqP; rewrite eq eq'.
  Qed.
      
  Lemma bvls_fchy phi psi: (fun n => /2^(baire_val_seq (phi, psi) n)) \is_fast_Cauchy_sequence.
  Proof.
    pose p i := phi (cnt i) != psi (cnt i).
    apply/cchy_eff_suff => n m ineq.
    have le: 0 <= /2^n by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    have le': 0 <= /2^m by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra.
    case E:(has p (seq.iota 0%nat n.+1)). 
    - move: E => /hasP => [[k]]; rewrite mem_iota add0n => /andP [_ ineq'] neq.      
      rewrite /p/d/= Rminus_diag_eq /baire_val_seq; first by split_Rabs; lra.
      do 2 f_equal; rewrite -(search_eq neq); last by apply/leq_trans/ineq'.
      by rewrite -[RHS](search_eq neq) //; apply/leq_trans/ineq/leq_trans/ineq'.
    rewrite /d /= bvls_ext => [ | k ineq']; last first.
    - apply/eqP/negP => neg.
      move: E => /hasP prp; apply/prp; exists k; last exact/negP.
      rewrite mem_iota add0n; apply/andP; split => //.
      by apply/leq_trans; first exact/ineq'.
    case E':(has (fun i => phi (cnt i) != psi (cnt i)) (seq.iota 0%nat m.+1)); last first. 
    - rewrite bvls_ext => [ | k ineq']; first by split_Rabs; lra.
    - apply/eqP/negP => neg.
      move: E' => /hasP prp; apply/prp; exists k; last exact/negP.
      by rewrite mem_iota add0n; apply/andP; split; last by apply/leq_trans; first exact/ineq'.
    suff: (/2 ^ baire_val_seq (phi, psi) m <= /2 ^ n).  
    - by have := tpmn_pos n; have := tpmn_pos (baire_val_seq (phi, psi) m); split_Rabs; lra.
    apply/tpmnP; rewrite /baire_val_seq /=.
    rewrite -(@search_fail p n); first exact/search_inc.
    move => k pk; rewrite ltnNge; apply/negP => kln.
    move: E => /hasP [].
    by exists k; first by rewrite mem_iota; apply/andP.
  Qed.
  
  Lemma bdsq_sym phi psi n: baire_val_seq (phi, psi) n = baire_val_seq (psi, phi) n.
  Proof.
    apply/search_ext => k ineq /=.
    by apply/eqP; case: ifP => /eqP // neg eq; apply/neg.    
  Qed.
    
  Definition mf_baire_distance := make_mf (fun phipsi =>
    efficient_limit (fun n => /2^(baire_val_seq phipsi n))).
    
  Lemma bdst_sing: mf_baire_distance \is_singlevalued.
  Proof. by move => [phi psi] r r' dst dst'; apply/metric.lim_eff_sing/dst'/dst. Qed.

  Lemma bdst0 phi: mf_baire_distance (phi,phi) 0.
  Proof.
    by move => n; rewrite bvls_ext; first by have:= tpmn_pos n; rewrite /d/=; split_Rabs; lra.
  Qed.

  Lemma bdst_tot: mf_baire_distance \is_total.
  Proof.
    move => [phi psi].
    have /fchy_lim_eff [ | r lmt]:= bvls_fchy phi psi; first exact/R_cmplt.
    by exists r.
  Qed.

  Lemma bdst_sym phi psi: mf_baire_distance (phi, psi) === mf_baire_distance (psi, phi).
  Proof. by split => dst n; rewrite bdsq_sym; apply/dst. Qed.

  Definition baire_distance phi psi := iota (mf_baire_distance (phi,psi)).

  Lemma bdst_spec phi psi: mf_baire_distance (phi, psi) (baire_distance phi psi).
  Proof.
    apply/(iota_correct (mf_baire_distance (phi,psi))).
    have [x val]:= bdst_tot (phi, psi).
    by exists x; split => // x' val'; apply/bdst_sing/val'/val.
  Qed.

  Lemma bdst_val phi psi x: mf_baire_distance (phi, psi) x -> baire_distance phi psi = x.
  Proof. move => dst; exact/bdst_sing/dst/bdst_spec. Qed.

  Lemma bdst_lim phi psi:
    metric.limit (fun n => /2 ^ (baire_val_seq (phi, psi) n)) (baire_distance phi psi).
  Proof. exact/lim_eff_lim/bdst_spec. Qed.
    
  Lemma dst_pos phi psi: 0 <= baire_distance phi psi.
  Proof.
    apply/lim_pos => [ | n]; first exact/lim_eff_lim/bdst_spec.
    exact/tpmn_pos.
  Qed.
  
  Lemma dst_sym phi psi: baire_distance phi psi = baire_distance psi phi.
  Proof. exact/bdst_val/bdst_sym/bdst_spec. Qed.

  Lemma dstxx phi: baire_distance phi phi = 0.
  Proof. exact/bdst_val/bdst0. Qed.

  Lemma dst_eq phi psi: baire_distance phi psi = 0 -> phi = psi.
  Proof.
    move => eq.
    apply/functional_extensionality => q.
    have [n <-]:= sur q.
    suff /eqP/bvls_spec prp: baire_val_seq (phi, psi) n.+1 == n.+1 by apply/ prp.
    rewrite eqn_leq; apply/andP; split; first exact/search_le.
    by apply/tpmnP; have := bdst_spec phi psi n.+1; rewrite /d /=; split_Rabs; lra.
  Qed.

  Lemma dst_trngl phi psi psi':
    baire_distance phi psi <= baire_distance phi psi' + baire_distance psi' psi.
  Proof.
    apply/lim_inc; [ | apply/lim_eff_lim/bdst_spec | apply/limD/lim_eff_lim/bdst_spec/lim_eff_lim/bdst_spec].
    move => n; rewrite /pointwise.ptw_op.
    apply/Rle_trans.
    - exact/tpmnP/bvls_trngl.
    rewrite -max_min.
    exact/Rmax_le_Rplus/tpmn_pos/tpmn_pos.
  Qed.

  Lemma search_lt p n: (search p n < n)%nat -> p (search p n).
  Proof.
    rewrite {1}search_find -{2}(size_iota 0 n) -has_find => /hasP [m].
    rewrite mem_iota add0n => /andP [_ mln] pm.
    apply/search_correct_le; first exact/pm.
    by apply/leq_trans/mln.
  Qed.
    
  Lemma dst_dscrt phi psi n:
    (baire_val_seq (phi, psi) n < n)%nat -> baire_distance phi psi = /2^(baire_val_seq (phi, psi) n).
  Proof.
    move => ineq.
    apply/cond_eq => eps /accf_tpmn [m [g0 mle]].
    apply/Rle_lt_trans/mle.
    have:= bdst_spec phi psi (maxn n m).
    have ->: baire_val_seq (phi, psi) (maxn n m) = baire_val_seq (phi, psi) n.
    - have /=prp:= search_lt ineq.
      rewrite /baire_val_seq/= -(search_eq _ (bvls_geq phi psi n)) //.
      have ineq': (baire_val_seq (phi, psi) n <= maxn n m)%nat by apply/leq_trans/leq_maxl/leq_trans/ineq.
      rewrite -(search_eq _ ineq') //.
    have /tpmnP:= leq_maxr n m.
    rewrite /d /baire_val_seq /=; lra.
  Qed.
    
  Lemma dst_coin phi psi n: baire_distance phi psi <= /2^n <->
                            phi \and psi \coincide_on (iseg cnt n).
  Proof.
    case lt: (baire_val_seq (phi, psi) n < n)%nat.
    - have ->:= dst_dscrt lt.
      split => [/tpmnP | /bvls_eq_coin coin]; first by rewrite leqNgt lt.
      by apply/tpmnP; rewrite coin.
    move: lt; rewrite ltnNge => /leP/leP ineq.
    have eq: baire_val_seq (phi, psi) n = n.
    - by apply/eqP; rewrite eqn_leq; apply/andP; split; first exact/bvls_geq.
    split => [dst | coin]; first exact/bvls_eq_coin.
    apply/cond_leq => eps /accf_tpmn [m [_ mle]].
    have:= bdst_spec phi psi (maxn n m.+1).
    rewrite /d/= => ineq'.
    have leq: baire_distance phi psi <= /2^baire_val_seq (phi, psi) (maxn n m.+1) + /2^maxn n m.+1.
    - by split_Rabs; lra.
    apply/Rle_trans; first exact/leq.
    apply/Rplus_le_compat; first by apply/tpmnP; rewrite -{1}eq; apply/search_inc/leq_maxl.
    apply/Rle_trans/Rlt_le/mle.
    exact/tpmnP/leq_trans/leq_maxr.
  Qed.

  Definition metric_baire_mixin: MetricSpace.mixin_of B :=
    MetricSpace.Mixin dst_pos dst_sym dstxx dst_eq dst_trngl.

  Canonical metric_baire: MetricSpace := MetricSpace.Pack metric_baire_mixin B.
 
Section continuity.
  (** This section assumes the existence of a minimal section for cnt. However,
      classically the existence of such a section can be proven. **)   
  Context (sec: Q -> nat).
  Hypothesis (ms: minimal_section cnt sec).
  Notation melt := (max_elt sec).
  
  Lemma lim_lim: (@metric.limit metric_baire) =~= baire.limit.
  Proof.
    move => phin phi.
    split => [lmt L | lmt eps /accf_tpmn [n [_ nle]]].
    - have [ | N prp]:= lmt (/2^(melt L)); first by apply/Rinv_0_lt_compat/pow_lt; lra.
      exists N => m ineq.
      apply/coin_subl/dst_coin/prp/ineq.
      exact/iseg_melt.
    have [N prp]:= lmt (iseg cnt n).
    exists N => m ineq.
    exact/Rle_trans/Rlt_le/nle/dst_coin/prp.
  Qed.

(** Since clasically continuity and sequential continuity are identical, the above can be
    used to prove that the continuity notions coincide. A direct proof is probably also
    possible but more work. **)
  
  Lemma cont_f_cont (F: B -> B): F \is_continuous_function <-> (F \is_continuous)%met.
  Proof.
    split => [/cont_F2MF cont | cont].
    - apply/metric.scnt_cont => phi phin.
      rewrite lim_lim => lmt.
      by apply/(cont_scnt cont); first exact/lmt.
    apply/cont_F2MF/scnt_cont.
    - by exists (F2MF cnt); split; [apply/F2MF_sing | rewrite -F2MF_cotot].
    move => phi phin Fphin Fphi .
    rewrite -lim_lim => lmt eq <-.
    have ->: Fphin = pointwise.ptw F phin by apply/functional_extensionality => n; rewrite -eq.
    exact/(metric.cont_scnt cont).
  Qed.

  Lemma cont_cont (F: B ->> B) f: F =~= (F2MF f)|_(dom F) ->
     F \is_continuous <-> ((@sub_fun _ _ (dom F) f) \is_continuous)%met.
  Proof.
    move => eq; split => [/cont_scnt cont | /metric.cont_scnt cont].
    - apply/metric.scnt_cont => phi phin lmt; rewrite lim_lim.
      apply/cont; first by rewrite -lim_lim; apply/lmt.
      - move => n /=; rewrite /pointwise.ptw /sub_fun/=.
        case: (phin n) => /= psin [Fpsin val].
        by have /= [_ ->]:= (eq psin Fpsin).1 val.
      case: (phi) => /= psi [Fpsi val]; rewrite /sub_fun/=.
      by have /= [_ ->]:= (eq psi Fpsi).1 val.
    apply/scnt_cont => [ | phi phin Fphin Fphi /lim_lim lmt valn val].
    - exists (F2MF cnt); split; first exact/F2MF_sing.
      by rewrite -F2MF_cotot; apply/sur.
    apply/lim_lim.
    have [phifd <-]:= (eq phi Fphi).1 val.
    have ->: Fphin = pointwise.ptw f phin.
    - apply/ functional_extensionality => n.
      by have [phinfd <-]:= (eq (phin n) (Fphin n)).1 (valn n).
    pose psi := exist _ _ phifd.
    have phinfd: forall n, (phin n) \from dom F by move => n; exists (Fphin n).                  
    pose psin n := exist _ _ (phinfd n).                                          
    move => eps eg0.
    have [N prp]:= cont (exist _ _ phifd) psin lmt eps eg0.
    exists N => m ineq.
    by have := prp m ineq.
  Qed.
  End continuity.
End baire_metric.
 