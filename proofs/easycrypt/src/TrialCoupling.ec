(* The cut sequential rule run on outcomes with p_U coupled with the same rule run on outcomes
   with 2^-16: they differ with probability at most 2^16 E|p_U - 2^-16| (DESIGN-NOTES A.6). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal DInterval RealSeries Finite.
require import Suite3 Chain Collision Passphrase Generation Selection PassRate TrialGames.
require (*--*) DMap.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- Both outcome probabilities are k / 2^256 ------------------------------------------------- *)
op N256 : int = 2 ^ 256.
op dr : int distr = dinter 0 (N256 - 1).
op kU (fS : state * pp -> seed) (fT : seed -> W16.word * W240.word) (q : pp) : int =
  count (pass fS fT q) st_enum.
op k16 : int = 2 ^ 240.

lemma N256_gt0 : 0 < N256 by rewrite /N256; smt(IntOrder.expr_gt0).

lemma N256_r : N256%r = 2%r ^ 256.
proof. by rewrite /N256 RField.fromintXn. qed.

lemma dr_ll : is_lossless dr.
proof. by apply dinter_ll; smt(N256_gt0). qed.

lemma kU_bound fS fT q : 0 <= kU fS fT q <= N256.
proof. by rewrite /kU /N256 -size_st_enum; smt(count_ge0 count_size). qed.

lemma k16_bound : 0 <= k16 <= N256.
proof.
rewrite /k16 /N256; split; 1: smt(IntOrder.expr_gt0).
by move=> _; apply IntOrder.ler_weexpn2l.
qed.

lemma sum_b2r ['a] (P : 'a -> bool) (s : 'a list) : big predT (fun x => b2r (P x)) s = (count P s)%r.
proof.
elim: s => [|x s ih]; 1: by rewrite big_nil.
by rewrite big_cons /predT /= ih; case: (P x) => _ /=; smt().
qed.

lemma pU_kU fS fT q : mu dstate (pass fS fT q) = (kU fS fT q)%r / 2%r ^ 256.
proof.
rewrite mu_dstate big_mkcond /kU (eq_bigr _ _ (fun e => b2r (pass fS fT q e) * inv (2%r ^ 256))).
- by move=> e _ /=; case: (pass fS fT q e).
rewrite -mulr_suml; congr.
exact (sum_b2r (pass fS fT q) st_enum).
qed.

lemma p16_k16 : p16 = k16%r / 2%r ^ 256.
proof.
rewrite /p16 /k16 -RField.fromintXn // (_ : 256 = 240 + 16) // RField.exprD_nneg //.
by field; smt(RealOrder.expr_gt0).
qed.

lemma dr_lt k : 0 <= k <= N256 => mu dr (fun r => r < k) = k%r / 2%r ^ 256.
proof.
move=> hk; rewrite /dr dinterE.
rewrite (_ : filter (fun r => r < k) (range 0 (N256 - 1 + 1)) = range 0 k).
- rewrite (range_cat k 0 (N256 - 1 + 1)) 1,2:/# filter_cat.
  rewrite eq_in_filter_predT => [x /mem_range /#|]; rewrite eq_in_filter_pred0 => [x /mem_range /#|].
  by rewrite cats0.
by rewrite size_range (_ : max 0 (k - 0) = k) 1:/# (_ : max 0 (N256 - 1 - 0 + 1) = N256) 1:/# N256_r.
qed.

lemma dbiased_dr k : 0 <= k <= N256 =>
  Biased.dbiased (k%r / 2%r ^ 256) = dmap dr (fun r => r < k).
proof.
move=> hk; have hp : 0%r <= k%r / 2%r ^ 256 <= 1%r.
- rewrite -N256_r; split; 1: smt(N256_gt0).
  by move=> _; rewrite ler_pdivr_mulr; smt(N256_gt0).
apply eq_distr => b; rewrite Biased.dbiased1E Biased.clamp_id // dmap1E /(\o) /pred1.
case: b => _.
- by rewrite -(dr_lt k hk); apply mu_eq => r /#.
by rewrite (mu_eq _ _ (predC (fun r => r < k))) 1:/# mu_not dr_lt // dr_ll.
qed.

(* ---- The coupled game: the cut sequential rule, padded to ntr steps ------------------------- *)
(* Each trial draws r uniformly below 2^256; its outcome with p_U is r < |U| and with 2^-16 is
   r < 2^240. The game returns one of them as the outcome (real or not) and records in bad whether
   they ever differ. *)
module CC (D : CONTO) = {
  var bad : bool
  proc main(real : bool) : bool = {
    var y, om, b, ok, i, r, x, x';
    Gen.p <$ dP;
    Gen.q <$ dQ;
    RSE.FunRO.init(); RTE.FunRO.init(); R.RO.init(); RW.RO.init();
    Trials.q <- Gen.q; Trials.outs <- [];
    bad <- false; ok <- false; i <- -1; SvO.i <- -1;
    while (i + 1 < ntr) {
      if (!ok) {
        r <$ dr;
        x <- r < kU RSE.FunRO.f RTE.FunRO.f Trials.q;
        x' <- r < k16;
        bad <- bad \/ x <> x';
        ok <- if real then x else x';
        Trials.outs <- rcons Trials.outs ok;
        SvO.i <- i + 1;
      }
      i <- i + 1;
    }
    Gen.e <- witness;
    if (0 <= SvO.i < size Trials.outs) {
      Gen.e <$ dtrial (SvO.i, nth false Trials.outs SvO.i, (RSE.FunRO.f, RTE.FunRO.f, Trials.q));
    }
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPSTO(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    return b;
  }
}.

(* A trial with p_U as the threshold r < |U| of a uniform r. *)
module TBR = {
  proc trial() : bool = { var r; r <$ dr; return r < kU RSE.FunRO.f RTE.FunRO.f Trials.q; }
}.

equiv trial_eq : TBO.trial ~ TBR.trial :
  TBO.p{1} = (kU RSE.FunRO.f RTE.FunRO.f Trials.q)%r{2} / 2%r ^ 256 ==> ={res}.
proof.
bypr (res{1}) (res{2}) => // &1 &2 a hp.
have -> : Pr[TBO.trial() @ &1 : res = a] = mu1 (Biased.dbiased TBO.p{1}) a.
- by byphoare (_ : TBO.p = TBO.p{1} ==> res = a) => //; proc; rnd; auto => />.
have -> : Pr[TBR.trial() @ &2 : res = a] =
          mu1 (dmap dr (fun r => r < kU RSE.FunRO.f{2} RTE.FunRO.f{2} Trials.q{2})) a.
- byphoare (_ : RSE.FunRO.f = RSE.FunRO.f{2} /\ RTE.FunRO.f = RTE.FunRO.f{2} /\ Trials.q = Trials.q{2} ==>
                res = a) => //; proc; rnd; auto => />.
  by rewrite dmap1E /(\o) /pred1; apply mu_eq => r /#.
by rewrite hp dbiased_dr // kU_bound.
qed.

module FROr (D : CONTO) = {
  proc main() : bool = {
    var y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.outs <- [];
    SvO.i <@ Seq(Rec(TBR)).select();
    Gen.e <- witness;
    if (0 <= SvO.i < size Trials.outs) {
      Gen.e <$ dtrial (SvO.i, nth false Trials.outs SvO.i, (RSE.FunRO.f, RTE.FunRO.f, Trials.q));
    }
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPSTO(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    return b;
  }
}.

lemma fro_r (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                         -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO})
            (ev : bool -> bool list -> bool) &m :
  Pr[FRO(Seq, D).main() @ &m : ev res Trials.outs] = Pr[FROr(D).main() @ &m : ev res Trials.outs].
proof.
byequiv (_ : ={glob D} ==> ={res, Trials.outs}) => //; proc.
call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
seq 10 9 : (={glob D, Gen.p, Gen.q, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f, Trials.q, Trials.outs, SvO.i}).
- inline Seq(Rec(TBO)).select Seq(Rec(TBR)).select; wp.
  while (={ok, i, Trials.outs, RSE.FunRO.f, RTE.FunRO.f, Trials.q} /\
         TBO.p{1} = (kU RSE.FunRO.f RTE.FunRO.f Trials.q)%r{2} / 2%r ^ 256).
  + wp; call (_ : ={Trials.outs, RSE.FunRO.f, RTE.FunRO.f, Trials.q} /\
                  TBO.p{1} = (kU RSE.FunRO.f RTE.FunRO.f Trials.q)%r{2} / 2%r ^ 256 ==>
                  ={res, Trials.outs, RSE.FunRO.f, RTE.FunRO.f, Trials.q} /\
                  TBO.p{1} = (kU RSE.FunRO.f RTE.FunRO.f Trials.q)%r{2} / 2%r ^ 256).
    * by proc; wp; call trial_eq; auto.
    by auto.
  by inline *; auto => />; smt(pU_kU).
by sp; if => //; auto.
qed.

lemma fror_cc (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                           -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC})
              (ev : bool -> bool list -> bool) &m :
  Pr[FROr(D).main() @ &m : ev res Trials.outs] = Pr[CC(D).main(true) @ &m : ev res Trials.outs].
proof.
byequiv (_ : ={glob D} /\ real{2} ==> ={res, Trials.outs}) => //; proc.
inline Seq(Rec(TBR)).select.
call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
swap{1} [5 .. 6] -4; swap{1} 3 1.
seq 8 8 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs} /\
           real{2}).
- by inline *; auto.
splitwhile{2} 5 : (!ok).
seq 3 5 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs,
             ok, i} /\ SvO.i{2} = i{2} /\ real{2} /\ (ok{2} \/ !(i{2} + 1 < ntr))).
- while (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs,
           ok, i} /\ SvO.i{2} = i{2} /\ real{2}).
  + rcondt{2} 1; 1: by auto.
    by inline Rec(TBR).trial TBR.trial; wp; rnd; auto => /> /#.
  by auto => /> /#.
seq 1 1 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs,
             SvO.i}).
- wp; while{2} (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs} /\
                SvO.i{2} = i{1} /\ (ok{2} \/ !(i{2} + 1 < ntr))) (ntr - i{2}).
  + by move=> &1 z; rcondf 1; auto => /> /#.
  by auto => /> /#.
by sp; if => //; auto.
qed.

lemma enc_llO : islossless Net(Ideal).enc.
proof. by proc; while true (12 - i); [move=> z; wp; inline *; auto; smt(dans_ll) | auto => /#]. qed.

(* Up to bad: the run with p_U and the run with 2^-16 agree until the two outcomes of a trial
   differ. *)
lemma cc_upto (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                           -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC})
              (ev : bool -> bool list -> bool) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[CC(D).main(true) @ &m : ev res Trials.outs] <=
  Pr[CC(D).main(false) @ &m : ev res Trials.outs /\ !CC.bad] + Pr[CC(D).main(false) @ &m : CC.bad].
proof.
move=> Dll.
have h : Pr[CC(D).main(true) @ &m : ev res Trials.outs] <=
         Pr[CC(D).main(false) @ &m : (ev res Trials.outs /\ !CC.bad) \/ CC.bad].
- byequiv (_ : ={glob D} /\ real{1} /\ !real{2} ==>
               ={CC.bad} /\ (!CC.bad{2} => ={res, Trials.outs})) => //; 2: smt().
  proc.
  seq 13 13 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, CC.bad} /\
               (!CC.bad{2} => ={Trials.outs, SvO.i})).
  + while (={i, glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, CC.bad} /\
           (!CC.bad{2} => ={ok, Trials.outs, SvO.i}) /\ real{1} /\ !real{2}).
    * wp; case (CC.bad{2}).
      - if{1}; if{2}.
        + by wp; rnd; auto => /> /#.
        + by wp; rnd{1}; auto => />; smt(dr_ll).
        + by wp; rnd{2}; auto => />; smt(dr_ll).
        by auto => /> /#.
      if; 1: smt().
      - by wp; rnd; auto => /> /#.
      by auto => /> /#.
    by inline *; auto => /> /#.
  case (CC.bad{2}).
  + wp; call{1} Dll; call{2} Dll; call{1} rw_get_ll; call{2} rw_get_ll; call{1} enc_llO; call{2} enc_llO.
    call{1} (_ : true ==> true); 1: by proc; auto.
    call{2} (_ : true ==> true); 1: by proc; auto.
    by sp; if{1}; [rnd{1} |]; (if{2}; [rnd{2} |]); auto => />; smt(dtrial_ll).
  call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
  call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
  call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
  call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
  by sp; if; [smt() | auto => /> /# | auto => /> /#].
have : Pr[CC(D).main(false) @ &m : (ev res Trials.outs /\ !CC.bad) \/ CC.bad] <=
       Pr[CC(D).main(false) @ &m : ev res Trials.outs /\ !CC.bad] + Pr[CC(D).main(false) @ &m : CC.bad].
- by rewrite Pr[mu_or]; smt(mu_bounded).
smt().
qed.

(* ---- The chance that the two outcomes ever differ ---------------------------------------------- *)
op dgap (fS : state * pp -> seed) (fT : seed -> W16.word * W240.word) (q : pp) : real =
  `|(kU fS fT q)%r - k16%r| / 2%r ^ 256.

lemma dr_gap fS fT q : mu dr (fun r => (r < kU fS fT q) <> (r < k16)) = dgap fS fT q.
proof.
have hk := kU_bound fS fT q; have h16 := k16_bound.
have hN : 0%r < 2%r ^ 256 by smt(RealOrder.expr_gt0).
have hU := dr_lt (kU fS fT q) hk; have h6 := dr_lt k16 h16.
rewrite /dgap; case: (kU fS fT q <= k16) => hle.
- have h := mu_split dr (fun r => r < k16) (fun r => r < kU fS fT q).
  have e1 : mu dr (predI (fun r => r < k16) (fun r => r < kU fS fT q)) = mu dr (fun r => r < kU fS fT q).
  + by apply mu_eq => r /#.
  have e2 : mu dr (fun r => (r < kU fS fT q) <> (r < k16)) =
            mu dr (predI (fun r => r < k16) (predC (fun r => r < kU fS fT q))) by apply mu_eq => r /#.
  have hr : (kU fS fT q)%r <= k16%r by rewrite le_fromint.
  rewrite e2 (_ : `|(kU fS fT q)%r - k16%r| = k16%r - (kU fS fT q)%r) 1:/#.
  have -> : (k16%r - (kU fS fT q)%r) / 2%r ^ 256 = k16%r / 2%r ^ 256 - (kU fS fT q)%r / 2%r ^ 256 by field; smt().
  smt().
have h := mu_split dr (fun r => r < kU fS fT q) (fun r => r < k16).
have e1 : mu dr (predI (fun r => r < kU fS fT q) (fun r => r < k16)) = mu dr (fun r => r < k16).
- by apply mu_eq => r /#.
have e2 : mu dr (fun r => (r < kU fS fT q) <> (r < k16)) =
          mu dr (predI (fun r => r < kU fS fT q) (predC (fun r => r < k16))) by apply mu_eq => r /#.
have hr : k16%r <= (kU fS fT q)%r by rewrite le_fromint /#.
rewrite e2 (_ : `|(kU fS fT q)%r - k16%r| = (kU fS fT q)%r - k16%r) 1:/#.
have -> : ((kU fS fT q)%r - k16%r) / 2%r ^ 256 = (kU fS fT q)%r / 2%r ^ 256 - k16%r / 2%r ^ 256 by field; smt().
smt().
qed.

lemma dgap_pU fS fT q : dgap fS fT q = `|mu dstate (pass fS fT q) - p16|.
proof.
have hN : 0%r < 2%r ^ 256 by smt(RealOrder.expr_gt0).
rewrite /dgap pU_kU p16_k16.
rewrite (_ : (kU fS fT q)%r / 2%r ^ 256 - k16%r / 2%r ^ 256 = ((kU fS fT q)%r - k16%r) / 2%r ^ 256).
- by field; smt().
by rewrite RealOrder.normrM RealOrder.normrV 1:/# RealOrder.gtr0_norm.
qed.

(* The beginning of the coupled game, up to the end of the trials, with outcomes of 2^-16. *)
module CCB = {
  proc main() : unit = {
    var ok, i, r, x, x';
    Gen.p <$ dP;
    Gen.q <$ dQ;
    RSE.FunRO.init(); RTE.FunRO.init();
    Trials.q <- Gen.q; Trials.outs <- [];
    CC.bad <- false; ok <- false; i <- -1; SvO.i <- -1;
    while (i + 1 < ntr) {
      if (!ok) {
        r <$ dr;
        x <- r < kU RSE.FunRO.f RTE.FunRO.f Trials.q;
        x' <- r < k16;
        CC.bad <- CC.bad \/ x <> x';
        ok <- x';
        Trials.outs <- rcons Trials.outs ok;
        SvO.i <- i + 1;
      }
      i <- i + 1;
    }
  }
}.

lemma cc_ccb (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[CC(D).main(false) @ &m : CC.bad] = Pr[CCB.main() @ &m : CC.bad].
proof.
move=> Dll; byequiv (_ : !real{1} ==> ={CC.bad}) => //; proc.
wp; call{1} Dll; call{1} rw_get_ll; call{1} enc_llO; call{1} (_ : true ==> true); 1: by proc; auto.
seq 13 11 : (={CC.bad}).
- while (={i, ok, CC.bad, Trials.outs, SvO.i, RSE.FunRO.f, RTE.FunRO.f, Trials.q} /\ !real{1}).
  + by wp; if => //; auto => />.
  by inline *; auto.
by sp; if{1}; [rnd{1} |]; auto => />; smt(dtrial_ll).
qed.

lemma dgap_ge0 fS fT q : 0%r <= dgap fS fT q.
proof. by rewrite /dgap; apply divr_ge0; smt(RealOrder.expr_gt0). qed.

lemma Ep_xr ['a] (d : 'a distr) (h : 'a -> real) :
  is_finite (support d) => (forall x, 0%r <= h x) => Ep d (fun x => (h x)%xr) = (E d h)%xr.
proof.
move=> hfin hpos; rewrite EP_E.
- by apply is_real_sM.
- rewrite to_real_mdfun /=; have := hasE_finite d h hfin; rewrite /hasE.
  have e : forall x, h x * mu1 d x = mu1 d x * (h x)%pos by move=> x; rewrite /(%pos); smt().
  by rewrite (eq_summable _ _ e).
have -> // : to_real (fun (x : 'a) => (h x)%xr) = h.
by apply fun_ext => x; rewrite /to_real /=; smt(to_real_of_real to_pos_pos).
qed.

lemma dr_fin : is_finite (support dr).
proof. by apply/uniform_finite/dinter_uni. qed.

lemma hasR (f : int -> real) : hasE dr f.
proof. exact (hasE_finite _ _ dr_fin). qed.

lemma ccb_e : ehoare [CCB.main : (inv (2%r ^ 120) - inv (2%r ^ 138))%xr ==> (CC.bad)%xr].
proof.
proc.
while (true `|` (b2r CC.bad + (if ok then 0%r else 2%r ^ 16 * dgap RSE.FunRO.f RTE.FunRO.f Trials.q))%xr).
- move=> &hr; apply xle_cxr_r => _; rewrite cxr_true; apply xr_le.
  by have := dgap_ge0 RSE.FunRO.f{hr} RTE.FunRO.f{hr} Trials.q{hr}; smt(b2r_ge0 RealOrder.expr_gt0).
- auto => &hr /=; apply xle_cxr_r => _.
  case: (ok{hr}) => hok /=; 1: by [].
  pose c := 2%r ^ 16 * dgap RSE.FunRO.f{hr} RTE.FunRO.f{hr} Trials.q{hr}.
  pose g := fun r0 => (r0 < kU RSE.FunRO.f{hr} RTE.FunRO.f{hr} Trials.q{hr}) <> (r0 < k16).
  have hc : 0%r <= c by rewrite /c; apply mulr_ge0; [smt(RealOrder.expr_gt0) | apply dgap_ge0].
  rewrite Ep_xr 1:dr_fin => [r0 /= | ]; 1: smt(b2r_ge0).
  apply xr_le.
  apply (ler_trans (E dr (fun r0 => b2r CC.bad{hr} + (b2r (g r0) + c * b2r (!(r0 < k16)))))).
  + by apply ler_exp; 1,2: exact hasR; move=> r0 /=; rewrite /g /b2r; smt().
  rewrite expD 1,2:hasR expC dr_ll expD 1,2:hasR expZ !exp_b2r /g dr_gap.
  rewrite (mu_eq _ _ (predC (fun r0 => r0 < k16))) 1:/# mu_not dr_ll dr_lt 1:k16_bound -p16_k16.
  have -> : c * (1%r - p16) = c - dgap RSE.FunRO.f{hr} RTE.FunRO.f{hr} Trials.q{hr}.
  + by rewrite /c /p16; field; smt(RealOrder.expr_gt0).
  smt().
inline *; auto => &hr /=.
rewrite -/dfS -/dfT.
have hb : forall q, Ep dfS (fun f => Ep dfT (fun f0 => (2%r ^ 16 * dgap f f0 q)%xr)) <=
                    (inv (2%r ^ 120) - inv (2%r ^ 138))%xr.
- move=> q.
  rewrite (eq_Ep _ _ (fun f => (E dfT (fun f0 => 2%r ^ 16 * dgap f f0 q))%xr)) => [f _ /= |].
  + by rewrite Ep_xr 1:dfT_fin => [f0 /= |]; 1: smt(dgap_ge0 RealOrder.expr_gt0).
  rewrite Ep_xr 1:dfS_fin => [f /= |].
  + by apply exp_ge0 => f0; smt(dgap_ge0 RealOrder.expr_gt0).
  apply xr_le.
  rewrite (_ : (fun f => E dfT (fun f0 => 2%r ^ 16 * dgap f f0 q)) =
               fun (f : state * pp -> seed) => 2%r ^ 16 * E dfT (fun f0 => `|mu dstate (pass f f0 q) - p16|)).
  + apply fun_ext => f; rewrite -expZ; congr; apply fun_ext => f0; by rewrite dgap_pU.
  rewrite expZ.
  have h := E_pU_tight q.
  have -> : inv (2%r ^ 120) - inv (2%r ^ 138) = 2%r ^ 16 * (inv (2%r ^ 136) - inv (2%r ^ 136) / 2%r ^ 18).
  + rewrite (_ : 136 = 16 + 120) // (_ : 138 = 18 + 120) // !RField.exprD_nneg //.
    by field; smt(RealOrder.expr_gt0).
  by apply ler_wpmul2l => //; smt(RealOrder.expr_gt0).
apply (xle_trans (Ep dP (fun _ => Ep dQ (fun _ => (inv (2%r ^ 120) - inv (2%r ^ 138))%xr)))).
- by apply le_Ep => p _ /=; apply le_Ep => q _ /=; exact (hb q).
by rewrite !EpC dQ_ll dP_ll.
qed.

lemma e120_138 : 0%r <= inv (2%r ^ 120) - inv (2%r ^ 138).
proof.
rewrite subr_ge0; apply lef_pinv; 1,2: smt(RealOrder.expr_gt0).
by apply RealOrder.ler_weexpn2l.
qed.

lemma ccb_bad &m : Pr[CCB.main() @ &m : CC.bad] <= inv (2%r ^ 120) - inv (2%r ^ 138).
proof.
byehoare (_ : (inv (2%r ^ 120) - inv (2%r ^ 138))%xr ==> (CC.bad)%xr) => //; 1: exact ccb_e.
exact e120_138.
qed.

(* The chance that the run with 2^-16 and the run with p_U ever differ is at most 2^16 * 2^-136. *)
lemma cc_bad (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[CC(D).main(false) @ &m : CC.bad] <= inv (2%r ^ 120) - inv (2%r ^ 138).
proof. by move=> Dll; rewrite (cc_ccb D &m Dll); exact (ccb_bad &m). qed.
