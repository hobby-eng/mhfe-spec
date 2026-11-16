(* The run with outcomes of 2^-16: the selected value no longer depends on them, and the
   reduction can draw them itself; the uncut sequential rule against the cut one. *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal DInterval RealSeries Finite.
require import Suite3 Chain Collision Passphrase Generation Selection PassRate TrialGames TrialCoupling.
import W128 StdBigop.Bigreal.BRA RealOrder.

lemma dtrial_index j j' b x : dtrial (j, b, x) = dtrial (j', b, x).
proof. by rewrite /dtrial. qed.

(* The selected trial passes. *)
op lastpass (i : int) (outs : bool list) = 0 <= i < size outs /\ nth false outs i.

(* The run with outcomes of 2^-16 and the selected value drawn from the passing values, whatever the
   outcomes. *)
module CF (D : CONTO) = {
  proc main() : bool = {
    var y, om, b, ok, i, r;
    Gen.p <$ dP;
    Gen.q <$ dQ;
    RSE.FunRO.init(); RTE.FunRO.init(); R.RO.init(); RW.RO.init();
    Trials.q <- Gen.q; Trials.outs <- [];
    ok <- false; i <- -1;
    while (i + 1 < ntr) {
      if (!ok) {
        r <$ dr;
        ok <- r < k16;
        Trials.outs <- rcons Trials.outs ok;
      }
      i <- i + 1;
    }
    Gen.e <$ dtrial (0, true, (RSE.FunRO.f, RTE.FunRO.f, Trials.q));
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPSTO(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    return b;
  }
}.

(* Without disagreement, a passing selected trial also passes with p_U, so U is not empty. *)
lemma cc_inv (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC}) :
  hoare [CC(D).main : !real ==>
         (!CC.bad /\ lastpass SvO.i Trials.outs) => 0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q].
proof.
proc.
call (_ : true); 1..6: by proc; inline *; auto.
call (_ : true ==> true); 1: by proc; auto.
call (_ : true ==> true); 1: by proc; while true; [inline *; auto | auto].
call (_ : true ==> true); 1: by proc; auto.
seq 13 : (!real /\ (!CC.bad => forall j, 0 <= j < size Trials.outs => nth false Trials.outs j =>
                     0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q)); last first.
- by sp; if; auto => />; smt().
while (!real /\ (!CC.bad => forall j, 0 <= j < size Trials.outs => nth false Trials.outs j =>
                    0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q)).
- wp; if; 2: by auto.
  auto => /> &hr hreal hinv _ _ rv hrv hnb j hj0; rewrite size_rcons nth_rcons => hj1.
  case: (j < size Trials.outs{hr}) => hjs.
  + by apply (hinv _ j); smt().
  move=> hl; move: hrv; rewrite supp_dinter; smt().
by inline *; auto => />; smt(size_ge0).
qed.

lemma cc_cf (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                         -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[CC(D).main(false) @ &m : res /\ !CC.bad] <=
  Pr[CF(D).main() @ &m : res /\ 0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q] +
  Pr[CC(D).main(false) @ &m : !lastpass SvO.i Trials.outs].
proof.
move=> Dll.
have h1 : Pr[CC(D).main(false) @ &m : res /\ !CC.bad] <=
          Pr[CC(D).main(false) @ &m : (res /\ lastpass SvO.i Trials.outs /\
                                        0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q) \/
                                       !lastpass SvO.i Trials.outs].
- byequiv (_ : ={glob D, real} /\ !real{1} ==>
               ={res, CC.bad, SvO.i, Trials.outs, RSE.FunRO.f, RTE.FunRO.f, Trials.q} /\
               ((!CC.bad /\ lastpass SvO.i Trials.outs) =>
                0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q){1}) => //; 2: smt().
  by conseq (_ : ={glob D, real} ==> ={res, CC.bad, SvO.i, Trials.outs, RSE.FunRO.f, RTE.FunRO.f, Trials.q})
            (cc_inv D) _ => //; sim.
have h2 : Pr[CC(D).main(false) @ &m : (res /\ lastpass SvO.i Trials.outs /\
                                       0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q) \/
                                      !lastpass SvO.i Trials.outs] <=
          Pr[CC(D).main(false) @ &m : res /\ lastpass SvO.i Trials.outs /\
                                      0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q] +
          Pr[CC(D).main(false) @ &m : !lastpass SvO.i Trials.outs].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have h3 : Pr[CC(D).main(false) @ &m : res /\ lastpass SvO.i Trials.outs /\
                                      0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q] <=
          Pr[CF(D).main() @ &m : res /\ 0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q].
- byequiv (_ : ={glob D} /\ !real{1} ==>
               (lastpass SvO.i Trials.outs){1} =>
               ={res, RSE.FunRO.f, RTE.FunRO.f, Trials.q}) => //; 2: smt().
  proc.
  seq 13 11 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs} /\
               (SvO.i{1} = size Trials.outs{1} - 1) /\ size Trials.outs{1} <= ntr).
  + while (={i, ok, glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q,
             Trials.outs} /\ !real{1} /\ SvO.i{1} = size Trials.outs{1} - 1 /\
           (!ok{1} => size Trials.outs{1} = i{1} + 1) /\
           size Trials.outs{1} <= i{1} + 1 /\ -1 <= i{1} /\ i{1} + 1 <= ntr).
    * by wp; if => //; auto => />; smt(size_rcons).
    by inline *; auto => />; smt(ntr_gt0).
  case ((lastpass SvO.i Trials.outs){1}).
  + rcondt{1} 2; 1: by auto => /> /#.
    call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
    call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
    call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
    call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
    by wp; rnd; wp; skip => /> &1 &2 _ _ [_ h]; rewrite h (dtrial_index _ 0).
  wp; call{1} Dll; call{2} Dll; call{1} rw_get_ll; call{2} rw_get_ll; call{1} enc_llO; call{2} enc_llO.
  call{1} (_ : true ==> true); 1: by proc; auto.
  call{2} (_ : true ==> true); 1: by proc; auto.
  by rnd{2}; sp; if{1}; [rnd{1} |]; auto => />; smt(dtrial_ll).
smt().
qed.

(* ---- Every trial of the run with 2^-16 fails: probability (1 - 2^-16)^(2^80) --------------- *)
module FL = {
  proc main() : unit = {
    var ok, i, r;
    Trials.outs <- []; ok <- false; i <- -1; SvO.i <- -1;
    while (i + 1 < ntr) {
      if (!ok) {
        r <$ dr;
        ok <- r < k16;
        Trials.outs <- rcons Trials.outs ok;
        SvO.i <- i + 1;
      }
      i <- i + 1;
    }
  }
}.

lemma cc_fl (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                         -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[CC(D).main(false) @ &m : !lastpass SvO.i Trials.outs] = Pr[FL.main() @ &m : !lastpass SvO.i Trials.outs].
proof.
move=> Dll; byequiv (_ : !real{1} ==> ={SvO.i, Trials.outs}) => //; proc.
wp; call{1} Dll; call{1} rw_get_ll; call{1} enc_llO; call{1} (_ : true ==> true); 1: by proc; auto.
seq 13 5 : (={SvO.i, Trials.outs}).
- while (={i, ok, Trials.outs, SvO.i} /\ !real{1}).
  + by wp; if => //; auto => />.
  have hS : is_lossless dfS by exact dfS_ll.
  have hT : is_lossless dfT by exact dfT_ll.
  by inline *; wp; rnd{1}; rnd{1}; rnd{1}; rnd{1}; skip => />; smt(dP_ll dQ_ll).
by sp; if{1}; [rnd{1} |]; auto => />; smt(dtrial_ll).
qed.

op phiF (ok : bool) (i : int) : real = if ok then 0%r else (1%r - p16) ^ (ntr - (i + 1)).

lemma fl_e : ehoare [FL.main : (phiF false (-1))%xr ==> (!lastpass SvO.i Trials.outs)%xr].
proof.
proc.
while ((-1 <= i /\ i + 1 <= ntr /\ (i = -1 => !ok) /\ (!ok => size Trials.outs = i + 1) /\
        (0 <= i => SvO.i = size Trials.outs - 1 /\ 1 <= size Trials.outs /\
                   nth false Trials.outs SvO.i = ok)) `|` (phiF ok i)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[hi [hn [h1 [h3 h2]]]].
  apply xr_ble; rewrite /phiF /lastpass.
  have hi0 : 0 <= i{hr} by smt(ntr_gt0).
  case: (ok{hr}) => hok /=; 1: smt().
  rewrite (_ : ntr - (i{hr} + 1) = 0) 1:/# RField.expr0.
  by case: (0 <= SvO.i{hr} < size Trials.outs{hr} /\ nth false Trials.outs{hr} SvO.i{hr}).
- auto => &hr /=; apply xle_cxr_r => -[hc [hi [hn [h1 [h3 h2]]]]].
  case: (ok{hr}) => hok /=.
  + by apply xle_cxr_l; [smt() | rewrite /phiF].
  pose C := (1%r - p16) ^ (ntr - (i{hr} + 2)).
  have hp : 0%r <= p16 <= 1%r by rewrite /p16; smt(RealOrder.expr_gt0 RealOrder.invr_le1 RealOrder.exprn_ege1).
  have hC : 0%r <= C by apply expr_ge0; smt().
  apply (xle_trans (Ep dr (fun r0 => (C * b2r (!(r0 < k16)))%xr))).
  + apply le_Ep => r0 _ /=; apply xle_cxr_l.
    * by rewrite size_rcons nth_rcons /=; smt().
    by rewrite /phiF; case: (r0 < k16) => /=; smt().
  rewrite Ep_xr 1:dr_fin => [r0 /= |]; 1: smt(b2r_ge0).
  apply xr_le; rewrite expZ exp_b2r (mu_eq _ _ (predC (fun r0 => r0 < k16))) 1:/# mu_not dr_ll.
  rewrite dr_lt 1:k16_bound -p16_k16 /phiF /= (_ : ntr - (i{hr} + 1) = ntr - (i{hr} + 2) + 1) 1:/#.
  by rewrite RField.exprS; smt(ntr_gt0).
by auto => &hr /=; apply xle_cxr_l => //; smt(ntr_gt0).
qed.

lemma fl_cut &m : Pr[FL.main() @ &m : !lastpass SvO.i Trials.outs] <= inv (2%r ^ 256).
proof.
have hp : 0%r <= p16 <= 1%r by rewrite /p16; smt(RealOrder.expr_gt0 RealOrder.invr_le1 RealOrder.exprn_ege1).
have h0 : 0%r <= phiF false (-1) by rewrite /phiF /=; apply expr_ge0; smt().
have h1 : Pr[FL.main() @ &m : !lastpass SvO.i Trials.outs] <= phiF false (-1).
- by byehoare (_ : (phiF false (-1))%xr ==> _) => //; exact fl_e.
apply (ler_trans _ _ _ h1); rewrite /phiF /=.
apply (ler_trans ((1%r - inv (2%r ^ 17)) ^ ntr)); 2: exact pcut17.
apply ler_pexp; 1: smt(ntr_gt0).
split; 1: smt().
move=> _; rewrite /p16; apply ler_sub => //; apply lef_pinv; smt(RealOrder.expr_gt0 RealOrder.ler_weexpn2l).
qed.

(* ---- The reduction runs the trials with 2^-16 itself ------------------------------------------- *)
module TF = { var outs : bool list }.

module CB (D : CONTO) (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed, outs : bool list) : bool = {
    var ok, i, r, b;
    TF.outs <- []; ok <- false; i <- -1;
    while (i + 1 < ntr) {
      if (!ok) {
        r <$ dr;
        ok <- r < k16;
        TF.outs <- rcons TF.outs ok;
      }
      i <- i + 1;
    }
    b <@ D(O).run(y, om, p, q, e, sd, TF.outs);
    return b;
  }
}.

(* The generation with the selected value drawn uniformly from the passing values. *)
module PreB (D : CONTO) = {
  proc main() : bool = {
    var y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q;
    Gen.e <$ dtrial (0, true, (RSE.FunRO.f, RTE.FunRO.f, Trials.q));
    Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
    y <@ Net(Ideal).enc(Gen.p, Gen.e);
    om <@ RW.RO.get(Gen.sd);
    b <@ D(IPSTO(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, []);
    return b;
  }
}.

lemma cf_preb (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                           -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC, -TF}) &m :
  Pr[CF(D).main() @ &m : res /\ 0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q] =
  Pr[PreB(CB(D)).main() @ &m : res /\ 0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q].
proof.
byequiv (_ : ={glob D} ==> ={res, RSE.FunRO.f, RTE.FunRO.f, Trials.q}) => //; proc.
inline CB(D, IPSTO(RSE.FunRO, RTE.FunRO)).run.
swap{1} [8 .. 11] 4; swap{1} [1 .. 2] 4; swap{1} 1 1.
wp; call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
while (={i, ok, glob D, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f, Trials.q, Gen.p, Gen.q, Gen.e, Gen.sd} /\
       Trials.outs{1} = TF.outs{2} /\ y{1} = y0{2} /\ om{1} = om0{2} /\ p{2} = Gen.p{2} /\
       q{2} = Gen.q{2} /\ e{2} = Gen.e{2} /\ sd{2} = Gen.sd{2}).
- by wp; if => //; auto.
wp; call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
by rnd; inline *; auto.
qed.

(* ---- The target game: the generation by SeqU and the reduction's own trials ------------------- *)
module KB (D : CONTO) = {
  proc main() : bool = {
    var b, ok;
    b <@ PreB(CB(D)).main();
    Trials.outs <- [];
    TBO.p <- mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q);
    SvO.i <@ SeqU(Rec(TBO)).select();
    ok <- lastpass SvO.i Trials.outs;
    return b /\ ok;
  }
}.

lemma seqU_pass : hoare [SeqU(Rec(TBO)).select : Trials.outs = [] ==> lastpass res Trials.outs].
proof. by conseq (SeqU_pass TBO). qed.

lemma seqU0 : hoare [SeqU(Rec(TBO)).select : TBO.p = 0%r ==> false].
proof.
proc; while (TBO.p = 0%r /\ !ok).
- by inline *; auto => /> &hr _ b; rewrite Biased.dbiased0 supp_dunit.
by auto => />.
qed.

lemma seqU_cov (p0 : real) :
  phoare [SeqU(Rec(TBO)).select : TBO.p = p0 /\ Trials.outs = [] /\ 0%r < p0 <= 1%r ==>
          lastpass res Trials.outs] = 1%r.
proof.
case (0%r < p0 <= 1%r) => hp; 2: by exfalso; smt().
conseq (_ : TBO.p = p0 ==> true) seqU_pass => //.
apply (SeqU_ll (Rec(TBO)) (fun (g : glob Rec(TBO)) => g.`2 = p0) p0) => //; 1: smt().
- proc; inline TBO.trial; wp; rnd (fun b => b); auto => />.
  by rewrite Biased.dbiasedE /= Biased.clamp_id /#.
by proc; inline TBO.trial; auto => />; exact Biased.dbiased_ll.
qed.

lemma cb_ll (D <: CONTO {-TF}) :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run => islossless CB(D, IPSTO(RSE.FunRO, RTE.FunRO)).run.
proof.
move=> Dll; proc; call Dll.
while true (ntr - i); 2: by auto => /#.
by move=> z; wp; if; auto => />; smt(dr_ll).
qed.

lemma fro_kb (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC, -TF}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[FRO(SeqU, CB(D)).main() @ &m : res /\ lastpass SvO.i Trials.outs] = Pr[KB(D).main() @ &m : res].
proof.
move=> Dll; have Cll := cb_ll D Dll.
byequiv (_ : ={glob D} ==> (res{1} /\ lastpass SvO.i{1} Trials.outs{1}) = res{2}) => //; proc.
inline PreB(CB(D)).main.
swap{2} [14 .. 16] -6.
seq 10 10 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs,
               SvO.i}).
- call (_ : ={TBO.p, Trials.outs}); 1: by sim.
  by inline *; auto.
case ((lastpass SvO.i Trials.outs){1}).
- rcondt{1} 2; 1: by auto => /> /#.
  wp; call (_ : ={y, om, p, q, e, sd, glob D, R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f} ==> ={res}).
  + by proc; sim.
  call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
  call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
  call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
  by wp; rnd; wp; skip => /> &1 &2 [_ h]; rewrite h (dtrial_index _ 0).
wp; call{1} Cll; call{2} Cll; call{1} rw_get_ll; call{2} rw_get_ll; call{1} enc_llO; call{2} enc_llO.
call{1} (_ : true ==> true); 1: by proc; auto.
call{2} (_ : true ==> true); 1: by proc; auto.
by rnd{2}; sp; if{1}; [rnd{1} |]; auto => />; smt(dtrial_ll).
qed.

lemma kb_pre (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC, -TF}) &m :
  Pr[KB(D).main() @ &m : res] =
  Pr[PreB(CB(D)).main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)].
proof.
byphoare (_ : (glob KB(D)) = (glob KB(D)){m} ==> res) => //; proc.
seq 1 : (b /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q))
  (Pr[PreB(CB(D)).main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)]) 1%r
  (Pr[PreB(CB(D)).main() @ &m : !(res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q))]) 0%r => //.
- call (_ : (glob PreB(CB(D))) = (glob PreB(CB(D))){m} ==>
            res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)).
  + bypr => &m0; split => [| h]; 1: smt(mu_bounded).
    by byequiv (_ : ={glob PreB(CB(D))} ==> ={res, RSE.FunRO.f, RTE.FunRO.f, Trials.q}) => //; sim.
  by auto.
- wp; exlim (mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)) => p0.
  by call (seqU_cov p0); auto => />; smt(le1_mu).
hoare; wp; case b.
- by call seqU0; auto => />; smt(ge0_mu).
by call (_ : true ==> true); [proc; while true; [inline *; auto | auto] | auto => />].
qed.

lemma fro_last (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                            -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC, -TF}) &m :
  Pr[FRO(SeqU, CB(D)).main() @ &m : res] = Pr[FRO(SeqU, CB(D)).main() @ &m : res /\ lastpass SvO.i Trials.outs].
proof.
have hl : hoare [FRO(SeqU, CB(D)).main : true ==> lastpass SvO.i Trials.outs]; last first.
- byequiv (_ : ={glob D} ==> ={res} /\ lastpass SvO.i{1} Trials.outs{1} /\
               lastpass SvO.i{2} Trials.outs{2}) => //.
  by conseq (_ : ={glob D} ==> ={res}) hl hl => //; sim.
proc; inline CB(D, IPSTO(RSE.FunRO, RTE.FunRO)).run.
wp; call (_ : true); 1..6: by proc; inline *; auto.
while true; 1: by wp; if; auto.
wp; call (_ : true ==> true); 1: by proc; auto.
call (_ : true ==> true); 1: by proc; while true; [inline *; auto | auto].
call (_ : true ==> true); 1: by proc; auto.
seq 10 : (lastpass SvO.i Trials.outs); 2: by sp; if; auto.
by call seqU_pass; inline *; auto.
qed.

(* The fake side: what the run with 2^-16 gives, without disagreement, is the target game. *)
lemma fake_side (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                             -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC, -TF, -VVO.RO, -VVO.FRO}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[CC(D).main(false) @ &m : res /\ !CC.bad] <=
  Pr[GenGameO(Setup0P(SeqU), CB(D)).main() @ &m : res] + inv (2%r ^ 256).
proof.
move=> Dll.
have h1 := cc_cf D &m Dll.
have h2 := cc_fl D &m Dll.
have h3 := fl_cut &m.
have h4 := cf_preb D &m.
have h5 : Pr[PreB(CB(D)).main() @ &m : res /\ 0 < kU RSE.FunRO.f RTE.FunRO.f Trials.q] =
          Pr[PreB(CB(D)).main() @ &m : res /\ 0%r < mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q)].
- rewrite Pr[mu_eq] => // &hr; rewrite pU_kU; smt(RealOrder.expr_gt0 RealOrder.divr_gt0 lt_fromint).
have h6 := kb_pre D &m.
have h7 := fro_kb D &m Dll.
have h8 := fro_last D &m.
have h9 := chainO SeqU (CB(D)) (fun b _ => b) &m.
smt().
qed.

(* The cut sequential rule revealing its outcomes against the target game. *)
lemma seq_disclosure (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                                  -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC, -TF, -VVO.RO, -VVO.FRO}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[GenGameO(Setup0P(Seq), D).main() @ &m : res] <=
  Pr[GenGameO(Setup0P(SeqU), CB(D)).main() @ &m : res] + (inv (2%r ^ 120) - inv (2%r ^ 138)) +
  inv (2%r ^ 256).
proof.
move=> Dll.
have h1 := chainO Seq D (fun b _ => b) &m.
have h2 := fro_r D (fun b _ => b) &m.
have h3 := fror_cc D (fun b _ => b) &m.
have h4 := cc_upto D (fun b _ => b) &m Dll.
have h5 := cc_bad D &m Dll.
have h6 := fake_side D &m Dll.
move: h1 h2 h3 h4 h5 h6 => /= h1 h2 h3 h4 h5 h6.
smt().
qed.

(* ---- The uncut sequential rule against the cut one ---- *)
module HV = { var ok, c : bool  var i : int }.

(* The first ntr trials, then the rest of the game only if one of them passed. *)
module H3 (D : CONTO) = {
  proc main() : bool = {
    var y, om, b;
    RTE.FunRO.init(); RSE.FunRO.init(); R.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    Trials.q <- Gen.q; Trials.outs <- [];
    TBO.p <- mu dstate (pass RSE.FunRO.f RTE.FunRO.f Trials.q);
    HV.ok <- false; HV.i <- -1;
    while (!HV.ok /\ HV.i + 1 < ntr) { HV.ok <@ Rec(TBO).trial(); HV.i <- HV.i + 1; }
    HV.c <- !HV.ok;
    b <- false;
    if (!HV.c) {
      SvO.i <- HV.i;
      Gen.e <- witness;
      if (0 <= SvO.i < size Trials.outs) {
        Gen.e <$ dtrial (SvO.i, nth false Trials.outs SvO.i, (RSE.FunRO.f, RTE.FunRO.f, Trials.q));
      }
      Gen.sd <@ RSE.FunRO.get(Gen.e, Gen.q);
      y <@ Net(Ideal).enc(Gen.p, Gen.e);
      om <@ RW.RO.get(Gen.sd);
      b <@ D(IPSTO(RSE.FunRO, RTE.FunRO)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs);
    }
    return b;
  }
}.

(* The same, with the remaining trials of the uncut rule at the very end. *)
module H2 (D : CONTO) = {
  proc main() : bool = {
    var b;
    b <@ H3(D).main();
    while (!HV.ok) { HV.ok <@ Rec(TBO).trial(); HV.i <- HV.i + 1; }
    return b;
  }
}.

lemma h1_h2 (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                         -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -HV}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[FRO(SeqU, D).main() @ &m : res] <= Pr[H2(D).main() @ &m : res \/ HV.c].
proof.
move=> Dll.
byequiv (_ : ={glob D} ==> !HV.c{2} => ={res}) => //; 2: smt().
proc; inline SeqU(Rec(TBO)).select H3(D).main.
splitwhile{1} 12 : (i + 1 < ntr).
seq 12 12 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs, TBO.p} /\
             ok{1} = HV.ok{2} /\ i{1} = HV.i{2}).
- while (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs, TBO.p} /\
         ok{1} = HV.ok{2} /\ i{1} = HV.i{2}).
  + by wp; call (_ : ={Trials.outs, TBO.p}); [sim | auto].
  by inline *; auto.
case (HV.ok{2}).
- rcondf{1} 1; 1: by auto.
  while{2} (HV.ok{2}) 0; 1: by move=> &1 z; exfalso; smt().
  rcondt{2} 3; 1: by auto.
  wp; call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
  call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
  call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
  call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
  by sp; if => //; auto => />.
rcondf{2} 3; 1: by auto.
seq 0 3 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs, TBO.p} /\
           ok{1} = HV.ok{2} /\ i{1} = HV.i{2} /\ HV.c{2}).
- by auto.
seq 1 1 : (HV.c{2}).
- while (={Trials.outs, TBO.p} /\ ok{1} = HV.ok{2} /\ i{1} = HV.i{2} /\ HV.c{2}).
  + by wp; call (_ : ={Trials.outs, TBO.p}); [sim | auto].
  by auto.
wp; call{1} Dll; call{1} rw_get_ll; call{1} enc_llO; call{1} (_ : true ==> true); 1: by proc; auto.
by sp; if{1}; [rnd{1} |]; auto => />; smt(dtrial_ll).
qed.

(* Dropping the trailing trials can only raise the probability of an event they do not change. *)
lemma h2_h3 (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                         -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -HV}) &m :
  Pr[H2(D).main() @ &m : res \/ HV.c] <= Pr[H3(D).main() @ &m : res \/ HV.c].
proof.
byphoare (_ : (glob H2(D)) = (glob H2(D)){m} ==> res \/ HV.c) => //; proc.
seq 1 : (b \/ HV.c) (Pr[H3(D).main() @ &m : res \/ HV.c]) 1%r
                    (Pr[H3(D).main() @ &m : !(res \/ HV.c)]) 0%r => //.
- call (_ : (glob H3(D)) = (glob H3(D)){m} ==> res \/ HV.c).
  + bypr => &m0; split => [| h]; 1: smt(mu_bounded).
    by byequiv (_ : ={glob H3(D)} ==> ={res, HV.c}) => //; sim.
  by auto.
hoare; while (!(b \/ HV.c)); 1: by wp; call (_ : true); auto.
by auto.
qed.

lemma h3_seq (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -HV}) &m :
  islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[H3(D).main() @ &m : res \/ HV.c] <=
  Pr[FRO(Seq, D).main() @ &m : res] + Pr[FRO(Seq, D).main() @ &m : !last false Trials.outs].
proof.
move=> Dll.
have h : Pr[H3(D).main() @ &m : res \/ HV.c] <=
         Pr[FRO(Seq, D).main() @ &m : res \/ !last false Trials.outs].
- byequiv (_ : ={glob D} ==> (HV.c{1} => !last false Trials.outs{2}) /\ (res{1} => res{2})) => //; 2: smt().
  proc; inline Seq(Rec(TBO)).select.
  seq 12 12 : (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs, TBO.p} /\
               HV.ok{1} = ok{2} /\ HV.i{1} = i{2} /\ ok{2} = last false Trials.outs{2}).
  + while (={glob D, Gen.p, Gen.q, RSE.FunRO.f, RTE.FunRO.f, R.RO.m, RW.RO.m, Trials.q, Trials.outs, TBO.p} /\
           HV.ok{1} = ok{2} /\ HV.i{1} = i{2} /\ ok{2} = last false Trials.outs{2}).
    * by inline *; wp; rnd; auto => />; smt(last_rcons).
    by inline *; auto.
  case (HV.ok{1}).
  + rcondt{1} 3; 1: by auto.
    wp; call (_ : ={R.RO.m, RW.RO.m, RSE.FunRO.f, RTE.FunRO.f}); 1..6: by sim.
    call (_ : ={arg, RW.RO.m} ==> ={res, RW.RO.m}); 1: by sim.
    call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by sim.
    call (_ : ={arg, RSE.FunRO.f} ==> ={res, RSE.FunRO.f}); 1: by sim.
    by sp; if => //; auto => />.
  rcondf{1} 3; 1: by auto.
  wp; call{2} Dll; call{2} rw_get_ll; call{2} enc_llO; call{2} (_ : true ==> true); 1: by proc; auto.
  by sp; if{2}; [rnd{2} |]; auto => />; smt(dtrial_ll).
have : Pr[FRO(Seq, D).main() @ &m : res \/ !last false Trials.outs] <=
       Pr[FRO(Seq, D).main() @ &m : res] + Pr[FRO(Seq, D).main() @ &m : !last false Trials.outs].
- by rewrite Pr[mu_or]; smt(mu_bounded).
smt().
qed.

(* The cutoff of the cut rule, seen at the end of a game that only adds a lossless continuation. *)
lemma cut_genO (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                            -RTE.FunRO, -RW.RO, -Trials, -Gen}) &m :
  islossless D(IP).run =>
  Pr[GenGameO(Setup0P(Seq), D).main() @ &m : !last false Trials.outs] =
  Pr[Setup0P(Seq).run() @ &m : !last false Trials.outs].
proof.
move=> Dll; byequiv => //; proc*; inline GenGameO(Setup0P(Seq), D).main; wp.
call{1} Dll.
by wp; call (_ : true ==> ={res, Trials.outs}); [sim | auto].
qed.

(* The uncut sequential rule against the cut one: they differ only when 2^80 trials fail. *)
lemma uncut (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                         -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -HV, -VVO.RO, -VVO.FRO}) &m :
  islossless D(IP).run => islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[GenGameO(Setup0P(SeqU), D).main() @ &m : res] <=
  Pr[GenGameO(Setup0P(Seq), D).main() @ &m : res] + inv (2%r ^ 256).
proof.
move=> Dll1 Dll2.
have c1 := chainO SeqU D (fun b _ => b) &m.
have c2 := chainO Seq D (fun b _ => b) &m.
have c3 := chainO Seq D (fun _ outs => !last false outs) &m.
have g := cut_genO D &m Dll1.
have k := seq_cutoff &m.
have a := h1_h2 D &m Dll2.
have b := h2_h3 D &m.
have c := h3_seq D &m Dll2.
move: c1 c2 c3 => /= c1 c2 c3.
smt().
qed.
