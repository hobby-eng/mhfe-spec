(* Theorem 5 and Corollary W5 when the generation reveals the pass/fail outcomes of its trials,
   their number and a duration that depends only on these: the bounds hold with 2^-120 added for
   the sequential rule (DESIGN-NOTES A.6, "The number of trials"). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal DInterval RealSeries Finite.
require import Suite3 Chain Collision Passphrase Generation Selection Theta2 Theorem5 W5W6.
require import PassRate TrialGames TrialCoupling TrialFake.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* The sequential rule of the specification, revealing its outcomes, against the target game. *)
lemma seqU_disclosure (D <: CONTO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                                   -RTE.FunRO, -RW.RO, -Trials, -Gen, -TBO, -SvO, -CC, -TF, -HV,
                                   -VVO.RO, -VVO.FRO}) &m :
  islossless D(IP).run => islossless D(IPSTO(RSE.FunRO, RTE.FunRO)).run =>
  Pr[GenGameO(Setup0P(SeqU), D).main() @ &m : res] <=
  Pr[GenGameO(Setup0P(SeqU), CB(D)).main() @ &m : res] + inv (2%r ^ 120).
proof.
move=> Dll1 Dll2.
have h1 := uncut D &m Dll1 Dll2.
have h2 := seq_disclosure D &m Dll2.
have h3 : 2%r * inv (2%r ^ 256) <= inv (2%r ^ 138).
- have e : 2%r * inv (2%r ^ 256) = inv (2%r ^ 138) * inv (2%r ^ 117).
  + rewrite (_ : 256 = 138 + 117 + 1) // !RField.exprD_nneg // RField.expr1.
    by field; smt(RealOrder.expr_gt0).
  have f : inv (2%r ^ 117) <= 1%r.
  + have g : 1%r <= 2%r ^ 117 by apply RealOrder.exprn_ege1.
    by rewrite RealOrder.invr_le1 //; smt(RealOrder.expr_gt0).
  rewrite e; have := RealOrder.expr_gt0 138 2%r _; 1: done.
  move=> h; apply (ler_trans (inv (2%r ^ 138) * 1%r)); 2: smt().
  by apply ler_wpmul2l => //; smt(RealOrder.invr_gt0).
smt().
qed.

(* ---- The games ---------------------------------------------------------------------------------- *)
(* The adversary also receives the outcomes of the owner's trials. *)
module type AdvPO (O : OraclesP) = {
  proc guess(y : state, om : data, outs : bool list) : seed * (pw * pp)
}.

module GamePRO (S : SETUPP) (A : AdvPO) (Rf : AFTERP) = {
  proc main() : seed * (pw * pp) = {
    var y, om, out;
    (y, om) <@ S.run();
    if (y = Gen.e) {
      out <@ Rf.run(Gen.p, Gen.q, y);
    } else {
      CountP(IP).init();
      out <@ A(CountP(IP)).guess(y, om, Trials.outs);
    }
    return out;
  }
}.

(* The reduction: it runs the cut sequential rule on outcomes r < 2^240 of a uniform r itself. *)
module BO (A : AdvPO) (O : OraclesP) = {
  proc guess(y : state, om : data) : seed * (pw * pp) = {
    var ok, i, r, out;
    TF.outs <- []; ok <- false; i <- -1;
    while (i + 1 < ntr) {
      if (!ok) {
        r <$ dr;
        ok <- r < k16;
        TF.outs <- rcons TF.outs ok;
      }
      i <- i + 1;
    }
    out <@ A(O).guess(y, om, TF.outs);
    return out;
  }
}.

(* ---- Responses after a refusal that always win ------------------------------------------------- *)
(* After a refused first attempt the container is the entropy itself, from which these responses
   give the seed, the pair or the phrase. Any other response wins at most as often, so the trials
   theorems hold for every response that Theorem 5 and Corollary W5 allow. *)
module RwSeed : AFTERP = {
  proc run(p : pw, q : pp, y : state) : seed * (pw * pp) = {
    var sd;
    sd <@ RS.RO.get(y, q);
    return (sd, (p, q));
  }
}.

module RwPair : AFTERP = {
  proc run(p : pw, q : pp, y : state) : seed * (pw * pp) = { return (witness, (p, q)); }
}.

lemma RwSeed_ll : islossless RwSeed.run.
proof. by proc; call rs_get_ll; auto. qed.

lemma RwSeed_win : hoare [RwSeed.run : y = Gen.e /\ p = Gen.p /\ q = Gen.q /\
  RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd ==> res.`1 = Gen.sd].
proof. by proc; inline *; auto => />; smt(domE). qed.

lemma RwPair_ll : islossless RwPair.run.
proof. by proc; auto. qed.

lemma RwPair_win : hoare [RwPair.run : y = Gen.e /\ p = Gen.p /\ q = Gen.q /\
  RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd ==> res.`2 = (Gen.p, Gen.q)].
proof. by proc; auto. qed.

(* After the generation the seed function stores the selected seed. *)
lemma setup_seed : hoare [Setup0P(SeqU).run : true ==> RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd].
proof.
proc; call (_ : true ==> true); 1: by trivial.
call (_ : true ==> true); 1: by trivial.
inline RS.RO.get; wp; rnd; wp.
conseq (_ : true ==> true) => //.
by move=> /> *; smt(domE get_set_sameE).
qed.

section DiscGame.
declare op Ev : seed * (pw * pp) -> pw -> pp -> seed -> bool.
declare module A <: AdvPO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                           -RTE.FunRO, -RW.RO, -Gen, -Trials, -Count, -CountP, -TBO, -SvO, -CC, -TF, -HV,
                           -VVO.RO, -VVO.FRO}.
declare module Rf <: AFTERP {-Gen}.
declare axiom Rf_ll : islossless Rf.run.
declare module Rw <: AFTERP {-Gen}.
declare axiom Rw_ll : islossless Rw.run.
declare axiom Rw_win : hoare [Rw.run : y = Gen.e /\ p = Gen.p /\ q = Gen.q /\
  RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd ==> Ev res Gen.p Gen.q Gen.sd].
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

(* The continuation wins on a refused first attempt and otherwise runs the adversary. *)
local module CW (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed, outs : bool list) : bool = {
    var out, b;
    b <- true;
    if (y <> e) {
      CountP(O).init();
      out <@ A(CountP(O)).guess(y, om, outs);
      b <- Ev out p q sd;
    }
    return b;
  }
}.

local lemma CW_ll (O <: OraclesP {-CW}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless CW(O).run.
proof.
move=> ha hb hh hs ht hw; proc; sp; if => //; wp.
call (A_ll (CountP(O)) _ _ _ _ _ _); 1..6: by proc; inline *; wp; (call ha || call hb || call hh ||
  call hs || call ht || call hw); auto.
by inline *; auto.
qed.

local lemma CW_ll_IP : islossless CW(IP).run.
proof. by apply (CW_ll IP); proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll). qed.

local lemma CW_ll_ST : islossless CW(IPSTO(RSE.FunRO, RTE.FunRO)).run.
proof. by apply (CW_ll (IPSTO(RSE.FunRO, RTE.FunRO))); proc; inline *; auto => />; smt(dans_ll ddata_ll). qed.

lemma disc_game &m :
  Pr[GamePRO(Setup0P(SeqU), A, Rf).main() @ &m : Ev res Gen.p Gen.q Gen.sd] <=
  Pr[GamePR(Setup0P(SeqU), BO(A), Rw).main() @ &m : Ev res Gen.p Gen.q Gen.sd] + inv (2%r ^ 120).
proof.
have h1 : Pr[GamePRO(Setup0P(SeqU), A, Rf).main() @ &m : Ev res Gen.p Gen.q Gen.sd] <=
          Pr[GenGameO(Setup0P(SeqU), CW).main() @ &m : res].
- byequiv => //; proc; inline CW(IP).run; wp.
  seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs, R.RO.m, RS.RO.m, RT.RO.m,
               RW.RO.m}); 1: by sim.
  sp; if{1}.
  + rcondf{2} 1; 1: by auto => /#.
    by wp; call{1} Rf_ll; auto.
  rcondt{2} 1; 1: by auto => /#.
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
              CountP.cw}); 1..6: by sim.
  by inline *; auto => /> /#.
have h2 := seqU_disclosure CW &m CW_ll_IP CW_ll_ST.
have h3 : Pr[GenGameO(Setup0P(SeqU), CB(CW)).main() @ &m : res] <=
          Pr[GamePR(Setup0P(SeqU), BO(A), Rw).main() @ &m : Ev res Gen.p Gen.q Gen.sd].
- byequiv => //; proc; inline CB(CW, IP).run CW(IP).run.
  seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m} /\
             RS.RO.m{2}.[(Gen.e{2}, Gen.q{2})] = Some Gen.sd{2}).
  + conseq (_ : _ ==> ={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m})
      _ (_ : _ ==> RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd) => //.
    * by call setup_seed.
    by sim => /#.
  case (y{1} = Gen.e{1}).
  + rcondf{1} 20; 1: by move=> &2; wp; while true; [wp; if; auto | auto].
    rcondt{2} 1; 1: by auto.
    have Rw_one : phoare [Rw.run : y = Gen.e /\ p = Gen.p /\ q = Gen.q /\
                    RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd ==> Ev res Gen.p Gen.q Gen.sd] = 1%r.
    * by conseq Rw_ll Rw_win.
    wp; call{2} Rw_one; wp.
    while{1} true (ntr - i{1}); 1: by move=> &2 z; wp; if; auto => />; smt(dr_ll).
    by auto => /#.
  rcondt{1} 20; 1: by move=> &2; wp; while true; [wp; if; auto | auto].
  rcondf{2} 1; 1: by auto.
  inline BO(A, CountP(IP)).guess.
  swap{2} 1 6.
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
              CountP.cw}); 1..6: by sim.
  call (_ : true ==> ={Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}).
  + by proc; inline *; auto.
  wp; while (={i, ok, TF.outs}); 1: by wp; if => //; auto.
  by auto => />.
smt().
qed.
end section DiscGame.

(* ---- Theorem 5 when the generation reveals its outcomes ----------------------------------------- *)
section DiscT5.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op kS : int.
declare op qT : int.
declare op qW : int.
declare module A <: AdvPO {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                           -RTE.FunRO, -RW.RO, -Gen, -Trials, -Count, -CountB, -CountP, -Mon, -Bwd,
                           -WithP, -AP, -TBO, -SvO, -CC, -TF, -HV, -VVO.RO, -VVO.FRO}.
declare module Rf <: AFTERP {-Gen}.
declare axiom Rf_ll : islossless Rf.run.
declare axiom A_bounded (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW].
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

(* The reduction makes the adversary's queries and no other. *)
local lemma BO_bounded (O <: OraclesP {-Count, -CountP, -BO(A)}) :
  hoare [BO(A, CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW].
proof.
proc; call (A_bounded O).
by while (Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0);
  [wp; if; auto | auto].
qed.

local lemma BO_ll (O <: OraclesP {-BO(A)}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless BO(A, O).guess.
proof.
move=> ha hb hh hs ht hw; proc; call (A_ll O ha hb hh hs ht hw).
while true (ntr - i); 2: by auto => /#.
by move=> z; wp; if; auto => />; smt(dr_ll).
qed.

(* Theorem 5 (a) with the outcomes, their number and a duration that depends only on these revealed:
   the bound of Theorem 5 plus 2^-120 (2^-136 n with n = 2^16 for the sequential rule). *)
lemma theorem5_seed_trials &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GamePRO(Setup0P(SeqU), A, Rf).main() @ &m : res.`1 = Gen.sd] <=
    top2 (kA %/ 12) kS + epsW kA kS qB qH qT qW + inv (2%r ^ 512) + inv (2%r ^ 120).
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := disc_game (fun (out : seed * (pw * pp)) _ _ (sd : seed) => out.`1 = sd) A Rf Rf_ll
             RwSeed RwSeed_ll RwSeed_win A_ll &m.
have h2 := theorem5_seed kA qB qH kS qT qW SeqU SeqU_pass SeqU_ll (BO(A)) RwSeed RwSeed_ll BO_bounded
             BO_ll &m hkA hqB hqH hkS hqT hqW.
by move: h1 h2 => /= h1 h2; smt().
qed.

(* Theorem 5 (b) with the outcomes revealed. *)
lemma theorem5_pair_trials &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GamePRO(Setup0P(SeqU), A, Rf).main() @ &m : res.`2 = (Gen.p, Gen.q)] <=
    minr (top2 (kA %/ 12 + 1) (kS + 1)) (top2 (kA %/ 12) kS + p1 * s1) + epsW kA kS qB qH qT qW +
    inv (2%r ^ 120).
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := disc_game (fun (out : seed * (pw * pp)) (p : pw) (q : pp) _ => out.`2 = (p, q)) A Rf Rf_ll
             RwPair RwPair_ll RwPair_win A_ll &m.
have h2 := theorem5_pair kA qB qH kS qT qW SeqU SeqU_pass SeqU_ll (BO(A)) RwPair RwPair_ll BO_bounded
             BO_ll &m hkA hqB hqH hkS hqT hqW.
by move: h1 h2 => /= h1 h2; smt().
qed.
end section DiscT5.


(* ---- Corollary W5 when the generation reveals its outcomes ------------------------------------ *)
module type AdvP5O (O : OraclesP) = {
  proc guess(y : state, om : data, outs : bool list) : state * pp
}.

module Game5O (S : SETUPP) (A : AdvP5O) (Rf : AFTER5) = {
  proc main() : state * pp = {
    var y, om, out;
    (y, om) <@ S.run();
    if (y = Gen.e) {
      out <@ Rf.run(Gen.p, Gen.q, y);
    } else {
      CountP(IP).init();
      out <@ A(CountP(IP)).guess(y, om, Trials.outs);
    }
    return out;
  }
}.

module BO5 (A : AdvP5O) (O : OraclesP) = {
  proc guess(y : state, om : data) : state * pp = {
    var ok, i, r, out;
    TF.outs <- []; ok <- false; i <- -1;
    while (i + 1 < ntr) {
      if (!ok) {
        r <$ dr;
        ok <- r < k16;
        TF.outs <- rcons TF.outs ok;
      }
      i <- i + 1;
    }
    out <@ A(O).guess(y, om, TF.outs);
    return out;
  }
}.

(* The response after a refusal that always wins Corollary W5's game: the container is the entropy. *)
module Rw5 : AFTER5 = {
  proc run(p : pw, q : pp, y : state) : state * pp = { return (y, q); }
}.

lemma Rw5_ll : islossless Rw5.run.
proof. by proc; auto. qed.

section DiscGame5.
declare module A <: AdvP5O {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                           -RTE.FunRO, -RW.RO, -Gen, -Trials, -Count, -CountP, -TBO, -SvO, -CC, -TF, -HV,
                           -VVO.RO, -VVO.FRO}.
declare module Rf <: AFTER5 {-Gen}.
declare axiom Rf_ll : islossless Rf.run.
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

local module CW5 (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed, outs : bool list) : bool = {
    var out, b;
    b <- true;
    if (y <> e) {
      CountP(O).init();
      out <@ A(CountP(O)).guess(y, om, outs);
      b <- out = (e, q);
    }
    return b;
  }
}.

local lemma CW5_ll (O <: OraclesP {-CW5}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless CW5(O).run.
proof.
move=> ha hb hh hs ht hw; proc; sp; if => //; wp.
call (A_ll (CountP(O)) _ _ _ _ _ _); 1..6: by proc; inline *; wp; (call ha || call hb || call hh ||
  call hs || call ht || call hw); auto.
by inline *; auto.
qed.

local lemma CW5_ll_IP : islossless CW5(IP).run.
proof. by apply (CW5_ll IP); proc; inline *; auto => />; smt(dans_ll dseed_ll dct_ll ddata_ll). qed.

local lemma CW5_ll_ST : islossless CW5(IPSTO(RSE.FunRO, RTE.FunRO)).run.
proof. by apply (CW5_ll (IPSTO(RSE.FunRO, RTE.FunRO))); proc; inline *; auto => />; smt(dans_ll ddata_ll). qed.

lemma disc_game5 &m :
  Pr[Game5O(Setup0P(SeqU), A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
  Pr[Game5(Setup0P(SeqU), BO5(A), Rw5).main() @ &m : res = (Gen.e, Gen.q)] + inv (2%r ^ 120).
proof.
have h1 : Pr[Game5O(Setup0P(SeqU), A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
          Pr[GenGameO(Setup0P(SeqU), CW5).main() @ &m : res].
- byequiv => //; proc; inline CW5(IP).run; wp.
  seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, Trials.outs, R.RO.m, RS.RO.m, RT.RO.m,
               RW.RO.m}); 1: by sim.
  sp; if{1}.
  + rcondf{2} 1; 1: by auto => /#.
    by wp; call{1} Rf_ll; auto.
  rcondt{2} 1; 1: by auto => /#.
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
              CountP.cw}); 1..6: by sim.
  by inline *; auto => /> /#.
have h2 := seqU_disclosure CW5 &m CW5_ll_IP CW5_ll_ST.
have h3 : Pr[GenGameO(Setup0P(SeqU), CB(CW5)).main() @ &m : res] <=
          Pr[Game5(Setup0P(SeqU), BO5(A), Rw5).main() @ &m : res = (Gen.e, Gen.q)].
- byequiv => //; proc; inline CB(CW5, IP).run CW5(IP).run.
  seq 1 1 : (={y, om, glob A, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m,
               RW.RO.m}); 1: by sim.
  case (y{1} = Gen.e{1}).
  + rcondf{1} 20; 1: by move=> &2; wp; while true; [wp; if; auto | auto].
    rcondt{2} 1; 1: by auto.
    inline Rw5.run; wp.
    while{1} true (ntr - i{1}); 1: by move=> &2 z; wp; if; auto => />; smt(dr_ll).
    by auto => /#.
  rcondt{1} 20; 1: by move=> &2; wp; while true; [wp; if; auto | auto].
  rcondf{2} 1; 1: by auto.
  inline BO5(A, CountP(IP)).guess.
  swap{2} 1 6.
  wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct,
              CountP.cw}); 1..6: by sim.
  call (_ : true ==> ={Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}).
  + by proc; inline *; auto.
  wp; while (={i, ok, TF.outs}); 1: by wp; if => //; auto.
  by auto => />.
smt().
qed.
end section DiscGame5.

section DiscW5.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op kS : int.
declare op qT : int.
declare op qW : int.
declare module A <: AdvP5O {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                            -RTE.FunRO, -RW.RO, -Gen, -Trials, -Count, -CountB, -CountP, -Mon, -Bwd,
                            -WithP, -AP, -AW5, -TBO, -SvO, -CC, -TF, -HV, -VVO.RO, -VVO.FRO}.
declare module Rf <: AFTER5 {-Gen}.
declare axiom Rf_ll : islossless Rf.run.
declare axiom A_bounded (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW].
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

local lemma BO5_bounded (O <: OraclesP {-Count, -CountP, -BO5(A)}) :
  hoare [BO5(A, CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW].
proof.
proc; call (A_bounded O).
by while (Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0);
  [wp; if; auto | auto].
qed.

local lemma BO5_ll (O <: OraclesP {-BO5(A)}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless BO5(A, O).guess.
proof.
move=> ha hb hh hs ht hw; proc; call (A_ll O ha hb hh hs ht hw).
while true (ntr - i); 2: by auto => /#.
by move=> z; wp; if; auto => />; smt(dr_ll).
qed.

(* Corollary W5 with the outcomes revealed: its bound plus 2^-120. *)
lemma W5_trials &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[Game5O(Setup0P(SeqU), A, Rf).main() @ &m : res = (Gen.e, Gen.q)] <=
    top2 (kA %/ 12) (kS + 1) + epsC kA (kS + 1) qB qH qT qW + deltagen kS qT + inv (2%r ^ 256) +
    inv (2%r ^ 120).
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := disc_game5 A Rf Rf_ll A_ll &m.
have h2 := W5 kA qB qH kS qT qW SeqU SeqU_pass SeqU_ll (BO5(A)) Rw5 Rw5_ll BO5_bounded BO5_ll &m
             hkA hqB hqH hkS hqT hqW.
smt().
qed.
end section DiscW5.
