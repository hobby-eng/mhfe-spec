(* Lemma W4 and Theorem 5 (DESIGN-NOTES A.6). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision Passphrase Generation Selection Theta2.
import W128 StdBigop.Bigreal.BRA RealOrder.

section Theorem5.

declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op kS : int.
declare op qT : int.
declare op qW : int.

declare module A <: AdvP {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Gen, -Trials, -Count, -CountB, -CountP, -Mon, -Bwd,
                          -WithP, -AP}.
declare axiom A_bounded (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW].

declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

(* ---- Θ1 and Θ2 until Bad, and Θ2 run lazily ------------------------------------------------ *)
(* The oracles of GameP with the S, T and Omega queries recorded. *)
local module IPL : OraclesP = {
  proc a = Ideal.a
  proc b = Ideal.b
  proc h = Ideal.h
  proc s(e : state, q : pp) = { var d; WithP.sq <- rcons WithP.sq (e, q); d <@ RS.RO.get(e, q); return d; }
  proc t(d : seed) = { var c; WithP.tq <- rcons WithP.tq d; c <@ RT.RO.get(d); return c; }
  proc w(d : seed) = { var o; WithP.wq <- rcons WithP.wq d; o <@ RW.RO.get(d); return o; }
}.

local module G2L = {
  proc main() : seed * (pw * pp) = {
    var y, om, out;
    (y, om) <@ Setup2P.run();
    WithP.sq <- []; WithP.tq <- []; WithP.wq <- [];
    CountP(IPL).init();
    out <@ A(CountP(IPL)).guess(y, om);
    return out;
  }
}.

(* Θ1 and Θ2 differ only at (e*, Q) for S and at seed* for T and Omega. *)
local equiv upto_theta : GameP(Setup1P, A).main ~ G2L.main :
  ={glob A} ==>
  !badP Gen.e{2} Gen.q{2} Gen.sd{2} WithP.sq{2} WithP.tq{2} WithP.wq{2} => ={res, glob A, Gen.p, Gen.q, Gen.e, Gen.sd}.
proof.
proc; inline Setup1P.run Setup2P.run.
call (_ : badP Gen.e Gen.q Gen.sd WithP.sq WithP.tq WithP.wq,
          ={R.RO.m, Gen.p, Gen.q, Gen.e, Gen.sd} /\
          eq_except (pred1 (Gen.e, Gen.q){2}) RS.RO.m{1} RS.RO.m{2} /\ ((Gen.e, Gen.q) \notin RS.RO.m){2} /\
          eq_except (pred1 Gen.sd{2}) RT.RO.m{1} RT.RO.m{2} /\ (Gen.sd \notin RT.RO.m){2} /\
          eq_except (pred1 Gen.sd{2}) RW.RO.m{1} RW.RO.m{2} /\ (Gen.sd \notin RW.RO.m){2}).
- exact A_ll.
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- proc; inline *; case ((e, q){2} = (Gen.e, Gen.q){2}).
  + by auto => />; smt(mem_rcons).
  by auto => />; smt(eq_exceptP eq_except_set_eq mem_set get_setE mem_rcons domE).
- by move=> &2 _; proc; inline *; auto => />; smt(dseed_ll).
- by move=> &1; proc; inline *; auto => />; smt(dseed_ll mem_rcons).
- proc; inline *; case (d{2} = Gen.sd{2}).
  + by auto => />; smt(mem_rcons).
  by auto => />; smt(eq_exceptP eq_except_set_eq mem_set get_setE mem_rcons domE).
- by move=> &2 _; proc; inline *; auto => />; smt(dct_ll).
- by move=> &1; proc; inline *; auto => />; smt(dct_ll mem_rcons).
- proc; inline *; case (d{2} = Gen.sd{2}).
  + by auto => />; smt(mem_rcons).
  by auto => />; smt(eq_exceptP eq_except_set_eq mem_set get_setE mem_rcons domE).
- by move=> &2 _; proc; inline *; auto => />; smt(ddata_ll).
- by move=> &1; proc; inline *; auto => />; smt(ddata_ll mem_rcons).
inline CountP(IP).init CountP(IPL).init Count(IP).init Count(IPL).init RS.RO.set RT.RO.set RW.RO.set.
wp; rnd{1}; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto => />; smt(eq_except_setl mem_empty W240.DWord.dunifin_ll).
qed.

(* Θ2 with the chain of P inverted before the run (M0) or after it (M1), on any oracle for A, B, H. *)
local module IPLG (G : R.RO) : OraclesP = {
  proc a = Orc(G).a
  proc b = Orc(G).b
  proc h = Orc(G).h
  proc s = IPL.s
  proc t = IPL.t
  proc w = IPL.w
}.

local module M0 (G : R.RO) = {
  proc distinguish() : bool = {
    var y, om;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    y <$ dstate;
    om <$ ddata;
    Gen.e <@ Net(Orc(G)).dec(Gen.p, y);
    WithP.sq <- []; WithP.tq <- []; WithP.wq <- [];
    CountP(IPLG(G)).init();
    AP.out <@ A(CountP(IPLG(G))).guess(y, om);
    Gen.q <$ dQ;
    Gen.sd <$ dseed;
    return true;
  }
}.

local module M1 (G : R.RO) = {
  proc distinguish() : bool = {
    var y, om;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    y <$ dstate;
    om <$ ddata;
    WithP.sq <- []; WithP.tq <- []; WithP.wq <- [];
    CountP(IPLG(G)).init();
    AP.out <@ A(CountP(IPLG(G))).guess(y, om);
    Gen.e <@ Net(Orc(G)).dec(Gen.p, y);
    Gen.q <$ dQ;
    Gen.sd <$ dseed;
    return true;
  }
}.

(* Q and seed* are not used during the run. *)
local equiv g2_m0 : G2L.main ~ R.MainD(M0, R.RO).distinguish :
  ={glob A} ==> res{1} = AP.out{2} /\ ={glob A, Gen.p, Gen.q, Gen.sd, Gen.e, WithP.sq, WithP.tq, WithP.wq}.
proof.
proc; inline Setup2P.run M0(R.RO).distinguish.
swap{1} 9 7; swap{1} 6 9.
wp; rnd; rnd.
call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, WithP.sq, WithP.tq, WithP.wq}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
inline CountP(IPL).init CountP(IPLG(R.RO)).init Count(IPL).init Count(IPLG(R.RO)).init; wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto.
qed.

(* With A, B, H a whole function, the inversion is a function of P and Y. *)
local equiv m0_m1 : R.MainD(M0, RE.FunRO).distinguish ~ R.MainD(M1, RE.FunRO).distinguish :
  ={glob A} ==> ={glob A, Gen.p, Gen.q, Gen.sd, Gen.e, AP.out, WithP.sq, WithP.tq, WithP.wq}.
proof.
proc; inline M0(RE.FunRO).distinguish M1(RE.FunRO).distinguish.
seq 8 8 : (={glob A, y, om, Gen.p, RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim.
seq 1 0 : (#pre /\ Gen.e{1} = invperm RE.FunRO.f{1} Gen.p{1} y{1}).
- by exlim Gen.p{1}, y{1} => p0 y0; call{1} (dec_fun_ph p0 y0); auto.
seq 5 5 : (={glob A, y, Gen.p, RE.FunRO.f, AP.out, WithP.sq, WithP.tq, WithP.wq} /\
           Gen.e{1} = invperm RE.FunRO.f{1} Gen.p{1} y{1}).
- call (_ : ={RE.FunRO.f, RS.RO.m, RT.RO.m, RW.RO.m, WithP.sq, WithP.tq, WithP.wq}).
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  by inline *; auto.
seq 0 1 : (#pre /\ Gen.e{2} = invperm RE.FunRO.f{2} Gen.p{2} y{2}).
- by exlim Gen.p{2}, y{2} => p0 y0; call{2} (dec_fun_ph p0 y0); auto.
by auto.
qed.

(* The run with the monitored oracle of Chain. *)
local equiv m1_t2 : R.MainD(M1, R.RO).distinguish ~ Theta2L(A).main :
  ={glob A} ==> ={glob A, AP.out, Gen.q, Gen.sd, WithP.sq, WithP.tq, WithP.wq} /\
                Gen.p{1} = Bwd.p{2} /\ Gen.e{1} = res{2}.
proof.
proc; inline M1(R.RO).distinguish ChainGame(AP(A)).main AP(A, CountB(Mon)).run.
wp; rnd; rnd; wp.
call (_ : ={R.RO.m}).
- while (={i, p, y, R.RO.m}); 2: by auto.
  wp; call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by proc; inline *; auto.
  wp; call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by proc; inline *; auto.
  wp; call (_ : ={arg, R.RO.m} ==> ={res, R.RO.m}); 1: by proc; inline *; auto.
  by auto.
wp; call (_ : ={R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, WithP.sq, WithP.tq, WithP.wq}).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
by inline *; auto.
qed.

(* Θ2 runs lazily, for every event of the adversary's state and output, the secrets and the queries. *)
local lemma lazy_thetaX (F : glob A -> seed * (pw * pp) -> pw -> pp -> state -> seed -> (state * pp) list ->
                             seed list -> seed list -> bool) &m :
  Pr[G2L.main() @ &m : F (glob A) res Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq] =
  Pr[Theta2L(A).main() @ &m : F (glob A) AP.out Bwd.p Gen.q res Gen.sd WithP.sq WithP.tq WithP.wq].
proof.
have -> : Pr[G2L.main() @ &m : F (glob A) res Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq] =
          Pr[R.MainD(M0, R.RO).distinguish() @ &m : F (glob A) AP.out Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq].
- by byequiv g2_m0 => // /#.
have -> : Pr[R.MainD(M0, R.RO).distinguish() @ &m : F (glob A) AP.out Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq] =
          Pr[R.MainD(M0, RE.FunRO).distinguish() @ &m : F (glob A) AP.out Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq].
- by byequiv (RO_FunRO M0) => // /#.
have -> : Pr[R.MainD(M0, RE.FunRO).distinguish() @ &m : F (glob A) AP.out Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq] =
          Pr[R.MainD(M1, RE.FunRO).distinguish() @ &m : F (glob A) AP.out Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq].
- by byequiv m0_m1 => // /#.
have -> : Pr[R.MainD(M1, RE.FunRO).distinguish() @ &m : F (glob A) AP.out Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq] =
          Pr[R.MainD(M1, R.RO).distinguish() @ &m : F (glob A) AP.out Gen.p Gen.q Gen.e Gen.sd WithP.sq WithP.tq WithP.wq].
- by rewrite eq_sym; byequiv (RO_FunRO M1) => // /#.
by byequiv m1_t2 => // /#.
qed.

(* Θ1 and Θ2 are identical until Bad (inequality (3)) for every event of the adversary's state and
   output and the secrets, and Θ2 runs lazily. *)
lemma upto_bad_theta (F : glob A -> seed * (pw * pp) -> pw -> pp -> state -> seed -> bool) &m :
  Pr[GameP(Setup1P, A).main() @ &m : F (glob A) res Gen.p Gen.q Gen.e Gen.sd] <=
  Pr[Theta2L(A).main() @ &m :
       F (glob A) AP.out Bwd.p Gen.q res Gen.sd \/
       (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq].
proof.
rewrite -(lazy_thetaX (fun (g : glob A) (out : seed * (pw * pp)) (p : pw) (q : pp) (e : state) (sd : seed)
                          (sq : (state * pp) list) (tq wq : seed list) =>
                          F g out p q e sd \/ (e, q) \in sq \/ sd \in tq \/ sd \in wq) &m) /=.
by byequiv upto_theta => // /#.
qed.

(* ---- The budgets in the lazy Θ2 ------------------------------------------------------------- *)
(* The oracles of AP without its count of S, T and Omega. *)
local module PX (O : ABHB) : OraclesP = {
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc s = IPL.s
  proc t = IPL.t
  proc w = IPL.w
}.

local equiv AP_eqv (O <: ABHB {-Count, -CountB, -CountP, -A, -WithP, -RS.RO, -RT.RO, -RW.RO}) :
  A(WithP(CountB(O))).guess ~ A(CountP(PX(O))).guess :
  ={glob A, glob O, arg, RS.RO.m, RT.RO.m, RW.RO.m, WithP.sq, WithP.tq, WithP.wq,
    Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw} ==>
  ={Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw, WithP.sq, WithP.tq, WithP.wq}.
proof.
proc (={glob O, RS.RO.m, RT.RO.m, RW.RO.m, WithP.sq, WithP.tq, WithP.wq,
        Count.ca, Count.cb, Count.ch, CountP.cs, CountP.ct, CountP.cw}) => //.
- by proc; inline *; sim.
- by proc; inline *; sim.
- by proc; inline *; sim.
- by proc; inline *; auto.
- by proc; inline *; auto.
by proc; inline *; auto.
qed.

local lemma AP_bounded (O <: ABHB {-Count, -CountB, -CountP, -A, -WithP, -RS.RO, -RT.RO, -RW.RO, -AP}) :
  hoare [AP(A, CountB(O)).run : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 ==>
         Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
         size WithP.sq <= kS /\ size WithP.tq <= qT /\ size WithP.wq <= qW].
proof.
proc; wp.
call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 /\
          size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw ==>
          Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
          CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW /\
          size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw).
- conseq (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
              Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
              CountP.cs <= kS /\ CountP.ct <= qT /\ CountP.cw <= qW)
         (_ : size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw ==>
              size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw) => //.
  + proc (size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw) => //.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; auto => />; smt(size_rcons).
    + by proc; inline *; auto => />; smt(size_rcons).
    by proc; inline *; auto => />; smt(size_rcons).
  by conseq (AP_eqv O) (A_bounded (PX(O))) => /#.
by inline *; auto.
qed.

local lemma theta_budget : hoare [ChainGame(AP(A)).main : true ==>
  Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
  size WithP.sq <= kS /\ size WithP.tq <= qT /\ size WithP.wq <= qW].
proof.
proc; inline Net(Mon).dec.
wp; while (Count.ca <= kA /\ Count.cb <= qB /\ Count.ch <= qH /\
           size WithP.sq <= kS /\ size WithP.tq <= qT /\ size WithP.wq <= qW); 1: by inline *; auto.
by wp; call (AP_bounded Mon); inline *; auto.
qed.

(* One cost budget: Argon2id calls cost cA and seed computations cS, at most c in all on every run. *)
local lemma AP_cost (cA cS c : real) (O <: ABHB {-Count, -CountB, -CountP, -A, -WithP, -RS.RO, -RT.RO, -RW.RO, -AP}) :
  (forall (O' <: OraclesP {-Count, -CountP, -A}),
     hoare [A(CountP(O')).guess :
       Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
       cA * Count.ca%r + cS * CountP.cs%r <= c]) =>
  hoare [AP(A, CountB(O)).run : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 ==>
         cA * Count.ca%r + cS * (size WithP.sq)%r <= c].
proof.
move=> hcost; proc; wp.
call (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 /\
          size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw ==>
          cA * Count.ca%r + cS * CountP.cs%r <= c /\
          size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw).
- conseq (_ : Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
              cA * Count.ca%r + cS * CountP.cs%r <= c)
         (_ : size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw ==>
              size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw) => //.
  + proc (size WithP.sq = CountP.cs /\ size WithP.tq = CountP.ct /\ size WithP.wq = CountP.cw) => //.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; wp; call (_ : true); auto.
    + by proc; inline *; auto => />; smt(size_rcons).
    + by proc; inline *; auto => />; smt(size_rcons).
    by proc; inline *; auto => />; smt(size_rcons).
  by conseq (AP_eqv O) (hcost (PX(O))) => /#.
by inline *; auto.
qed.

local lemma theta_cost (cA cS c : real) :
  (forall (O' <: OraclesP {-Count, -CountP, -A}),
     hoare [A(CountP(O')).guess :
       Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
       cA * Count.ca%r + cS * CountP.cs%r <= c]) =>
  hoare [ChainGame(AP(A)).main : true ==> cA * Count.ca%r + cS * (size WithP.sq)%r <= c].
proof.
move=> hcost; proc; inline Net(Mon).dec.
wp; while (cA * Count.ca%r + cS * (size WithP.sq)%r <= c); 1: by inline *; auto.
by wp; call (AP_cost cA cS c Mon hcost); inline *; auto.
qed.

(* The seed query when the adversary did not query c_36 (event N). *)
local lemma S_N_game : 0 <= kS =>
  ehoare [ChainGame(AP(A)).main : (s1 * kS%r * e128)%xr ==>
    (if !(Bwd.sts Bwd.p).`early /\ !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log) /\
        size WithP.sq <= kS /\ (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs
     then wS WithP.sq res else 0%r)%xr].
proof.
move=> hkS; proc.
conseq (_ : _ ==> (!Mon.inrun) `|` (phiS kS WithP.sq Mon.log (Bwd.sts Bwd.p))%xr).
- by move=> _; apply xle_cxr_l => // *; apply xle_cxr_r => _; apply postS.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call (dec_gS kS); wp.
conseq (_ : _ ==> (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (s1 * kS%r * e128)%xr).
- move=> _; apply xle_cxr_l => // *; apply xle_cxr_r => -[_ hf] /=; apply le_pos.
  by apply run_endS => //; move: hf; rewrite /fin_logged => hf; apply hf.
- by move=> &hr; apply xle_cxr_r => h; apply h.
inline AP(A, CountB(Mon)).run; wp.
call (: (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (s1 * kS%r * e128)%xr ==>
        (Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (s1 * kS%r * e128)%xr).
- proc ((Mon.inrun /\ fin_logged Mon.log Bwd.sts) `|` (s1 * kS%r * e128)%xr).
  + by move=> &hr; apply xlexx.
  + by move=> &hr; apply xlexx.
  + exact (countb_a_k (s1 * kS%r * e128)).
  + exact (count_b_k (s1 * kS%r * e128)).
  + exact (count_h_k (s1 * kS%r * e128)).
  + by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hf]; rewrite hi hf /= ?if_same EpC dseed_ll smul1m.
  + by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hf]; rewrite hi hf /= ?if_same EpC dct_ll smul1m.
  by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hf]; rewrite hi hf /= ?if_same EpC ddata_ll smul1m.
inline *; auto => &hr.
rewrite (eq_Ep _ _ (fun _ => (s1 * kS%r * e128)%xr)) => [p0 _ /= | ].
- rewrite (eq_Ep _ _ (fun _ => (s1 * kS%r * e128)%xr)) => [y1 _ /= | ].
  + rewrite (eq_Ep _ _ (fun _ => (s1 * kS%r * e128)%xr)) => [om1 _ /= | ].
    * have -> : fin_logged [] (fun _ => cbwd y1) = true by rewrite eqT /fin_logged /cbwd.
      by [].
    by rewrite EpC ddata_ll smul1m.
  by rewrite EpC dstate_ll smul1m.
by rewrite EpC dP_ll smul1m.
qed.

local lemma bad_S_N_e : 0 <= kS =>
  ehoare [Theta2L(A).main : (s1 * kS%r * e128)%xr ==>
    ((res, Gen.q) \in WithP.sq /\ !(Bwd.sts Bwd.p).`early /\
     !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log) /\
     size WithP.sq <= kS /\ (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs)%xr].
proof.
move=> hkS; proc.
seq 1 : (if !(Bwd.sts Bwd.p).`early /\ !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log) /\
            size WithP.sq <= kS /\ (Bwd.sts Bwd.p).`fin /\ xs = (Bwd.sts Bwd.p).`xs
         then wS WithP.sq xs else 0%r)%xr.
- by call (S_N_game hkS).
by auto => &hr; apply Ep_wS_end.
qed.

local lemma theta_facts : hoare [Theta2L(A).main : true ==>
  size WithP.sq <= kS /\ (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs)].
proof.
proc; auto; call (_ : true ==> size WithP.sq <= kS /\
  (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs)); 2: by auto.
by conseq theta_budget (chain_end (AP(A))) => /#.
qed.

(* The seed query when the adversary did not query c_36 (event N). *)
lemma bad_S_N &m : 0 <= kS =>
  Pr[Theta2L(A).main() @ &m :
       (res, Gen.q) \in WithP.sq /\ !(Bwd.sts Bwd.p).`early /\ !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log)]
    <= s1 * kS%r / 2%r ^ 128.
proof.
move=> hkS.
have h1 : Pr[Theta2L(A).main() @ &m : !(size WithP.sq <= kS /\
             (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs))] = 0%r.
- by byphoare => //; hoare; conseq theta_facts.
have h2 : Pr[Theta2L(A).main() @ &m :
             (res, Gen.q) \in WithP.sq /\ !(Bwd.sts Bwd.p).`early /\
             !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log) /\
             size WithP.sq <= kS /\ (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs] <= s1 * kS%r * e128.
- byehoare (_ : (s1 * kS%r * e128)%xr ==> _) => //; 1: exact (bad_S_N_e hkS).
  by have := s1_ge0; have := e128_gt0; smt().
have h3 : Pr[Theta2L(A).main() @ &m :
             (res, Gen.q) \in WithP.sq /\ !(Bwd.sts Bwd.p).`early /\
             !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log)] <=
          Pr[Theta2L(A).main() @ &m :
             ((res, Gen.q) \in WithP.sq /\ !(Bwd.sts Bwd.p).`early /\
              !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log) /\
              size WithP.sq <= kS /\ (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs) \/
             !(size WithP.sq <= kS /\
               (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs))].
- by rewrite Pr[mu_sub] => // &hr /#.
move: h3; rewrite Pr[mu_or] h1; move: h2; rewrite /e128; smt(mu_bounded).
qed.

(* seed* is drawn after the run. *)
lemma bad_TW &m : 0 <= qT => 0 <= qW =>
  Pr[Theta2L(A).main() @ &m : Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq] <= (qT%r + qW%r) / 2%r ^ 512.
proof.
move=> hqT hqW; byphoare => //; proc.
seq 2 : (size WithP.tq <= qT /\ size WithP.wq <= qW) 1%r ((qT%r + qW%r) / 2%r ^ 512) 0%r 0%r => //.
- rnd; last by move=> _; smt(expr_gt0 invr_gt0).
  skip => /> &hr htq hwq.
  apply (ler_trans (mu dseed (mem (WithP.tq{hr} ++ WithP.wq{hr})))).
  + by apply mu_le => x _; rewrite mem_cat.
  apply (ler_trans ((size (WithP.tq{hr} ++ WithP.wq{hr}))%r * inv (2%r ^ 512))).
  + by apply mu_mem_le_mu1 => x; rewrite dseed1.
  by rewrite size_cat; have := e512_gt0; smt().
by hoare; rnd; call theta_budget; auto; smt().
qed.

lemma bad_W &m : 0 <= qW => Pr[Theta2L(A).main() @ &m : Gen.sd \in WithP.wq] <= qW%r / 2%r ^ 512.
proof.
move=> hqW; byphoare => //; proc.
seq 2 : (size WithP.wq <= qW) 1%r (qW%r / 2%r ^ 512) 0%r 0%r => //.
- rnd; last by move=> _; smt(expr_gt0 invr_gt0).
  skip => /> &hr hwq.
  apply (ler_trans ((size WithP.wq{hr})%r * inv (2%r ^ 512))).
  + by apply mu_mem_le_mu1 => x; rewrite dseed1.
  by have := e512_gt0; smt().
by hoare; rnd; call theta_budget; auto; smt().
qed.

(* ---- Lemma W4 --------------------------------------------------------------------------------- *)
(* The adversary of Theorem 5 submits no batches: one logged query per call. *)
local lemma bn_uniq : hoare [ChainGame(AP(A)).main : true ==> uniq (map snd Mon.log)].
proof.
proc; inline Net(Mon).dec.
wp; while (!Mon.inrun /\ uniq (map snd Mon.log)); 1: by inline *; auto.
wp; inline AP(A, CountB(Mon)).run; wp.
call (_ : Mon.inrun /\ uniq (map snd Mon.log) /\ all (fun (e : point * int) => e.`2 <= Mon.bn) Mon.log).
- by proc; inline *; auto => />; smt(map_rcons rcons_uniq allP all_rcons1 mapP).
- by proc; inline *; auto => />; smt(map_rcons rcons_uniq allP all_rcons1 mapP).
- by proc; inline *; auto => />; smt(map_rcons rcons_uniq allP all_rcons1 mapP).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
by inline *; auto.
qed.

local lemma W4_e : 0 <= kA =>
  ehoare [ChainLate(AP(A)).main : (kA%r * (e128 + e256))%xr ==>
    ((col1 R.RO.m Mon.log Bwd.p Bwd.y (Bwd.sts Bwd.p) \/ col2 R.RO.m Mon.log (Bwd.sts Bwd.p)) /\
     !(Bwd.sts Bwd.p).`early /\ (Bwd.sts Bwd.p).`fin /\ Count.ca <= kA)%xr].
proof.
move=> hkA; proc.
conseq (_ : _ ==> (!Mon.inrun /\ gD R.RO.m Mon.log Count.ca Bwd.p (Bwd.sts Bwd.p)) `|`
                  (phiDC kA Count.ca R.RO.m Mon.log Bwd.y Bwd.p (Bwd.sts Bwd.p))%xr).
- by move=> _; apply xle_cxr_l => // *; apply xle_cxr_r => -[_ [hsh _]]; apply postC.
- by move=> &hr; apply xle_cxr_r => h; apply h.
call (dec_C kA hkA); wp.
conseq (_ : _ ==> (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
                  (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr).
- by move=> _; apply xle_cxr_l => // *; apply run_decC.
- by move=> &hr; apply xle_cxr_r => h; apply h.
inline AP(A, CountB(Mon)).run; wp.
call (: (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
        (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr ==>
        (Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
        (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr).
- proc ((Mon.inrun /\ gC R.RO.m Mon.log Mon.bn Count.ca Bwd.sts) `|`
        (phiC kA Count.ca Mon.inrun R.RO.m Mon.log Bwd.y Bwd.sts)%xr).
  + by move=> &hr; apply xlexx.
  + by move=> &hr; apply xlexx.
  + exact (countb_a_C kA hkA).
  + exact (count_b_C kA hkA).
  + exact (count_h_C kA hkA).
  + by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi hg /= ?if_same EpC dseed_ll smul1m.
  + by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi hg /= ?if_same EpC dct_ll smul1m.
  by proc; inline *; auto => &hr /=; apply xle_cxr_r => -[hi hg]; rewrite hi hg /= ?if_same EpC ddata_ll smul1m.
inline *; auto => &hr.
rewrite (eq_Ep _ _ (fun _ => (kA%r * (e128 + e256))%xr)) => [y1 _ /= | ].
- rewrite (eq_Ep _ _ (fun _ => (kA%r * (e128 + e256))%xr)) => [om1 _ /= | ].
  + have -> : gC empty [] 0 0 (fun _ => cbwd y1) = true.
    * rewrite eqT; split; 1: by move=> w; apply shape_bwd.
      split; 1: by move=> x; rewrite mem_empty.
      split; 1: by [].
      split; 1: by [].
      split; 1: by rewrite /fin_logged /cbwd.
      by move=> w _ t; rewrite /cbwd /=; smt().
    rewrite /= /phiC /= hkA /= /psiC /cbwd /=.
    by rewrite -Bigreal.BRA.mulr_suml sum_dP; smt().
  by rewrite EpC ddata_ll smul1m.
by rewrite EpC dstate_ll smul1m.
qed.

(* The samplings after the lazy game do not matter for its events. *)
local lemma pr_theta_cg (ev : (point, ans) fmap -> (point * int) list -> pw -> state -> (pw -> cst) -> int -> bool) &m :
  Pr[Theta2L(A).main() @ &m : ev R.RO.m Mon.log Bwd.p Bwd.y Bwd.sts Count.ca] =
  Pr[ChainGame(AP(A)).main() @ &m : ev R.RO.m Mon.log Bwd.p Bwd.y Bwd.sts Count.ca].
proof.
byequiv (_ : ={glob A} ==> ={R.RO.m, Mon.log, Bwd.p, Bwd.y, Bwd.sts, Count.ca}) => //.
proc *; inline{1} Theta2L(A).main; wp; rnd{1}; rnd{1}; wp.
call (_ : ={glob A} ==> ={res, R.RO.m, Mon.log, Bwd.p, Bwd.y, Bwd.sts, Count.ca}); 1: by sim.
by auto => />; smt(dQ_ll dseed_ll).
qed.

(* Lemma W4. *)
lemma W4 &m : 0 <= kA =>
  Pr[Theta2L(A).main() @ &m :
       coll R.RO.m Mon.log Bwd.p Bwd.y /\ !(Bwd.sts Bwd.p).`early /\
       last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log]
    <= kA%r / 2%r ^ 128 + kA%r / 2%r ^ 256.
proof.
move=> hkA.
have -> := pr_theta_cg (fun m log p y (sts : pw -> cst) (ca : int) =>
             coll m log p y /\ !(sts p).`early /\ last witness (sts p).`chain \in map fst log) &m.
have hinv : Pr[ChainGame(AP(A)).main() @ &m :
               !inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p)] = 0%r.
- by byphoare => //; hoare; conseq (chain_inv (AP(A))).
have hend : Pr[ChainGame(AP(A)).main() @ &m :
               !(!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin)] = 0%r.
- by byphoare => //; hoare; conseq (chain_end (AP(A))) => /#.
have hbn : Pr[ChainGame(AP(A)).main() @ &m : !uniq (map snd Mon.log)] = 0%r.
- by byphoare => //; hoare; conseq bn_uniq.
have hca : Pr[ChainGame(AP(A)).main() @ &m : !(Count.ca <= kA)] = 0%r.
- by byphoare => //; hoare; conseq theta_budget => /#.
have hW : Pr[ChainGame(AP(A)).main() @ &m :
             (col1 R.RO.m Mon.log Bwd.p Bwd.y (Bwd.sts Bwd.p) \/ col2 R.RO.m Mon.log (Bwd.sts Bwd.p)) /\
             !(Bwd.sts Bwd.p).`early /\ (Bwd.sts Bwd.p).`fin /\ Count.ca <= kA] <= kA%r * (e128 + e256).
- have -> : Pr[ChainGame(AP(A)).main() @ &m :
               (col1 R.RO.m Mon.log Bwd.p Bwd.y (Bwd.sts Bwd.p) \/ col2 R.RO.m Mon.log (Bwd.sts Bwd.p)) /\
               !(Bwd.sts Bwd.p).`early /\ (Bwd.sts Bwd.p).`fin /\ Count.ca <= kA] =
            Pr[ChainLate(AP(A)).main() @ &m :
               (col1 R.RO.m Mon.log Bwd.p Bwd.y (Bwd.sts Bwd.p) \/ col2 R.RO.m Mon.log (Bwd.sts Bwd.p)) /\
               !(Bwd.sts Bwd.p).`early /\ (Bwd.sts Bwd.p).`fin /\ Count.ca <= kA].
  + by byequiv (chain_late (AP(A))).
  byehoare (_ : (kA%r * (e128 + e256))%xr ==> _) => //; 1: exact (W4_e hkA).
  by have := e128_gt0; have := e256_gt0; smt().
have hsub : Pr[ChainGame(AP(A)).main() @ &m :
               coll R.RO.m Mon.log Bwd.p Bwd.y /\ !(Bwd.sts Bwd.p).`early /\
               last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log] <=
            Pr[ChainGame(AP(A)).main() @ &m :
               ((col1 R.RO.m Mon.log Bwd.p Bwd.y (Bwd.sts Bwd.p) \/ col2 R.RO.m Mon.log (Bwd.sts Bwd.p)) /\
                !(Bwd.sts Bwd.p).`early /\ (Bwd.sts Bwd.p).`fin /\ Count.ca <= kA) \/
               (!inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) \/
                !(!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin)) \/
               (!uniq (map snd Mon.log) \/ !(Count.ca <= kA))].
- rewrite Pr[mu_sub] => // &hr [hc [hea hl]].
  case: (inv true false R.RO.m{hr} Mon.log{hr} Mon.bn{hr} Bwd.p{hr} (cbwd Bwd.y{hr}) (Bwd.sts{hr} Bwd.p{hr})) => hi; 2: by right; left; left.
  case: ((Bwd.sts{hr} Bwd.p{hr}).`fin) => hfin; 2: by right; left; right; rewrite hea.
  case: (uniq (map snd Mon.log{hr})) => hu; 2: by right; right; left.
  case: (Count.ca{hr} <= kA) => hk; 2: by right; right; right.
  left; rewrite hea /=.
  have [_ [_ [hsh hne]]] := hi; have [hord [_ [_ [_ hdet]]]] := hne hea.
  by apply (coll_split R.RO.m{hr} Mon.log{hr} Bwd.p{hr} Bwd.y{hr} (Bwd.sts{hr} Bwd.p{hr}) hu hea hfin hord
                       (determined_chain _ _ _ _ hdet) hsh hc hl).
rewrite /=; move: hsub; do 4! rewrite Pr[mu_or]; rewrite hinv hend hbn hca.
have := e128_gt0; have := e256_gt0; rewrite /e128 /e256; smt(mu_bounded).
qed.

(* ---- The term top2: P and Q drawn after the run ------------------------------------------------ *)
local module TopP = {
  proc main() : unit = {
    var p, y;
    R.RO.init();
    CountB(Mon).init();
    y <$ dstate;
    Mon.init(y);
    AP(A, CountB(Mon)).run(y);
    Mon.inrun <- false;
    p <$ dP;
    Bwd.p <- p;
    Gen.q <$ dQ;
  }
}.

local module ThetaLate = {
  proc main() : state = {
    var xs;
    xs <@ ChainLate(AP(A)).main();
    Gen.q <$ dQ;
    Gen.sd <$ dseed;
    return xs;
  }
}.

local equiv t2_late : Theta2L(A).main ~ ThetaLate.main :
  ={glob AP(A)} ==> ={res, R.RO.m, glob Mon, glob Bwd, Gen.q, Gen.sd, WithP.sq, WithP.tq, WithP.wq, AP.out, Count.ca}.
proof. by proc; rnd; rnd; call (chain_late (AP(A))). qed.

(* Without the decryption the table is the one of the run, which the decryption only extends. *)
local equiv late_topP : ThetaLate.main ~ TopP.main : ={glob A} ==>
  ={Bwd.p, Bwd.y, Mon.log, WithP.sq, AP.out, Gen.q, Count.ca} /\
  (forall x, x \in R.RO.m{2} => R.RO.m{1}.[x] = R.RO.m{2}.[x]).
proof.
proc; inline{1} ChainLate(AP(A)).main Net(Mon).dec.
rnd{1}; rnd.
seq 8 8 : (={Bwd.p, Bwd.y, Mon.log, WithP.sq, AP.out, Count.ca, R.RO.m} /\ !Mon.inrun{1}).
- by wp; rnd; wp; conseq (_ : _ ==> ={Bwd.y, Mon.log, WithP.sq, AP.out, Count.ca, R.RO.m}) => //; sim.
wp; while{1} (={Bwd.p, Bwd.y, Mon.log, WithP.sq, AP.out, Count.ca} /\ !Mon.inrun{1} /\
          (forall x, x \in R.RO.m{2} => R.RO.m{1}.[x] = R.RO.m{2}.[x])) (i{1} + 1).
- move=> &2 z; inline *; auto => />; smt(get_setE mem_set dans_ll).
by auto => />; smt(dseed_ll).
qed.

(* In the run every logged point is in the table. *)
local lemma topP_logm : hoare [TopP.main : true ==> forall x, x \in map fst Mon.log => x \in R.RO.m].
proof.
proc; rnd; wp; rnd; wp; inline AP(A, CountB(Mon)).run; wp.
call (_ : Mon.inrun /\ forall x, x \in map fst Mon.log => x \in R.RO.m).
- by proc; inline *; auto => />; smt(map_rcons mem_rcons mem_set).
- by proc; inline *; auto => />; smt(map_rcons mem_rcons mem_set).
- by proc; inline *; auto => />; smt(map_rcons mem_rcons mem_set).
- by proc; inline *; auto.
- by proc; inline *; auto.
- by proc; inline *; auto.
by inline *; auto => />; smt(mem_empty).
qed.

local lemma topP_e (Bud : int -> int -> bool) (S : (point * int) list -> (point, ans) fmap -> state ->
                        (state * pp) list -> seed * (pw * pp) -> (pw * pp) list) (b : real) :
  (forall log m y sq out, Bud (size sq) (count isA (map fst log)) => mass2 (undup (S log m y sq out)) <= b) =>
  0%r <= b =>
  ehoare [TopP.main : b%xr ==>
    ((Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out /\ Bud (size WithP.sq) (count isA (map fst Mon.log)))%xr].
proof.
move=> hS hb; proc.
seq 5 : (b%xr).
- inline AP(A, CountB(Mon)).run; wp.
  call (: b%xr ==> b%xr).
  + proc (b%xr) => //.
    * by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
    * by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
    * by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dans_ll smul1m.
    * by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dseed_ll smul1m.
    * by proc; inline *; auto => &hr /=; rewrite ?if_same EpC dct_ll smul1m.
    by proc; inline *; auto => &hr /=; rewrite ?if_same EpC ddata_ll smul1m.
  inline *; auto => &hr.
  rewrite (eq_Ep _ _ (fun _ => b%xr)) => [y1 _ /= | ]; 2: by rewrite EpC dstate_ll smul1m.
  by rewrite EpC ddata_ll smul1m.
auto => &hr.
apply (Ep_Z (S Mon.log{hr} R.RO.m{hr} Bwd.y{hr} WithP.sq{hr} AP.out{hr})
            (Bud (size WithP.sq{hr}) (count isA (map fst Mon.log{hr}))) b) => //.
by move=> h; apply hS.
qed.

(* Pr[(P, Q) in S] for a set S of the run that the decryption does not change. *)
local lemma top2_pr (Bud : int -> int -> bool) (S : (point * int) list -> (point, ans) fmap -> state ->
                         (state * pp) list -> seed * (pw * pp) -> (pw * pp) list) (b : real) &m :
  hoare [ChainGame(AP(A)).main : true ==> Bud (size WithP.sq) (count isA (map fst Mon.log))] =>
  (forall log m y sq out, Bud (size sq) (count isA (map fst log)) => mass2 (undup (S log m y sq out)) <= b) =>
  (forall log (m m' : (point, ans) fmap) y sq out, (forall x, x \in m => m'.[x] = m.[x]) =>
     (forall x, x \in map fst log => x \in m) => S log m' y sq out = S log m y sq out) =>
  0%r <= b =>
  Pr[Theta2L(A).main() @ &m : (Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out] <= b.
proof.
move=> hB hS hext hb.
have h0 : Pr[Theta2L(A).main() @ &m : !(Bud (size WithP.sq) (count isA (map fst Mon.log)))] = 0%r.
- by byphoare => //; hoare; proc; auto; call hB; auto.
have hL : Pr[TopP.main() @ &m : !(forall x, x \in map fst Mon.log => x \in R.RO.m)] = 0%r.
- by byphoare => //; hoare; conseq topP_logm.
have h1 : Pr[Theta2L(A).main() @ &m : (Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out /\
             Bud (size WithP.sq) (count isA (map fst Mon.log))] <=
          Pr[TopP.main() @ &m : ((Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out /\
             Bud (size WithP.sq) (count isA (map fst Mon.log))) \/
             !(forall x, x \in map fst Mon.log => x \in R.RO.m)].
- have -> : Pr[Theta2L(A).main() @ &m : (Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out /\
               Bud (size WithP.sq) (count isA (map fst Mon.log))] =
            Pr[ThetaLate.main() @ &m : (Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out /\
               Bud (size WithP.sq) (count isA (map fst Mon.log))].
  + by byequiv t2_late.
  byequiv late_topP => // &1 &2 [[-> [-> [-> [-> [-> [-> _]]]]]] hagr] [hin hc].
  case: (forall x, x \in map fst Mon.log{2} => x \in R.RO.m{2}) => hlm; [left | by right].
  by rewrite -(hext _ R.RO.m{2} R.RO.m{1}).
have h2 : Pr[TopP.main() @ &m : (Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out /\
             Bud (size WithP.sq) (count isA (map fst Mon.log))] <= b.
- by byehoare (_ : b%xr ==> _) => //; exact (topP_e Bud S b hS hb).
have h3 : Pr[Theta2L(A).main() @ &m : (Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out] <=
          Pr[Theta2L(A).main() @ &m : ((Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out /\
             Bud (size WithP.sq) (count isA (map fst Mon.log))) \/
             !(Bud (size WithP.sq) (count isA (map fst Mon.log)))].
- by rewrite Pr[mu_sub] => // &hr /#.
move: h1 h3; do ! rewrite Pr[mu_or]; rewrite h0 hL; smt(mu_bounded).
qed.

(* The same under the budgets of the section. *)
local lemma top2_prK (S : (point * int) list -> (point, ans) fmap -> state -> (state * pp) list ->
                          seed * (pw * pp) -> (pw * pp) list) (b : real) &m :
  (forall log m y sq out, size sq <= kS => count isA (map fst log) <= kA => mass2 (undup (S log m y sq out)) <= b) =>
  (forall log (m m' : (point, ans) fmap) y sq out, (forall x, x \in m => m'.[x] = m.[x]) =>
     (forall x, x \in map fst log => x \in m) => S log m' y sq out = S log m y sq out) =>
  0%r <= b =>
  Pr[Theta2L(A).main() @ &m : (Bwd.p, Gen.q) \in S Mon.log R.RO.m Bwd.y WithP.sq AP.out] <= b.
proof.
move=> hS; apply (top2_pr (fun s a => s <= kS /\ a <= kA) S b &m).
- by conseq theta_budget (log_count (AP(A))) => /#.
by move=> log m y sq out [hs hc]; apply hS.
qed.

(* ---- Θ2: win or Bad ---------------------------------------------------------------------------- *)
(* The lazy game satisfies the run facts used below. *)
local lemma theta_chain_facts : hoare [ChainGame(AP(A)).main : true ==>
  inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
  (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs) /\
  (!(Bwd.sts Bwd.p).`early => comp (Bwd.sts Bwd.p).`chain Mon.log =>
     12 <= count (isApw Bwd.p) (undup (map fst Mon.log)))].
proof.
conseq (chain_inv (AP(A))) (_ : true ==>
  (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs) /\
  (!(Bwd.sts Bwd.p).`early => comp (Bwd.sts Bwd.p).`chain Mon.log =>
     12 <= count (isApw Bwd.p) (undup (map fst Mon.log)))) => //.
by conseq (chain_end (AP(A))) (G5 (AP(A))) => /#.
qed.

local lemma pr_theta_res (ev : (point, ans) fmap -> (point * int) list -> pw -> state -> (pw -> cst) -> int -> state -> bool) &m :
  Pr[Theta2L(A).main() @ &m : ev R.RO.m Mon.log Bwd.p Bwd.y Bwd.sts Count.ca res] =
  Pr[ChainGame(AP(A)).main() @ &m : ev R.RO.m Mon.log Bwd.p Bwd.y Bwd.sts Count.ca res].
proof.
byequiv (_ : ={glob A} ==> ={res, R.RO.m, Mon.log, Bwd.p, Bwd.y, Bwd.sts, Count.ca}) => //.
proc *; inline{1} Theta2L(A).main; wp; rnd{1}; rnd{1}; wp.
call (_ : ={glob A} ==> ={res, R.RO.m, Mon.log, Bwd.p, Bwd.y, Bwd.sts, Count.ca}); 1: by sim.
by auto => />; smt(dQ_ll dseed_ll).
qed.

local lemma facts_theta &m : Pr[Theta2L(A).main() @ &m :
  !(inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
    (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs) /\
    (!(Bwd.sts Bwd.p).`early => comp (Bwd.sts Bwd.p).`chain Mon.log =>
       12 <= count (isApw Bwd.p) (undup (map fst Mon.log))))] = 0%r.
proof.
byphoare => //; hoare; proc; auto.
by call theta_chain_facts; auto.
qed.

(* Θ2: win or Bad lies in win or (P, Q) in Z, Early_P, the seed query without the last point, Coll_P,
   or a query of T or Omega at seed*. *)
local lemma theta2_split (E : seed * (pw * pp) -> pw -> pp -> seed -> bool) &m :
  0 <= kS => 0 <= kA => 0 <= qT => 0 <= qW =>
  Pr[Theta2L(A).main() @ &m : E AP.out Bwd.p Gen.q Gen.sd \/
       (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq]
  <= Pr[Theta2L(A).main() @ &m : E AP.out Bwd.p Gen.q Gen.sd \/
          (Bwd.p, Gen.q) \in Zset R.RO.m Mon.log Bwd.y WithP.sq]
   + Pr[Theta2L(A).main() @ &m : (Bwd.sts Bwd.p).`early]
   + s1 * kS%r / 2%r ^ 128 + (kA%r / 2%r ^ 128 + kA%r / 2%r ^ 256) + (qT%r + qW%r) / 2%r ^ 512.
proof.
move=> hkS hkA hqT hqW.
have hN := bad_S_N &m hkS.
have hC := W4 &m hkA.
have hT := bad_TW &m hqT hqW.
have hF := facts_theta &m.
have h : Pr[Theta2L(A).main() @ &m : E AP.out Bwd.p Gen.q Gen.sd \/
             (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq] <=
         Pr[Theta2L(A).main() @ &m :
           ((E AP.out Bwd.p Gen.q Gen.sd \/ (Bwd.p, Gen.q) \in Zset R.RO.m Mon.log Bwd.y WithP.sq) \/
            (Bwd.sts Bwd.p).`early) \/
           (((res, Gen.q) \in WithP.sq /\ !(Bwd.sts Bwd.p).`early /\
             !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log)) \/
            (coll R.RO.m Mon.log Bwd.p Bwd.y /\ !(Bwd.sts Bwd.p).`early /\
             last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log)) \/
           ((Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq) \/
            !(inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
              (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs) /\
              (!(Bwd.sts Bwd.p).`early => comp (Bwd.sts Bwd.p).`chain Mon.log =>
                 12 <= count (isApw Bwd.p) (undup (map fst Mon.log)))))].
- rewrite Pr[mu_sub] => // &hr.
  case: (inv true false R.RO.m{hr} Mon.log{hr} Mon.bn{hr} Bwd.p{hr} (cbwd Bwd.y{hr}) (Bwd.sts{hr} Bwd.p{hr}) /\
         (!(Bwd.sts{hr} Bwd.p{hr}).`early => (Bwd.sts{hr} Bwd.p{hr}).`fin /\ res{hr} = (Bwd.sts{hr} Bwd.p{hr}).`xs) /\
         (!(Bwd.sts{hr} Bwd.p{hr}).`early => comp (Bwd.sts{hr} Bwd.p{hr}).`chain Mon.log{hr} =>
            12 <= count (isApw Bwd.p{hr}) (undup (map fst Mon.log{hr})))) => hf; last by smt().
  have [hi [he hcomp]] := hf.
  case: ((Bwd.sts{hr} Bwd.p{hr}).`early) => hea; 1: smt().
  case: (last witness (Bwd.sts{hr} Bwd.p{hr}).`chain \in map fst Mon.log{hr}) => hl; last by smt().
  case: (coll R.RO.m{hr} Mon.log{hr} Bwd.p{hr} Bwd.y{hr}) => hc; 1: smt().
  move=> [hE | [hS | hTW]]; [smt() | | smt()].
  have [_ [_ [hsh hne]]] := hi; have [hord [_ [_ [_ hdet]]]] := hne hea; have [hfin hres] := he hea.
  have [_ [hcne _]] := hsh.
  have hz := Z_incl R.RO.m{hr} Mon.log{hr} Bwd.p{hr} Bwd.y{hr} (Bwd.sts{hr} Bwd.p{hr}) WithP.sq{hr} Gen.q{hr}
               hea hfin (determined_chain _ _ _ _ hdet) hord hcne (hcomp hea) hl _ hc.
  + by rewrite -hres.
  by left; left; right.
move: h hT; do ! rewrite Pr[mu_or]; rewrite hF; smt(mu_bounded).
qed.

(* The seed is drawn last in Θ2. *)
local lemma seed_guess &m : Pr[Theta2L(A).main() @ &m : AP.out.`1 = Gen.sd] <= inv (2%r ^ 512).
proof.
byphoare => //; proc.
seq 2 : true 1%r (inv (2%r ^ 512)) 0%r 0%r => //.
rnd; last by move=> _; smt(expr_gt0 invr_gt0).
skip => &hr _; split; 2: by move=> _ v _ /=.
by rewrite (mu_eq _ _ (pred1 AP.out{hr}.`1)) 1:/# dseed1.
qed.

(* Early_P in Θ2: Lemma G3 for the adversary with its own S, T and Omega. *)
local lemma theta_early &m : 0 <= kA => 0 <= qB => 0 <= qH =>
  Pr[Theta2L(A).main() @ &m : (Bwd.sts Bwd.p).`early] <=
    (12%r * p1 * kA%r + 66%r + qB%r) / 2%r ^ 128 + qH%r / 2%r ^ 256.
proof.
move=> hkA hqB hqH.
have -> := pr_theta_cg (fun (m : (point, ans) fmap) (log : (point * int) list) (p : pw) (y : state)
                            (sts : pw -> cst) (ca : int) => (sts p).`early) &m.
by apply (G3 kA qB qH (AP(A)) _ &m) => // O; conseq (AP_bounded O).
qed.

(* Bad in Θ2, for any budget of the run under which Z weighs at most T. *)
local lemma theta_bad_gen (Bud : int -> int -> bool) (T : real) &m :
  hoare [ChainGame(AP(A)).main : true ==> Bud (size WithP.sq) (count isA (map fst Mon.log))] =>
  (forall log (m : (point, ans) fmap) y sq, Bud (size sq) (count isA (map fst log)) =>
     mass2 (Zset m log y sq) <= T) =>
  0%r <= T => 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[Theta2L(A).main() @ &m : (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq] <=
    T + (s1 * kS%r + qB%r + (1%r + 12%r * p1) * kA%r + 66%r) / 2%r ^ 128 +
    (qH%r + kA%r) / 2%r ^ 256 + (qT%r + qW%r) / 2%r ^ 512.
proof.
move=> hB hZ hT hkA hqB hqH hkS hqT hqW.
have h3 := theta2_split (fun _ _ _ _ => false) &m hkS hkA hqT hqW.
have h4 := top2_pr Bud (fun log m y sq (_ : seed * (pw * pp)) => Zset m log y sq) T &m hB _ _ hT.
- move=> log m y sq out hb /=; have [hu _] := Zset_props m log y sq.
  by rewrite undup_id //; apply hZ.
- by move=> log m m' y sq out hagr hlm /=; apply Zset_ext.
have h5 := theta_early &m hkA hqB hqH.
by move: h3 h4 h5 => /=; smt().
qed.

(* Bad in Θ2: a query of S at (e*, Q), or of T or Omega at seed*. *)
lemma theta_bad &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[Theta2L(A).main() @ &m : (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq] <=
    top2 (kA %/ 12) kS + (s1 * kS%r + qB%r + (1%r + 12%r * p1) * kA%r + 66%r) / 2%r ^ 128 +
    (qH%r + kA%r) / 2%r ^ 256 + (qT%r + qW%r) / 2%r ^ 512.
proof.
move=> hkA hqB hqH hkS hqT hqW.
apply (theta_bad_gen (fun s a => s <= kS /\ a <= kA) (top2 (kA %/ 12) kS) &m _ _ (top2_ge0 _ _)
         hkA hqB hqH hkS hqT hqW).
- by conseq theta_budget (log_count (AP(A))) => /#.
by move=> log m y sq [hs hc]; apply Zset_mass.
qed.

(* ---- From Θ0 to Θ1 ------------------------------------------------------------------------------ *)
local lemma IP_ll : islossless CountP(IP).a /\ islossless CountP(IP).b /\ islossless CountP(IP).h /\
                    islossless CountP(IP).s /\ islossless CountP(IP).t /\ islossless CountP(IP).w.
proof.
do! split; 1..3: by proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />; smt(dseed_ll).
- by proc; inline *; auto => />; smt(dct_ll).
by proc; inline *; auto => />; smt(ddata_ll).
qed.

local lemma guess_ll : islossless A(CountP(IP)).guess.
proof. by have [? [? [? [? [? ?]]]]] := IP_ll; apply (A_ll (CountP(IP))). qed.



(* From Θ0 with the cut rule to Θ1 (Lemmas W2 and W3) for an event of the output and the secrets. *)
local lemma gen_out (E : seed * (pw * pp) -> pw -> pp -> state -> seed -> bool) &m : 0 <= kS => 0 <= qT =>
  Pr[GameP(Setup0P(Seq), A).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd] <=
  Pr[GameP(Setup1P, A).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd] + deltacut kS qT.
proof.
move=> hkS hqT; have := theta01_out kS qT E A _ A_ll &m hkS hqT; 2: smt().
by move=> O; conseq (A_bounded O) => /#.
qed.

(* Theorem 5 for the rule cut off after ntr trials and without refusal; Theorem5R below states it for
   every covered rule with refusal. *)
lemma theorem5_seed_cut &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GameP(Setup0P(Seq), A).main() @ &m : res.`1 = Gen.sd] <=
    top2 (kA %/ 12) kS + epsC kA kS qB qH qT qW + deltacut kS qT + inv (2%r ^ 512).
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := gen_out (fun (out : seed * (pw * pp)) _ _ _ (sd : seed) => out.`1 = sd) &m hkS hqT.
have h2 := upto_bad_theta (fun _ (out : seed * (pw * pp)) _ _ _ (sd : seed) => out.`1 = sd) &m.
have h3 : Pr[Theta2L(A).main() @ &m : AP.out.`1 = Gen.sd \/
                (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq] <=
          Pr[Theta2L(A).main() @ &m : AP.out.`1 = Gen.sd] +
          Pr[Theta2L(A).main() @ &m : (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have h4 := seed_guess &m.
have h5 := theta_bad &m hkA hqB hqH hkS hqT hqW.
move: h1 h2 h3 h4 h5; rewrite /epsC /=; smt().
qed.

(* One cost budget, for the cut rule without refusal: T bounds top2 over the pairs (m, n) that the
   budget allows, 12 cA m + cS n <= c. *)
lemma theorem5_seed_cost_cut (cA cS c T : real) &m :
  (forall (O <: OraclesP {-Count, -CountP, -A}),
     hoare [A(CountP(O)).guess :
       Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
       cA * Count.ca%r + cS * CountP.cs%r <= c]) =>
  0%r <= cA => 0%r <= T =>
  (forall (m n : int), 0 <= m => 0 <= n => 12%r * cA * m%r + cS * n%r <= c => top2 m n <= T) =>
  0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GameP(Setup0P(Seq), A).main() @ &m : res.`1 = Gen.sd] <=
    T + epsC kA kS qB qH qT qW + deltacut kS qT + inv (2%r ^ 512).
proof.
move=> hcost hcA hT hTm hkA hqB hqH hkS hqT hqW.
have h1 := gen_out (fun (out : seed * (pw * pp)) _ _ _ (sd : seed) => out.`1 = sd) &m hkS hqT.
have h2 := upto_bad_theta (fun _ (out : seed * (pw * pp)) _ _ _ (sd : seed) => out.`1 = sd) &m.
have h3 : Pr[Theta2L(A).main() @ &m : AP.out.`1 = Gen.sd \/
                (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq] <=
          Pr[Theta2L(A).main() @ &m : AP.out.`1 = Gen.sd] +
          Pr[Theta2L(A).main() @ &m : (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.tq \/ Gen.sd \in WithP.wq].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have h4 := seed_guess &m.
have h5 := theta_bad_gen (fun (s a : int) => cA * a%r + cS * s%r <= c) T &m _ _ hT hkA hqB hqH hkS hqT hqW.
- conseq (theta_cost cA cS c hcost) (log_count (AP(A))) => // &hr /> log ca sq hc hl.
  have : cA * (count isA (unzip1 log))%r <= cA * ca%r by apply ler_wpmul2l => //; smt().
  smt().
- move=> log m y sq /= hb.
  apply (ler_trans _ _ _ (Zset_mass m log y sq (count isA (map fst log)) (size sq) _ _)) => //.
  have h12 := lez_floor (count isA (map fst log)) 12 _ => //.
  apply hTm; 1,2: smt(size_ge0 count_ge0 divz_ge0).
  have hx : cA * ((count isA (map fst log) %/ 12) * 12)%r <= cA * (count isA (map fst log))%r.
  + by apply ler_wpmul2l => //; rewrite le_fromint.
  have e : ((count isA (map fst log) %/ 12) * 12)%r = (count isA (map fst log) %/ 12)%r * 12%r.
  + by rewrite fromintM.
  smt().
move: h1 h2 h3 h4 h5; rewrite /epsC /=; smt().
qed.

lemma theorem5_pair_cut &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GameP(Setup0P(Seq), A).main() @ &m : res.`2 = (Gen.p, Gen.q)] <=
    minr (top2 (kA %/ 12 + 1) (kS + 1)) (top2 (kA %/ 12) kS + p1 * s1) + epsC kA kS qB qH qT qW +
    deltacut kS qT.
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := gen_out (fun (out : seed * (pw * pp)) (p : pw) (q : pp) _ _ => out.`2 = (p, q)) &m hkS hqT.
have h2 := upto_bad_theta (fun _ (out : seed * (pw * pp)) (p : pw) (q : pp) _ _ => out.`2 = (p, q)) &m.
have h3 := theta2_split (fun (out : seed * (pw * pp)) (p : pw) (q : pp) (_ : seed) => out.`2 = (p, q)) &m hkS hkA hqT hqW.
have h4 : Pr[Theta2L(A).main() @ &m : AP.out.`2 = (Bwd.p, Gen.q) \/ (Bwd.p, Gen.q) \in Zset R.RO.m Mon.log Bwd.y WithP.sq] <=
          minr (top2 (kA %/ 12 + 1) (kS + 1)) (top2 (kA %/ 12) kS + p1 * s1).
- have -> : Pr[Theta2L(A).main() @ &m : AP.out.`2 = (Bwd.p, Gen.q) \/ (Bwd.p, Gen.q) \in Zset R.RO.m Mon.log Bwd.y WithP.sq] =
            Pr[Theta2L(A).main() @ &m : (Bwd.p, Gen.q) \in AP.out.`2 :: Zset R.RO.m Mon.log Bwd.y WithP.sq].
  + by rewrite Pr[mu_eq] => // &hr /=; rewrite eq_sym.
  apply (top2_prK (fun log m y sq (out : seed * (pw * pp)) => out.`2 :: Zset m log y sq) _ &m) => /=.
  + move=> log m y sq out hs hc; have [hu [hsz hcz]] := Zset_props m log y sq.
    have hmz := Zset_mass m log y sq kA kS hc hs.
    have hcs : size (cands log) <= kA %/ 12 by have := cands_size log; rewrite lez_divRL //; smt().
    have hA : mass2 (undup (out.`2 :: Zset m log y sq)) <= top2 (kA %/ 12 + 1) (kS + 1).
    * apply W1; 1: by apply undup_uniq.
      - by apply (IntOrder.ler_trans _ _ _ (size_undup _)); rewrite /=; smt().
      apply (IntOrder.ler_trans (size (out.`2.`1 :: cands log))); last by rewrite /=; smt().
      apply (IntOrder.ler_trans (size (undup (out.`2.`1 :: cands log)))); 2: by apply size_undup.
      apply uniq_leq_size; 1: by apply undup_uniq.
      move=> u; rewrite mem_undup mapP => -[z [hz ->]]; rewrite mem_undup /=.
      by move: hz; rewrite mem_undup /= => -[-> | /hcz ->] //=; right.
    have hB : mass2 (undup (out.`2 :: Zset m log y sq)) <= top2 (kA %/ 12) kS + p1 * s1.
    * apply (ler_trans _ _ _ (mass2_cons _ _)); rewrite undup_id //.
      have : mu1 dP out.`2.`1 * mu1 dQ out.`2.`2 <= p1 * s1.
      - by apply ler_pmul; [apply ge0_mu | apply ge0_mu | apply mu1_p1 | apply mu1_s1].
      smt().
    by rewrite /minr; smt().
  + by move=> log m m' y sq hagr hlm; apply Zset_ext.
  smt(top2_ge0 p1_ge0 s1_ge0).
have h5 := theta_early &m hkA hqB hqH.
move: h1 h2 h3 h4 h5; rewrite /epsC /=; smt().
qed.

(* ---- Corollary W6: Θ1 without the programmed check value ------------------------------------ *)
local equiv upto_thetaO : GameP(Setup1O, A).main ~ G2L.main :
  ={glob A} ==>
  !((Gen.e, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.wq){2} => ={res, glob A, Gen.p, Gen.q, Gen.e, Gen.sd}.
proof.
proc; inline Setup1O.run Setup2P.run.
call (_ : (Gen.e, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.wq,
          ={R.RO.m, RT.RO.m, Gen.p, Gen.q, Gen.e, Gen.sd} /\
          eq_except (pred1 (Gen.e, Gen.q){2}) RS.RO.m{1} RS.RO.m{2} /\ ((Gen.e, Gen.q) \notin RS.RO.m){2} /\
          eq_except (pred1 Gen.sd{2}) RW.RO.m{1} RW.RO.m{2} /\ (Gen.sd \notin RW.RO.m){2}).
- exact A_ll.
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dans_ll).
- by move=> &1; proc; inline *; auto => />; smt(dans_ll).
- proc; inline *; case ((e, q){2} = (Gen.e, Gen.q){2}).
  + by auto => />; smt(mem_rcons).
  by auto => />; smt(eq_exceptP eq_except_set_eq mem_set get_setE mem_rcons domE).
- by move=> &2 _; proc; inline *; auto => />; smt(dseed_ll).
- by move=> &1; proc; inline *; auto => />; smt(dseed_ll mem_rcons).
- by proc; inline *; auto => />.
- by move=> &2 _; proc; inline *; auto => />; smt(dct_ll).
- by move=> &1; proc; inline *; auto => />; smt(dct_ll).
- proc; inline *; case (d{2} = Gen.sd{2}).
  + by auto => />; smt(mem_rcons).
  by auto => />; smt(eq_exceptP eq_except_set_eq mem_set get_setE mem_rcons domE).
- by move=> &2 _; proc; inline *; auto => />; smt(ddata_ll).
- by move=> &1; proc; inline *; auto => />; smt(ddata_ll mem_rcons).
inline CountP(IP).init CountP(IPL).init Count(IP).init Count(IPL).init RS.RO.set RW.RO.set.
wp.
call (_ : ={R.RO.m}); 1: by sim.
by inline *; auto => />; smt(eq_except_setl mem_empty).
qed.

local lemma theta2_splitO (E : seed * (pw * pp) -> pw -> pp -> seed -> bool) &m :
  0 <= kS => 0 <= kA => 0 <= qW =>
  Pr[Theta2L(A).main() @ &m : E AP.out Bwd.p Gen.q Gen.sd \/
       (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.wq]
  <= Pr[Theta2L(A).main() @ &m : E AP.out Bwd.p Gen.q Gen.sd \/
          (Bwd.p, Gen.q) \in Zset R.RO.m Mon.log Bwd.y WithP.sq]
   + Pr[Theta2L(A).main() @ &m : (Bwd.sts Bwd.p).`early]
   + s1 * kS%r / 2%r ^ 128 + (kA%r / 2%r ^ 128 + kA%r / 2%r ^ 256) + qW%r / 2%r ^ 512.
proof.
move=> hkS hkA hqW.
have hN := bad_S_N &m hkS.
have hC := W4 &m hkA.
have hT := bad_W &m hqW.
have hF := facts_theta &m.
have h : Pr[Theta2L(A).main() @ &m : E AP.out Bwd.p Gen.q Gen.sd \/
             (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.wq] <=
         Pr[Theta2L(A).main() @ &m :
           ((E AP.out Bwd.p Gen.q Gen.sd \/ (Bwd.p, Gen.q) \in Zset R.RO.m Mon.log Bwd.y WithP.sq) \/
            (Bwd.sts Bwd.p).`early) \/
           (((res, Gen.q) \in WithP.sq /\ !(Bwd.sts Bwd.p).`early /\
             !(last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log)) \/
            (coll R.RO.m Mon.log Bwd.p Bwd.y /\ !(Bwd.sts Bwd.p).`early /\
             last witness (Bwd.sts Bwd.p).`chain \in map fst Mon.log)) \/
           (Gen.sd \in WithP.wq \/
            !(inv true false R.RO.m Mon.log Mon.bn Bwd.p (cbwd Bwd.y) (Bwd.sts Bwd.p) /\
              (!(Bwd.sts Bwd.p).`early => (Bwd.sts Bwd.p).`fin /\ res = (Bwd.sts Bwd.p).`xs) /\
              (!(Bwd.sts Bwd.p).`early => comp (Bwd.sts Bwd.p).`chain Mon.log =>
                 12 <= count (isApw Bwd.p) (undup (map fst Mon.log)))))].
- rewrite Pr[mu_sub] => // &hr.
  case: (inv true false R.RO.m{hr} Mon.log{hr} Mon.bn{hr} Bwd.p{hr} (cbwd Bwd.y{hr}) (Bwd.sts{hr} Bwd.p{hr}) /\
         (!(Bwd.sts{hr} Bwd.p{hr}).`early => (Bwd.sts{hr} Bwd.p{hr}).`fin /\ res{hr} = (Bwd.sts{hr} Bwd.p{hr}).`xs) /\
         (!(Bwd.sts{hr} Bwd.p{hr}).`early => comp (Bwd.sts{hr} Bwd.p{hr}).`chain Mon.log{hr} =>
            12 <= count (isApw Bwd.p{hr}) (undup (map fst Mon.log{hr})))) => hf; last by smt().
  have [hi [he hcomp]] := hf.
  case: ((Bwd.sts{hr} Bwd.p{hr}).`early) => hea; 1: smt().
  case: (last witness (Bwd.sts{hr} Bwd.p{hr}).`chain \in map fst Mon.log{hr}) => hl; last by smt().
  case: (coll R.RO.m{hr} Mon.log{hr} Bwd.p{hr} Bwd.y{hr}) => hc; 1: smt().
  move=> [hE | [hS | hTW]]; [smt() | | smt()].
  have [_ [_ [hsh hne]]] := hi; have [hord [_ [_ [_ hdet]]]] := hne hea; have [hfin hres] := he hea.
  have [_ [hcne _]] := hsh.
  have hz := Z_incl R.RO.m{hr} Mon.log{hr} Bwd.p{hr} Bwd.y{hr} (Bwd.sts{hr} Bwd.p{hr}) WithP.sq{hr} Gen.q{hr}
               hea hfin (determined_chain _ _ _ _ hdet) hord hcne (hcomp hea) hl _ hc.
  + by rewrite -hres.
  by left; left; right.
move: h hT; do ! rewrite Pr[mu_or]; rewrite hF; smt(mu_bounded).
qed.

lemma upto_bad_thetaO (F : glob A -> seed * (pw * pp) -> pw -> pp -> state -> seed -> bool) &m :
  Pr[GameP(Setup1O, A).main() @ &m : F (glob A) res Gen.p Gen.q Gen.e Gen.sd] <=
  Pr[Theta2L(A).main() @ &m : F (glob A) AP.out Bwd.p Gen.q res Gen.sd \/ (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.wq].
proof.
rewrite -(lazy_thetaX (fun (g : glob A) (out : seed * (pw * pp)) (p : pw) (q : pp) (e : state) (sd : seed)
                          (sq : (state * pp) list) (_ : seed list) (wq : seed list) =>
                          F g out p q e sd \/ (e, q) \in sq \/ sd \in wq) &m) /=.
by byequiv upto_thetaO => // /#.
qed.

lemma theta_badO &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qW =>
  Pr[Theta2L(A).main() @ &m : (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.wq] <=
    top2 (kA %/ 12) kS + (s1 * kS%r + qB%r + (1%r + 12%r * p1) * kA%r + 66%r) / 2%r ^ 128 +
    (qH%r + kA%r) / 2%r ^ 256 + qW%r / 2%r ^ 512.
proof.
move=> hkA hqB hqH hkS hqW.
have h3 := theta2_splitO (fun _ _ _ _ => false) &m hkS hkA hqW.
have h4 := top2_prK (fun log m y sq (_ : seed * (pw * pp)) => Zset m log y sq) (top2 (kA %/ 12) kS) &m _ _ (top2_ge0 _ _).
- move=> log m y sq out hs hc /=; have [hu _] := Zset_props m log y sq.
  by rewrite undup_id //; apply Zset_mass.
- by move=> log m m' y sq out hagr hlm /=; apply Zset_ext.
have h5 := theta_early &m hkA hqB hqH.
by move: h3 h4 h5 => /=; smt().
qed.

lemma theorem5O_seed &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qW =>
  Pr[GameP(Setup1O, A).main() @ &m : res.`1 = Gen.sd] <=
    top2 (kA %/ 12) kS + (s1 * kS%r + qB%r + (1%r + 12%r * p1) * kA%r + 66%r) / 2%r ^ 128 +
    (qH%r + kA%r) / 2%r ^ 256 + qW%r / 2%r ^ 512 + inv (2%r ^ 512).
proof.
move=> hkA hqB hqH hkS hqW.
have h2 := upto_bad_thetaO (fun _ (out : seed * (pw * pp)) _ _ _ (sd : seed) => out.`1 = sd) &m.
have h3 : Pr[Theta2L(A).main() @ &m : AP.out.`1 = Gen.sd \/ (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.wq] <=
          Pr[Theta2L(A).main() @ &m : AP.out.`1 = Gen.sd] +
          Pr[Theta2L(A).main() @ &m : (res, Gen.q) \in WithP.sq \/ Gen.sd \in WithP.wq].
- by rewrite Pr[mu_or]; smt(mu_bounded).
have h4 := seed_guess &m.
have h5 := theta_badO &m hkA hqB hqH hkS hqW.
by move: h2 h3 h4 h5 => /=; smt().
qed.

lemma theorem5O_pair &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qW =>
  Pr[GameP(Setup1O, A).main() @ &m : res.`2 = (Gen.p, Gen.q)] <=
    minr (top2 (kA %/ 12 + 1) (kS + 1)) (top2 (kA %/ 12) kS + p1 * s1) +
    (s1 * kS%r + qB%r + (1%r + 12%r * p1) * kA%r + 66%r) / 2%r ^ 128 + (qH%r + kA%r) / 2%r ^ 256 + qW%r / 2%r ^ 512.
proof.
move=> hkA hqB hqH hkS hqW.
have h2 := upto_bad_thetaO (fun _ (out : seed * (pw * pp)) (p : pw) (q : pp) _ _ => out.`2 = (p, q)) &m.
have h3 := theta2_splitO (fun (out : seed * (pw * pp)) (p : pw) (q : pp) (_ : seed) => out.`2 = (p, q)) &m hkS hkA hqW.
have h4 : Pr[Theta2L(A).main() @ &m : AP.out.`2 = (Bwd.p, Gen.q) \/ (Bwd.p, Gen.q) \in Zset R.RO.m Mon.log Bwd.y WithP.sq] <=
          minr (top2 (kA %/ 12 + 1) (kS + 1)) (top2 (kA %/ 12) kS + p1 * s1).
- have -> : Pr[Theta2L(A).main() @ &m : AP.out.`2 = (Bwd.p, Gen.q) \/ (Bwd.p, Gen.q) \in Zset R.RO.m Mon.log Bwd.y WithP.sq] =
            Pr[Theta2L(A).main() @ &m : (Bwd.p, Gen.q) \in AP.out.`2 :: Zset R.RO.m Mon.log Bwd.y WithP.sq].
  + by rewrite Pr[mu_eq] => // &hr /=; rewrite eq_sym.
  apply (top2_prK (fun log m y sq (out : seed * (pw * pp)) => out.`2 :: Zset m log y sq) _ &m) => /=.
  + move=> log m y sq out hs hc; have [hu [hsz hcz]] := Zset_props m log y sq.
    have hmz := Zset_mass m log y sq kA kS hc hs.
    have hcs : size (cands log) <= kA %/ 12 by have := cands_size log; rewrite lez_divRL //; smt().
    have hA : mass2 (undup (out.`2 :: Zset m log y sq)) <= top2 (kA %/ 12 + 1) (kS + 1).
    * apply W1; 1: by apply undup_uniq.
      - by apply (IntOrder.ler_trans _ _ _ (size_undup _)); rewrite /=; smt().
      apply (IntOrder.ler_trans (size (out.`2.`1 :: cands log))); last by rewrite /=; smt().
      apply (IntOrder.ler_trans (size (undup (out.`2.`1 :: cands log)))); 2: by apply size_undup.
      apply uniq_leq_size; 1: by apply undup_uniq.
      move=> u; rewrite mem_undup mapP => -[z [hz ->]]; rewrite mem_undup /=.
      by move: hz; rewrite mem_undup /= => -[-> | /hcz ->] //=; right.
    have hB : mass2 (undup (out.`2 :: Zset m log y sq)) <= top2 (kA %/ 12) kS + p1 * s1.
    * apply (ler_trans _ _ _ (mass2_cons _ _)); rewrite undup_id //.
      have : mu1 dP out.`2.`1 * mu1 dQ out.`2.`2 <= p1 * s1.
      - by apply ler_pmul; [apply ge0_mu | apply ge0_mu | apply mu1_p1 | apply mu1_s1].
      smt().
    by rewrite /minr; smt().
  + by move=> log m m' y sq hagr hlm; apply Zset_ext.
  smt(top2_ge0 p1_ge0 s1_ge0).
have h5 := theta_early &m hkA hqB hqH.
move: h2 h3 h4 h5 => /=; smt().
qed.

end section Theorem5.

(* ---- A known passphrase (A.6): s_1 = 1 and top2(m, n) = top(min(m, n)) -------------------------- *)
(* Every other passphrase has probability 0. *)
lemma sr_known (j : int) : s1 = 1%r => 2 <= j => sr j = 0%r.
proof.
move=> h1 hj; rewrite /sr; case: (1 <= j <= size rankedQ) => // hjs.
have hu : uniq rankedQ by rewrite /rankedQ sort_uniq PpT.enum_uniq.
have hne : nth witness rankedQ (j - 1) <> nth witness rankedQ 0.
- by move/(nth_uniqP rankedQ) : hu => h; apply h; smt().
have h0 : mu1 dQ (nth witness rankedQ 0) = 1%r by move: h1; rewrite /s1 /sr; smt().
have := mu_disjoint dQ (pred1 (nth witness rankedQ 0)) (pred1 (nth witness rankedQ (j - 1))) _.
- by move=> x; rewrite /predI /pred1 /pred0 /#.
smt(le1_mu ge0_mu).
qed.

lemma top2_known (m n : int) : s1 = 1%r => 0 <= m => 0 <= n => top2 m n = top (min m n).
proof.
move=> h1 hm hn.
have hsz : 1 <= size rankedQ by move: h1; rewrite /s1 /sr; smt().
pose P := allpairs (fun i j => (i, j)) (iota_ 1 m) (iota_ 1 (size rankedQ)).
pose f := fun (y : int * int) => pr y.`1 * sr y.`2.
have -> : top2 m n = big predT idfun (take n (sort (fun (a b : real) => b <= a) (map f P))).
- by rewrite /top2 /P allpairs_mapE.
have hP : uniq P by apply allpairs_uniq; [apply iota_uniq | apply iota_uniq | smt()].
have hf : forall (y : int * int), y \in P => f y = if y.`2 = 1 then pr y.`1 else 0%r.
- move=> [i j] /allpairsP [[i' j'] /= [_ [/mem_iota hj [-> ->]]]]; rewrite /f /=.
  case: (j' = 1) => [-> | hj1]; 1: by rewrite -/s1 h1.
  by rewrite sr_known //; smt().
apply ler_anti; split => [|_].
- (* the n largest products are those of at most min(m, n) distinct passwords with v_1 *)
  have [I [hIu [hIP [hIn ->]]]] := top_sum_ex f P n hP hn.
  pose J := map (fun (y : int * int) => y.`1 - 1) (filter (fun (y : int * int) => y.`2 = 1) I).
  have -> : big predT f I = big predT (fun i => pr (i + 1)) J.
  + rewrite /J big_map big_filter (big_mkcond (fun (y : int * int) => y.`2 = 1)).
    by apply eq_big_seq => y hy; rewrite /(\o) /= hf 1:hIP.
  have hJu : uniq J.
  + rewrite /J map_inj_in_uniq; 2: by apply filter_uniq.
    by move=> x y; rewrite !mem_filter /= => -[hx _] [hy _] heq; rewrite (pairS x) (pairS y) hx hy; smt().
  have hJm : forall i, i \in J => 0 <= i < m.
  + move=> i /mapP [y [hy ->]] /=; move: hy; rewrite mem_filter => -[_ /hIP].
    by move=> /allpairsP [[i' j'] /= [/mem_iota hi [_ ->]]] /=; smt().
  have hsJ : size J <= min m n.
  + have h1' : size J <= n by rewrite /J size_map size_filter; smt(count_size).
    have := uniq_leq_size J (iota_ 0 m) hJu _; 1: by move=> i /hJm hi; rewrite mem_iota; smt().
    by rewrite size_iota; smt().
  have := sum_distinct_le (fun i => pr (i + 1)) J _ hJu _.
  + by move=> i j hij /=; apply pr_mono; smt().
  + by move=> i /hJm; smt().
  by rewrite -top_shift; have := top_mono (size J) (min m n) hsJ; smt().
(* the pairs (w_i, v_1) for i <= min(m, n) are among the candidates *)
pose K := map (fun i => (i, 1)) (iota_ 1 (min m n)).
have := top_sum f K P n _ _ _ _.
- by rewrite /K map_inj_in_uniq ?iota_uniq // => i j _ _ /= [].
- move=> y /mapP [i [/mem_iota hi ->]]; rewrite /P allpairsP; exists (i, 1) => /=.
  by rewrite !mem_iota; smt().
- by rewrite /K size_map size_iota; smt().
- by move=> y _; rewrite /f; apply mulr_ge0; [apply pr_ge0 | apply sr_ge0].
have -> // : big predT f K = top (min m n).
rewrite /K big_map /top /range /=.
by apply eq_big_seq => i hi; rewrite /(\o) /f /= -/s1 h1.
qed.

(* ---- Theorem 5 for every covered rule, in particular the sequential rule of the specification --- *)
section Theorem5R.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op kS : int.
declare op qT : int.
declare op qW : int.

declare module Rl <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                           -Trials, -Gen, -Count, -CountP}.
declare axiom Rl_pass (T <: TRIALS {-Rl, -Trials}) :
  hoare [Rl(Rec(T)).select : Trials.outs = [] ==>
           0 <= res < size Trials.outs /\ nth false Trials.outs res].
declare axiom Rl_ll (T <: TRIALS {-Rl}) (P : glob T -> bool) (b : real) :
  0%r < b => phoare [T.trial : P (glob T) ==> P (glob T) /\ res] = b =>
  phoare [T.trial : P (glob T) ==> P (glob T)] = 1%r =>
  phoare [Rl(T).select : P (glob T) ==> true] = 1%r.

declare module A <: AdvP {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Gen, -Trials, -Count, -CountB, -CountP, -Mon, -Bwd,
                          -WithP, -AP, -Rl}.
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

(* Theorem 5. *)
lemma theorem5_seed &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GamePR(Setup0P(Rl), A, Rf).main() @ &m : res.`1 = Gen.sd] <=
    top2 (kA %/ 12) kS + epsW kA kS qB qH qT qW + inv (2%r ^ 512).
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := rule_up (fun (out : seed * (pw * pp)) _ _ (sd : seed) => out.`1 = sd)
             Rl Rl_pass Rl_ll A A_ll Rf Rf_ll &m.
have h2 := theorem5_seed_cut kA qB qH kS qT qW A A_bounded A_ll &m hkA hqB hqH hkS hqT hqW.
have h3 := deltacut_le kS qT hkS hqT.
by move: h1 h2 h3; rewrite /epsW /=; smt().
qed.

lemma theorem5_pair &m : 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GamePR(Setup0P(Rl), A, Rf).main() @ &m : res.`2 = (Gen.p, Gen.q)] <=
    minr (top2 (kA %/ 12 + 1) (kS + 1)) (top2 (kA %/ 12) kS + p1 * s1) + epsW kA kS qB qH qT qW.
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := rule_up (fun (out : seed * (pw * pp)) (p : pw) (q : pp) _ => out.`2 = (p, q))
             Rl Rl_pass Rl_ll A A_ll Rf Rf_ll &m.
have h2 := theorem5_pair_cut kA qB qH kS qT qW A A_bounded A_ll &m hkA hqB hqH hkS hqT hqW.
have h3 := deltacut_le kS qT hkS hqT.
by move: h1 h2 h3; rewrite /epsW /=; smt().
qed.

(* A known passphrase: part (b) bounds the recovery of the password, the analogue of Corollary G10
   for a source generated under the profile. *)
lemma theorem5_pair_known &m : s1 = 1%r => 0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GamePR(Setup0P(Rl), A, Rf).main() @ &m : res.`2 = (Gen.p, Gen.q)] <=
    top (min (kA %/ 12) kS + 1) + epsW kA kS qB qH qT qW.
proof.
move=> h1 hkA hqB hqH hkS hqT hqW.
have := theorem5_pair &m hkA hqB hqH hkS hqT hqW.
rewrite (top2_known (kA %/ 12 + 1) (kS + 1) h1) 1,2:/#.
by rewrite (_ : min (kA %/ 12 + 1) (kS + 1) = min (kA %/ 12) kS + 1) 1:/#; smt().
qed.
end section Theorem5R.

(* ---- Theorem 5 for a rule with a limit and a failure -------------------------------------------- *)
(* The sequential rule that stops after n trials and reports a failure (A.6, "Selection rule"), for
   every n: a failed generation creates no container and wins nothing, so parts (a) and (b) hold as
   stated. *)
section Theorem5F.
declare op kA : int.
declare op qB : int.
declare op qH : int.
declare op kS : int.
declare op qT : int.
declare op qW : int.

declare module A <: AdvP {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Gen, -Trials, -Count, -CountB, -CountP, -Mon, -Bwd,
                          -WithP, -AP}.
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

lemma theorem5_seed_capped &m (n : int) :
  0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GameF(A, Rf).main(n) @ &m : res <> None /\ (oget res).`1 = Gen.sd] <=
    top2 (kA %/ 12) kS + epsW kA kS qB qH qT qW + inv (2%r ^ 512).
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := capped_up (fun (out : seed * (pw * pp)) _ _ (sd : seed) => out.`1 = sd)
             SeqU SeqU_pass SeqU_ll A A_ll Rf Rf_ll &m n.
have h2 := theorem5_seed_cut kA qB qH kS qT qW A A_bounded A_ll &m hkA hqB hqH hkS hqT hqW.
have h3 := deltacut_le kS qT hkS hqT.
have h4 : 0%r <= inv (2%r ^ 256) by smt(invr_ge0 expr_ge0).
by move: h1 h2 h3 h4; rewrite /epsW /=; smt().
qed.

lemma theorem5_pair_capped &m (n : int) :
  0 <= kA => 0 <= qB => 0 <= qH => 0 <= kS => 0 <= qT => 0 <= qW =>
  Pr[GameF(A, Rf).main(n) @ &m : res <> None /\ (oget res).`2 = (Gen.p, Gen.q)] <=
    minr (top2 (kA %/ 12 + 1) (kS + 1)) (top2 (kA %/ 12) kS + p1 * s1) + epsW kA kS qB qH qT qW.
proof.
move=> hkA hqB hqH hkS hqT hqW.
have h1 := capped_up (fun (out : seed * (pw * pp)) (p : pw) (q : pp) _ => out.`2 = (p, q))
             SeqU SeqU_pass SeqU_ll A A_ll Rf Rf_ll &m n.
have h2 := theorem5_pair_cut kA qB qH kS qT qW A A_bounded A_ll &m hkA hqB hqH hkS hqT hqW.
have h3 := deltacut_le kS qT hkS hqT.
have h4 : 0%r <= inv (2%r ^ 256) by smt(invr_ge0 expr_ge0).
by move: h1 h2 h3 h4; rewrite /epsW /=; smt().
qed.
end section Theorem5F.

(* ---- Bounds on top2, and independent uniform secrets ------------------------------------------ *)
(* top2(m, n) sums at most min(n, m |Qw|) products, each at most p1 s1. *)
lemma top2_le (m n : int) : 0 <= m => 0 <= n => top2 m n <= (min n (m * size rankedQ))%r * (p1 * s1).
proof.
move=> hm hn; rewrite /top2.
pose S := sort (fun (a b : real) => b <= a)
            (allpairs (fun i j => pr i * sr j) (iota_ 1 m) (iota_ 1 (size rankedQ))).
have hS : forall x, x \in take n S => x <= p1 * s1.
- move=> x /mem_take; rewrite /S mem_sort => /allpairsP [[i j] /= [/mem_iota hi [/mem_iota hj ->]]].
  apply ler_pmul; [exact pr_ge0 | exact sr_ge0 | | ].
  + by rewrite /p1; apply pr_mono; smt().
  by rewrite /s1; apply sr_mono; smt().
have hsz : size (take n S) = min n (m * size rankedQ).
- by rewrite size_take // /S size_sort size_allpairs !size_iota; smt(size_ge0).
apply (ler_trans (big predT (fun _ => p1 * s1) (take n S))).
- by apply Bigreal.ler_sum_seq => x hx _; rewrite /idfun; apply hS.
by rewrite Bigreal.sumr_const count_predT hsz.
qed.

(* N1 equally likely passwords and N2 equally likely passphrases (A.6, "Reading for independent
   uniform secrets"): top2(m, n) <= min(n, m N2) / (N1 N2), so part (a) of Theorem 5 gives at most
   min(k_S, floor(k_A / 12) N2) / (N1 N2) + epsW + 2^-512. *)
lemma top2_uniform (m n : int) :
  (forall w, mu1 dP w = inv PwT.card%r) => (forall v, mu1 dQ v = inv PpT.card%r) => 0 <= m => 0 <= n =>
  top2 m n <= (min n (m * PpT.card))%r / (PwT.card * PpT.card)%r.
proof.
move=> hP hQ hm hn; have := top2_le m n hm hn.
have hN1 : 0 < PwT.card by rewrite /PwT.card; have := PwT.enumP witness; smt(size_eq0 size_ge0).
have hN2 : 0 < PpT.card by rewrite /PpT.card; have := PpT.enumP witness; smt(size_eq0 size_ge0).
have -> : size rankedQ = PpT.card by rewrite /rankedQ size_sort.
have hp1 : p1 <= inv PwT.card%r.
- by rewrite /p1 /pr; case: (1 <= 1 <= size ranked) => _; [rewrite hP | smt(invr_ge0 le_fromint)].
have hs1 : s1 <= inv PpT.card%r.
- by rewrite /s1 /sr; case: (1 <= 1 <= size rankedQ) => _; [rewrite hQ | smt(invr_ge0 le_fromint)].
have : (min n (m * PpT.card))%r * (p1 * s1) <= (min n (m * PpT.card))%r * (inv PwT.card%r * inv PpT.card%r).
- by apply ler_wpmul2l; [smt(le_fromint) | apply ler_pmul => //; smt(p1_ge0 s1_ge0)].
by rewrite fromintM RField.invfM; smt().
qed.

(* The exact value for N1 equally likely passwords and N2 equally likely passphrases (A.6, "Reading
   for independent uniform secrets"): top2(m, n) = min(n, min(m, N1) N2) / (N1 N2). *)
lemma top2_uniform_eq (m n : int) :
  (forall w, mu1 dP w = inv PwT.card%r) => (forall v, mu1 dQ v = inv PpT.card%r) => 0 <= m => 0 <= n =>
  top2 m n = (min n (min m PwT.card * PpT.card))%r / (PwT.card * PpT.card)%r.
proof.
move=> hP hQ hm hn.
have hN1 : 0 < PwT.card by rewrite /PwT.card; have := PwT.enumP witness; smt(size_eq0 size_ge0).
have hN2 : 0 < PpT.card by rewrite /PpT.card; have := PpT.enumP witness; smt(size_eq0 size_ge0).
have sQ : size rankedQ = PpT.card by rewrite /rankedQ size_sort.
have sP : size ranked = PwT.card by rewrite /ranked size_sort.
pose c := inv PwT.card%r * inv PpT.card%r.
pose k := min m PwT.card.
pose f := fun (x : int * int) => pr x.`1 * sr x.`2.
pose pairs := fun (a : int) => allpairs (fun (i j : int) => (i, j)) (iota_ 1 a) (iota_ 1 (size rankedQ)).
have hc : 0%r <= c by rewrite /c; smt(invr_ge0 le_fromint).
have hf : forall x, x \in pairs m => f x = if x.`1 <= PwT.card then c else 0%r.
- move=> x /allpairsP [[i j] /= [/mem_iota hi [/mem_iota hj ->]]] /=.
  rewrite /f /= /pr /sr sP sQ (_ : 1 <= j <= PpT.card) 1:/# /= hQ.
  by case: (i <= PwT.card) => hik /=; [rewrite (_ : 1 <= i) 1:/# /= hP | done].
have hf0 : forall x, x \in pairs m => 0%r <= f x by move=> x hx; rewrite (hf x hx); smt().
have hu : forall a, uniq (pairs a).
- by move=> a; apply allpairs_uniq; [apply iota_uniq | apply iota_uniq | smt()].
have hsz : forall a, 0 <= a => size (pairs a) = a * PpT.card.
- by move=> a ha; rewrite /pairs size_allpairs !size_iota sQ; smt().
have hsub : forall x, x \in pairs k => x \in pairs m.
- move=> x /allpairsP [[i j] /= [/mem_iota hi [hj ->]]].
  by apply/allpairsP; exists (i, j) => /=; rewrite hj mem_iota /#.
have -> : top2 m n = big predT idfun (take n (sort (fun (a b : real) => b <= a) (map f (pairs m)))).
- by rewrite /top2 allpairs_mapE.
have -> : (min n (k * PpT.card))%r / (PwT.card * PpT.card)%r = (min n (k * PpT.card))%r * c.
- by rewrite /c fromintM RField.invfM.
apply ler_anti; split => [| _].
- have [I [uI [sub [szI ->]]]] := top_sum_ex f (pairs m) n (hu m) hn.
  rewrite (eq_big_seq _ (fun (x : int * int) => if x.`1 <= PwT.card then c else 0%r)) => [x hx /= | ]; 1: by apply hf; apply sub.
  rewrite -big_mkcond Bigreal.sumr_const; apply ler_wpmul2r => //; apply le_fromint.
  have h1 : count (fun (x : int * int) => x.`1 <= PwT.card) I <= n by smt(count_size).
  have h2 : count (fun (x : int * int) => x.`1 <= PwT.card) I <= k * PpT.card.
  + rewrite -size_filter -(hsz k) 1:/#; apply uniq_leq_size; 1: by apply filter_uniq.
    move=> x; rewrite mem_filter => -[hx /sub /allpairsP [[i j] /= [/mem_iota hi [hj e]]]].
    by apply/allpairsP; exists (i, j) => /=; rewrite hj mem_iota -e /=; move: hx; rewrite e /= /#.
  smt().
pose I := take n (pairs k).
have uI : uniq I by apply uniq_take; apply hu.
have sI : size I = min n (k * PpT.card) by rewrite /I size_take // hsz /#.
have := top_sum f I (pairs m) n uI _ _ hf0.
- by move=> x /mem_take /hsub.
- smt().
have -> // : big predT f I = (min n (k * PpT.card))%r * c.
rewrite (eq_big_seq _ (fun (_ : int * int) => c)) => [x /mem_take hx /= | ].
- rewrite (hf x (hsub x hx)); move/allpairsP : hx => [[i j] /= [/mem_iota hi [_ ->]]] /=; smt().
by rewrite Bigreal.sumr_const count_predT sI.
qed.

(* One cost budget with uniform secrets: 12 cA m + cS n <= c gives
   min(n, m N2) / (N1 N2) <= c / (N1 (12 cA + N2 cS)). *)
lemma cost_uniform (N1 N2 : int) (cA cS c : real) (m n : int) :
  0 < N1 => 0 < N2 => 0%r < cA => 0%r < cS => 0 <= m => 0 <= n => 12%r * cA * m%r + cS * n%r <= c =>
  (min n (m * N2))%r / (N1 * N2)%r <= c / (N1%r * (12%r * cA + N2%r * cS)).
proof.
move=> hN1 hN2 hcA hcS hm hn hc.
have hN1r : 0%r < N1%r by rewrite lt_fromint.
have hN2r : 0%r < N2%r by rewrite lt_fromint.
have hK : 0%r < 12%r * cA + N2%r * cS by smt().
pose x := (min n (m * N2))%r.
have hx1 : x <= n%r by rewrite /x le_fromint; smt().
have hx2 : x <= m%r * N2%r by rewrite /x -fromintM le_fromint; smt().
have h : x * (12%r * cA + N2%r * cS) <= N2%r * c.
- have h1 : x * (12%r * cA) <= m%r * N2%r * (12%r * cA) by apply ler_wpmul2r => //; smt().
  have h2 : x * (N2%r * cS) <= n%r * (N2%r * cS) by apply ler_wpmul2r => //; smt().
  have h3 : N2%r * (12%r * cA * m%r + cS * n%r) <= N2%r * c by apply ler_wpmul2l => //; smt().
  smt().
have -> : c / (N1%r * (12%r * cA + N2%r * cS)) = N2%r * c / (12%r * cA + N2%r * cS) / (N1 * N2)%r.
- by rewrite fromintM; field; smt().
apply ler_wpmul2r; 1: by rewrite invr_ge0 le_fromint; smt().
by rewrite ler_pdivl_mulr.
qed.

lemma floor_ge (n : int) (x : real) : n%r <= x => n <= floor x.
proof. by move=> h; have := floor_mono _ _ h; rewrite (_ : floor n%r = n) // floorP; smt(). qed.

(* ---- One cost budget, for every covered rule ------------------------------------------------ *)
(* A.6, "One cost budget": an attacker that divides one budget c between Argon2id calls (cost cA each)
   and seed computations (cost cS each), with total cost at most c on every execution. *)
section Theorem5Cost.
declare op cA : real.
declare op cS : real.
declare op c : real.
declare op qB : int.
declare op qH : int.
declare op qT : int.
declare op qW : int.
declare axiom gt0_cA : 0%r < cA.
declare axiom gt0_cS : 0%r < cS.

declare module Rl <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                           -Trials, -Gen, -Count, -CountP}.
declare axiom Rl_pass (T <: TRIALS {-Rl, -Trials}) :
  hoare [Rl(Rec(T)).select : Trials.outs = [] ==>
           0 <= res < size Trials.outs /\ nth false Trials.outs res].
declare axiom Rl_ll (T <: TRIALS {-Rl}) (P : glob T -> bool) (b : real) :
  0%r < b => phoare [T.trial : P (glob T) ==> P (glob T) /\ res] = b =>
  phoare [T.trial : P (glob T) ==> P (glob T)] = 1%r =>
  phoare [Rl(T).select : P (glob T) ==> true] = 1%r.

declare module A <: AdvP {-R.RO, -R.FRO, -RE.FunRO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO,
                          -RTE.FunRO, -RW.RO, -Gen, -Trials, -Count, -CountB, -CountP, -Mon, -Bwd,
                          -WithP, -AP, -Rl}.
declare module Rf <: AFTERP {-Gen}.
declare axiom Rf_ll : islossless Rf.run.
declare axiom A_cost (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    cA * Count.ca%r + cS * CountP.cs%r <= c /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.ct <= qT /\ CountP.cw <= qW].
declare axiom A_ll (O <: OraclesP {-A}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless A(O).guess.

(* The budget allows at most floor(c / cA) Argon2id calls and floor(c / cS) seed computations. *)
local lemma A_bounded_c (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= floor (c / cA) /\ Count.cb <= qB /\ Count.ch <= qH /\
    CountP.cs <= floor (c / cS) /\ CountP.ct <= qT /\ CountP.cw <= qW].
proof.
conseq (A_cost O) (_ : 0 <= Count.ca /\ 0 <= CountP.cs ==> 0 <= Count.ca /\ 0 <= CountP.cs) => [/# | | ].
- move=> &hr _ s cb ch a ct cw [[hc [-> [-> [-> ->]]]] [h0a h0s]] /=.
  have ha : cA * a%r <= c by smt(le_fromint gt0_cS).
  have hs : cS * s%r <= c by smt(le_fromint gt0_cA).
  split; 1: by apply floor_ge; rewrite ler_pdivl_mulr 1:gt0_cA; smt().
  by apply floor_ge; rewrite ler_pdivl_mulr 1:gt0_cS; smt().
by proc (0 <= Count.ca /\ 0 <= CountP.cs) => //; proc; inline *; wp; call (_ : true); auto => /#.
qed.

local lemma A_cost0 (O <: OraclesP {-Count, -CountP, -A}) :
  hoare [A(CountP(O)).guess :
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    cA * Count.ca%r + cS * CountP.cs%r <= c].
proof. by conseq (A_cost O). qed.

(* One cost budget: T bounds top2(m, n) whenever 12 cA m + cS n <= c. *)
lemma theorem5_cost (T : real) &m : 0 <= qB => 0 <= qH => 0 <= qT => 0 <= qW => 0%r <= c => 0%r <= T =>
  (forall (m n : int), 0 <= m => 0 <= n => 12%r * cA * m%r + cS * n%r <= c => top2 m n <= T) =>
  Pr[GamePR(Setup0P(Rl), A, Rf).main() @ &m : res.`1 = Gen.sd] <=
    T + epsW (floor (c / cA)) (floor (c / cS)) qB qH qT qW + inv (2%r ^ 512).
proof.
move=> hqB hqH hqT hqW hc hT hTm.
have hkA : 0 <= floor (c / cA) by apply floor_ge; smt(divr_ge0 gt0_cA).
have hkS : 0 <= floor (c / cS) by apply floor_ge; smt(divr_ge0 gt0_cS).
have h1 := rule_up (fun (out : seed * (pw * pp)) _ _ (sd : seed) => out.`1 = sd) Rl Rl_pass Rl_ll
             A A_ll Rf Rf_ll &m.
have h2 := theorem5_seed_cost_cut (floor (c / cA)) qB qH (floor (c / cS)) qT qW A A_bounded_c A_ll
             cA cS c T &m A_cost0 _ hT hTm hkA hqB hqH hkS hqT hqW; 1: smt(gt0_cA).
have h3 := deltacut_le (floor (c / cS)) qT hkS hqT.
by move: h1 h2 h3; rewrite /epsW /=; smt().
qed.

(* With independent uniform secrets: at most c / (N1 (12 cA + N2 cS)) + epsW + 2^-512. *)
lemma theorem5_cost_uniform &m :
  (forall w, mu1 dP w = inv PwT.card%r) => (forall v, mu1 dQ v = inv PpT.card%r) =>
  0 <= qB => 0 <= qH => 0 <= qT => 0 <= qW => 0%r <= c =>
  Pr[GamePR(Setup0P(Rl), A, Rf).main() @ &m : res.`1 = Gen.sd] <=
    c / (PwT.card%r * (12%r * cA + PpT.card%r * cS)) +
    epsW (floor (c / cA)) (floor (c / cS)) qB qH qT qW + inv (2%r ^ 512).
proof.
move=> hP hQ hqB hqH hqT hqW hc.
have hN1 : 0 < PwT.card by rewrite /PwT.card; have := PwT.enumP witness; smt(size_eq0 size_ge0).
have hN2 : 0 < PpT.card by rewrite /PpT.card; have := PpT.enumP witness; smt(size_eq0 size_ge0).
apply (theorem5_cost (c / (PwT.card%r * (12%r * cA + PpT.card%r * cS))) &m) => //.
- by apply divr_ge0 => //; smt(lt_fromint gt0_cA gt0_cS).
move=> m n hm hn hmn; apply (ler_trans _ _ _ (top2_uniform m n hP hQ hm hn)).
exact (cost_uniform PwT.card PpT.card cA cS c m n hN1 hN2 gt0_cA gt0_cS hm hn hmn).
qed.
end section Theorem5Cost.
