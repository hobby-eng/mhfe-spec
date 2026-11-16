(* Proposition W7: the matching attack on a source generated under the profile (DESIGN-NOTES A.6). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision Passphrase Generation Selection Theta2 Theorem5 W5W6.
require (*--*) PROM.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- Proposition W7: the matching attack ----------------------------------------------------- *)
(* Inverts Y under the passwords of [ws], then goes through the pairs of [pairs] in order and stops at
   the first one whose candidate seed passes the test. Mode 0 tests Omega(sigma) = omega*; mode 1
   tests the 16-bit check; mode 2 tests the check and then Omega after a pass. *)
module MatchP (O : OraclesP) = {
  var ws    : pw list
  var pairs : (pw * pp) list
  var mode  : int
  proc guess(y : state, om : data) : seed * (pw * pp) = {
    var xsl, s11, j, w, i, z, s, k, m, v, sg, c, o, pass, found, out;
    xsl <- [];
    s11 <@ O.b(rd 11, y.`1);
    j <- 0;
    while (j < size ws) {
      w <- nth witness ws j;
      z <- y;
      i <- 11;
      while (0 <= i) {
        if (i = 11) { s <- s11; } else { s <@ O.b(rd i, z.`1); }
        k <@ O.a(w, s);
        m <@ O.h(k, rd i, z.`1);
        z <- unround m z;
        i <- i - 1;
      }
      xsl <- rcons xsl (w, z);
      j <- j + 1;
    }
    found <- false;
    out <- (witness, witness);
    j <- 0;
    while (j < size pairs /\ !found) {
      v <- nth witness pairs j;
      sg <@ O.s(oget (assoc xsl v.`1), v.`2);
      pass <- true;
      if (mode = 1 \/ mode = 2) { c <@ O.t(sg); pass <- c.`1 = zero16; }
      if (pass /\ (mode = 0 \/ mode = 2)) { o <@ O.w(sg); pass <- o = om; }
      if (pass) { found <- true; out <- (sg, v); }
      j <- j + 1;
    }
    return out;
  }
}.

(* The false-match probability of one wrong pair under each test. *)
op tw (mode : int) : real =
  if mode = 0 then inv (2%r ^ lambda) else if mode = 1 then inv (2%r ^ 16) else inv (2%r ^ (lambda + 16)).

lemma W7_budget (O <: OraclesP {-Count, -CountP, -MatchP}) (m n : int) :
  hoare [MatchP(CountP(O)).guess :
    size MatchP.ws = m /\ size MatchP.pairs = n /\ 0 <= MatchP.mode <= 2 /\
    Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0 ==>
    Count.ca <= 12 * m /\ Count.cb <= 11 * m + 1 /\ Count.ch <= 12 * m /\ CountP.cs <= n /\
    (MatchP.mode = 0 => CountP.ct = 0 /\ CountP.cw <= n) /\
    (MatchP.mode = 1 => CountP.ct <= n /\ CountP.cw = 0) /\
    (MatchP.mode = 2 => CountP.ct <= n /\ CountP.cw <= CountP.ct)].
proof.
proc.
while (0 <= j <= n /\ size MatchP.pairs = n /\ 0 <= MatchP.mode <= 2 /\ CountP.cs = j /\
       (MatchP.mode = 0 => CountP.ct = 0 /\ CountP.cw <= j) /\
       (MatchP.mode = 1 => CountP.ct <= j /\ CountP.cw = 0) /\
       (MatchP.mode = 2 => CountP.ct <= j /\ CountP.cw <= CountP.ct) /\
       Count.ca <= 12 * m /\ Count.cb <= 11 * m + 1 /\ Count.ch <= 12 * m).
- inline CountP(O).s CountP(O).t CountP(O).w; sp.
  seq 1 : (0 <= j < n /\ size MatchP.pairs = n /\ 0 <= MatchP.mode <= 2 /\ CountP.cs = j + 1 /\
           (MatchP.mode = 0 => CountP.ct = 0 /\ CountP.cw <= j) /\
           (MatchP.mode = 1 => CountP.ct <= j /\ CountP.cw = 0) /\
           (MatchP.mode = 2 => CountP.ct <= j /\ CountP.cw <= CountP.ct) /\
           Count.ca <= 12 * m /\ Count.cb <= 11 * m + 1 /\ Count.ch <= 12 * m).
  + by call (_ : true); auto => /> /#.
  sp; seq 1 : (0 <= j < n /\ size MatchP.pairs = n /\ 0 <= MatchP.mode <= 2 /\ CountP.cs = j + 1 /\
               (MatchP.mode = 0 => CountP.ct = 0 /\ CountP.cw <= j /\ pass) /\
               (MatchP.mode = 1 => CountP.ct <= j + 1 /\ CountP.cw = 0) /\
               (MatchP.mode = 2 => CountP.ct <= j + 1 /\ CountP.cw + 1 <= CountP.ct) /\
               Count.ca <= 12 * m /\ Count.cb <= 11 * m + 1 /\ Count.ch <= 12 * m).
  + if; 2: by auto => /> /#.
    by wp; call (_ : true); auto => /> /#.
  seq 1 : (0 <= j < n /\ size MatchP.pairs = n /\ 0 <= MatchP.mode <= 2 /\ CountP.cs = j + 1 /\
           (MatchP.mode = 0 => CountP.ct = 0 /\ CountP.cw <= j + 1) /\
           (MatchP.mode = 1 => CountP.ct <= j + 1 /\ CountP.cw = 0) /\
           (MatchP.mode = 2 => CountP.ct <= j + 1 /\ CountP.cw <= CountP.ct) /\
           Count.ca <= 12 * m /\ Count.cb <= 11 * m + 1 /\ Count.ch <= 12 * m).
  + if; 2: by auto => /> /#.
    by wp; call (_ : true); auto => /> /#.
  by auto => /> /#.
wp.
while (0 <= j <= m /\ size MatchP.ws = m /\ size MatchP.pairs = n /\ 0 <= MatchP.mode <= 2 /\
       Count.ca = 12 * j /\ Count.cb = 1 + 11 * j /\ Count.ch = 12 * j /\
       CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0).
- wp.
  while (-1 <= i <= 11 /\ 0 <= j < m /\ size MatchP.ws = m /\ size MatchP.pairs = n /\ 0 <= MatchP.mode <= 2 /\
         Count.ca = 12 * j + (11 - i) /\ Count.cb = 1 + 11 * j + max 0 (10 - i) /\
         Count.ch = 12 * j + (11 - i) /\ CountP.cs = 0 /\ CountP.ct = 0 /\ CountP.cw = 0).
  + inline *; wp; call (_ : true); wp; call (_ : true); wp.
    if; 1: by auto => /> /#.
    by wp; call (_ : true); auto => /> /#.
  by auto => /> /#.
by inline *; wp; call (_ : true); auto => />; smt(size_ge0).
qed.

(* The passes of the 16-bit check among the answers of T. *)
module Passes (O : OraclesP) = {
  var n : int
  proc a = O.a
  proc b = O.b
  proc h = O.h
  proc s = O.s
  proc t(d : seed) = { var c; c <@ O.t(d); if (c.`1 = zero16) n <- n + 1; return c; }
  proc w = O.w
}.

(* With the check first and Omega after a pass (mode 2), q_Omega is the number of passes. *)
lemma W7_passes (O <: OraclesP {-Count, -CountP, -MatchP, -Passes}) :
  hoare [MatchP(CountP(Passes(O))).guess : MatchP.mode = 2 /\ CountP.cw = 0 /\ Passes.n = 0 ==>
    CountP.cw = Passes.n].
proof.
proc.
while (MatchP.mode = 2 /\ CountP.cw = Passes.n).
- inline CountP(Passes(O)).s CountP(Passes(O)).t CountP(Passes(O)).w Passes(O).t; sp.
  seq 1 : (MatchP.mode = 2 /\ CountP.cw = Passes.n); 1: by call (_ : true); auto.
  sp; seq 1 : (MatchP.mode = 2 /\ CountP.cw + b2i pass = Passes.n).
  + rcondt 1; 1: by auto.
    by wp; call (_ : true); auto => /> /#.
  seq 1 : (MatchP.mode = 2 /\ CountP.cw = Passes.n); 2: by auto.
  if; 2: by auto => /> /#.
  by wp; call (_ : true); auto => /> /#.
wp.
while (MatchP.mode = 2 /\ CountP.cw = 0 /\ Passes.n = 0).
- wp.
  while (MatchP.mode = 2 /\ CountP.cw = 0 /\ Passes.n = 0).
  + inline *; wp; call (_ : true); wp; call (_ : true); wp.
    if; 1: by auto.
    by wp; call (_ : true); auto.
  by auto.
by inline *; wp; call (_ : true); auto.
qed.

lemma assoc_mapF ['a 'b] (F : 'a -> 'b) (s : 'a list) x : x \in s => assoc (map (fun w => (w, F w)) s) x = Some (F x).
proof. by elim: s => //= y s ih; rewrite assoc_cons; case: (x = y) => // hne /= /#. qed.

(* All pairs (P, Q), the expectation over them as a sum, and the weight of a list of pairs. *)
op allPQ : (pw * pp) list = allpairs (fun (p : pw) (q : pp) => (p, q)) PwT.enum PpT.enum.

lemma allPQ_uniq : uniq allPQ.
proof. by apply allpairs_uniq; [exact PwT.enum_uniq | exact PpT.enum_uniq | smt()]. qed.

lemma allPQP (z : pw * pp) : z \in allPQ.
proof. by case: z => p q; rewrite allpairsP; exists (p, q); rewrite PwT.enumP PpT.enumP. qed.

lemma Ep_dPQ (f : pw * pp -> real) : (forall z, 0%r <= f z) =>
  Ep dP (fun p => Ep dQ (fun q => (f (p, q))%xr)) =
  (big predT (fun (z : pw * pp) => mu1 dP z.`1 * mu1 dQ z.`2 * f z) allPQ)%xr.
proof.
move=> hf.
have -> : Ep dP (fun p => Ep dQ (fun q => (f (p, q))%xr)) = Ep (dP `*` dQ) (fun z => (f z)%xr).
- rewrite dprod_dlet Ep_dlet; apply eq_Ep => p _ /=.
  by rewrite Ep_dlet; apply eq_Ep => q _ /=; rewrite Ep_dunit.
rewrite (Ep_fin allPQ) ?allPQ_uniq => [z _ | ]; 1: by apply allPQP.
rewrite (BXA.eq_bigr _ _ (fun (z : pw * pp) => (mu1 dP z.`1 * mu1 dQ z.`2 * f z)%xr)) => [[p q] _ /= | ].
- by rewrite dprod1E -(of_realM _ _ _ (hf (p, q))) //; apply mulr_ge0; apply ge0_mu.
by rewrite bigXR // => z _; smt(ge0_mu mulr_ge0).
qed.

lemma sum_pairs (ps : (pw * pp) list) (g : pw * pp -> real) : uniq ps =>
  big predT (fun (z : pw * pp) => mu1 dP z.`1 * mu1 dQ z.`2 * (if z \in ps then g z else 1%r)) allPQ =
  1%r - bigi predT (fun j => mu1 dP (nth witness ps j).`1 * mu1 dQ (nth witness ps j).`2
                             * (1%r - g (nth witness ps j))) 0 (size ps).
proof.
move=> hu.
have h1 : big predT (fun (z : pw * pp) => mu1 dP z.`1 * mu1 dQ z.`2) allPQ = 1%r.
- have hll : is_lossless (dP `*` dQ) by apply/dprod_ll; rewrite dP_ll dQ_ll.
  rewrite -hll (mu_eq _ predT (mem allPQ)) => [z | ]; 1: by rewrite allPQP.
  by rewrite mu_mem_uniq ?allPQ_uniq; apply eq_bigr => -[p q] _ /=; rewrite dprod1E.
have hX : big predT (fun (z : pw * pp) => if z \in ps then mu1 dP z.`1 * mu1 dQ z.`2 * (1%r - g z) else 0%r) allPQ =
          bigi predT (fun j => mu1 dP (nth witness ps j).`1 * mu1 dQ (nth witness ps j).`2
                               * (1%r - g (nth witness ps j))) 0 (size ps).
- rewrite -(big_mkcond (mem ps)) -big_filter (eq_big_perm _ _ (filter (mem ps) allPQ) ps).
  + apply uniq_perm_eq; [apply filter_uniq; apply allPQ_uniq | exact hu | by move=> z; rewrite mem_filter allPQP].
  by rewrite (big_nth witness) /(\o).
rewrite (eq_bigr _ _ (fun (z : pw * pp) => mu1 dP z.`1 * mu1 dQ z.`2 +
           (- (if z \in ps then mu1 dP z.`1 * mu1 dQ z.`2 * (1%r - g z) else 0%r)))) => [z _ /= | ].
- by case: (z \in ps) => _; ring.
by rewrite big_split h1 -hX -sumrN.
qed.

(* The attack halts when its oracles do. *)
lemma matchp_ll (O <: OraclesP {-MatchP}) :
  islossless O.a => islossless O.b => islossless O.h => islossless O.s => islossless O.t =>
  islossless O.w => islossless MatchP(O).guess.
proof.
move=> ha hb hh hs ht hw; proc.
while true (size MatchP.pairs - j).
- move=> z; wp; sp; conseq (_ : _ ==> true) => [/# |].
  seq 1 : true 1%r 1%r 0%r 0%r => //; 1: by call hs.
  sp; seq 1 : true 1%r 1%r 0%r 0%r => //; 1: by if; [wp; call ht; auto | auto].
  by if; [wp; call hw; auto | auto].
wp; while true (size MatchP.ws - j).
- move=> z; wp; while true (i + 1).
  + by move=> z'; wp; call hh; call ha; if; [auto | call hb; auto]; auto => /#.
  by auto => /#.
by wp; call hb; auto => /#.
qed.

section W7.
declare op ws0 : pw list.
declare op pairs0 : (pw * pp) list.
declare op mode0 : int.

(* The attack with its lists fixed, as an adversary. In a memory that holds the lists it plays the
   game of MatchP. *)
local module M7 (O : OraclesP) = {
  proc guess(y : state, om : data) : seed * (pw * pp) = {
    var out;
    MatchP.ws <- ws0; MatchP.pairs <- pairs0; MatchP.mode <- mode0;
    out <@ MatchP(O).guess(y, om);
    return out;
  }
}.

local lemma fixed7 (E : seed * (pw * pp) -> pw -> pp -> state -> seed -> bool) &m :
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  Pr[GameP(Setup0P(Seq), MatchP).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd] =
  Pr[GameP(Setup0P(Seq), M7).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd].
proof.
move=> hws hpairs hmd.
byequiv (_ : ={glob MatchP} /\ MatchP.ws{1} = ws0 /\ MatchP.pairs{1} = pairs0 /\ MatchP.mode{1} = mode0
            ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd}) => //.
proc; inline M7(CountP(IP)).guess; wp.
call (_ : ={arg, glob MatchP, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs,
            CountP.ct, CountP.cw} ==> ={res}); 1: by sim.
inline CountP(IP).init Count(IP).init; wp.
call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); 1: by sim.
by auto => />.
qed.

(* From Θ0 with the cut rule to Θ1 (Lemmas W2 and W3), for an event of the output and the secrets. *)
local lemma red7 (E : seed * (pw * pp) -> pw -> pp -> state -> seed -> bool) &m : 0 <= mode0 <= 2 =>
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  Pr[GameP(Setup1P, M7).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd]
    - deltacut (size pairs0) (if mode0 = 0 then 0 else size pairs0)
  <= Pr[GameP(Setup0P(Seq), MatchP).main() @ &m : E res Gen.p Gen.q Gen.e Gen.sd].
proof.
move=> hmode hws hpairs hmd; rewrite (fixed7 E &m hws hpairs hmd).
have := theta01_out (size pairs0) (if mode0 = 0 then 0 else size pairs0) E M7 _ _ &m _ _; 3,4: smt(size_ge0).
- move=> O; proc; call (W7_budget O (size ws0) (size pairs0)); auto => />; smt().
- by move=> O ha hb hh hs ht hw; proc; call (matchp_ll O ha hb hh hs ht hw); auto.
smt().
qed.

(* Θ1 as a game on a continuation, for the seed and for the pair. *)
local module D7 (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = {
    var out;
    MatchP.ws <- ws0; MatchP.pairs <- pairs0; MatchP.mode <- mode0;
    CountP(O).init();
    out <@ MatchP(CountP(O)).guess(y, om);
    return out.`1 = sd;
  }
}.

local module D7p (O : OraclesP) = {
  proc run(y : state, om : data, p : pw, q : pp, e : state, sd : seed) : bool = {
    var out;
    MatchP.ws <- ws0; MatchP.pairs <- pairs0; MatchP.mode <- mode0;
    CountP(O).init();
    out <@ MatchP(CountP(O)).guess(y, om);
    return out.`2 = (p, q);
  }
}.

(* Θ1 with A, B, H as a whole function. *)
local module IPG7 (G : R.RO) : OraclesP = {
  proc a = Orc(G).a
  proc b = Orc(G).b
  proc h = Orc(G).h
  proc s = IP.s
  proc t = IP.t
  proc w = IP.w
}.

local module V7 (G : R.RO) = {
  proc distinguish() : bool = {
    var y, om, et, b;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    y <$ dstate;
    om <$ ddata;
    Gen.sd <$ dseed;
    Gen.e <@ Net(Orc(G)).dec(Gen.p, y);
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    et <$ W240.DWord.dunifin;
    RT.RO.set(Gen.sd, (zero16, et));
    RW.RO.set(Gen.sd, om);
    b <@ D7(IPG7(G)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local lemma eager7 &m :
  Pr[GameP(Setup1P, M7).main() @ &m : res.`1 = Gen.sd] = Pr[R.MainD(V7, RE.FunRO).distinguish() @ &m : res].
proof.
have -> : Pr[GameP(Setup1P, M7).main() @ &m : res.`1 = Gen.sd] = Pr[GenGame(Setup1P, D7).main() @ &m : res].
- byequiv => //; proc; inline M7(CountP(IP)).guess D7(IP).run; wp.
  call (_ : ={arg, glob MatchP, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs,
              CountP.ct, CountP.cw} ==> ={res}); 1: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
have -> : Pr[GenGame(Setup1P, D7).main() @ &m : res] = Pr[R.MainD(V7, R.RO).distinguish() @ &m : res].
- by byequiv => //; proc; inline *; sim.
by byequiv (RO_FunRO V7).
qed.

local module V7p (G : R.RO) = {
  proc distinguish() : bool = {
    var y, om, et, b;
    RS.RO.init(); RT.RO.init(); RW.RO.init();
    Gen.p <$ dP;
    Gen.q <$ dQ;
    y <$ dstate;
    om <$ ddata;
    Gen.sd <$ dseed;
    Gen.e <@ Net(Orc(G)).dec(Gen.p, y);
    RS.RO.set((Gen.e, Gen.q), Gen.sd);
    et <$ W240.DWord.dunifin;
    RT.RO.set(Gen.sd, (zero16, et));
    RW.RO.set(Gen.sd, om);
    b <@ D7p(IPG7(G)).run(y, om, Gen.p, Gen.q, Gen.e, Gen.sd);
    return b;
  }
}.

local lemma eager7p &m :
  Pr[GameP(Setup1P, M7).main() @ &m : res.`2 = (Gen.p, Gen.q)] = Pr[R.MainD(V7p, RE.FunRO).distinguish() @ &m : res].
proof.
have -> : Pr[GameP(Setup1P, M7).main() @ &m : res.`2 = (Gen.p, Gen.q)] = Pr[GenGame(Setup1P, D7p).main() @ &m : res].
- byequiv => //; proc; inline M7(CountP(IP)).guess D7p(IP).run; wp.
  call (_ : ={arg, glob MatchP, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m, Count.ca, Count.cb, Count.ch, CountP.cs,
              CountP.ct, CountP.cw} ==> ={res}); 1: by sim.
  inline CountP(IP).init Count(IP).init; wp.
  by call (_ : true ==> ={res, Gen.p, Gen.q, Gen.e, Gen.sd, R.RO.m, RS.RO.m, RT.RO.m, RW.RO.m}); [sim | auto].
have -> : Pr[GenGame(Setup1P, D7p).main() @ &m : res] = Pr[R.MainD(V7p, R.RO).distinguish() @ &m : res].
- by byequiv => //; proc; inline *; sim.
by byequiv (RO_FunRO V7p).
qed.

(* Potentials of the matching: before the run, and in the loop over the pairs. *)
op phi7 (p : pw) (q : pp) : real =
  if (p, q) \in pairs0 then minr 1%r ((index (p, q) pairs0)%r * tw mode0) else 1%r.

op Phi7 (found : bool) (j : int) (bad : bool) (p : pw) (q : pp) : real =
  if found then b2r bad
  else if (p, q) \in pairs0 /\ j <= index (p, q) pairs0
  then minr 1%r ((index (p, q) pairs0 - j)%r * tw mode0) else 1%r.

(* No stored answer of T or Omega lets a seed other than seed* pass the test. *)
op tinv7 (mT : (seed, W16.word * W240.word) fmap) (mW : (seed, data) fmap) (sd : seed) (om : data) =
  forall s, s <> sd =>
    (mode0 = 1 => s \in mT => (oget mT.[s]).`1 <> zero16) /\
    ((mode0 = 0 \/ mode0 = 2) => s \in mW => oget mW.[s] <> om) /\
    (mode0 = 2 => s \in mT => (oget mT.[s]).`1 = zero16 => s \in mW) /\
    (mode0 = 2 => s \in mW => s \in mT).

lemma tw_bounds : 0 <= mode0 <= 2 => 0%r < tw mode0 <= 1%r.
proof.
move=> hm; have h : forall k, 0 <= k => 0%r < inv (2%r ^ k) <= 1%r.
- by move=> k hk; split; [smt(expr_gt0 invr_gt0) | rewrite invr_le1; smt(expr_gt0 exprn_ege1)].
by rewrite /tw; smt(gt0_lambda).
qed.

(* After the query of S: 0 if it returned seed*, otherwise the potential of the next pair plus the
   chance tw that this pair passes. *)
op Psi7 (sgsd : bool) (j : int) (p : pw) (q : pp) : real =
  if sgsd then 0%r
  else Phi7 false (j + 1) false p q + tw mode0 * (1%r - Phi7 false (j + 1) false p q).

lemma Phi7_bounds j p q : 0 <= mode0 <= 2 => 0%r <= Phi7 false j false p q <= 1%r.
proof. by move=> hm; have := tw_bounds hm; rewrite /Phi7 /=; smt(index_ge0). qed.

lemma psi7_le sgsd j p q : 0 <= mode0 <= 2 => 0 <= j =>
  ((p, q) \in pairs0 => j = index (p, q) pairs0 => sgsd) =>
  Psi7 sgsd j p q <= Phi7 false j false p q.
proof.
move=> hm hj hs; have [ht0 ht1] := tw_bounds hm; have [hA0 hA1] := Phi7_bounds (j + 1) p q hm.
have [hB0 hB1] := Phi7_bounds j p q hm.
rewrite /Psi7; case: sgsd hs => [_ | hs] /=; 1: smt().
move: hA0 hA1 hB0 hB1; rewrite /Phi7 /=.
case: ((p, q) \in pairs0) hs => hin hs /=; 2: smt().
have hne : j <> index (p, q) pairs0 by smt().
case: (j + 1 <= index (p, q) pairs0) => hlt /=; 2: smt().
rewrite (_ : j <= index (p, q) pairs0) 1:/# /= /minr.
have -> : (index (p, q) pairs0 - j)%r * tw mode0 = (index (p, q) pairs0 - (j + 1))%r * tw mode0 + tw mode0.
- by rewrite !fromintB fromintD; ring.
smt().
qed.

local lemma core7_e : 0 <= mode0 <= 2 => uniq pairs0 => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  ehoare [R.MainD(V7, RE.FunRO).distinguish :
    (Ep dP (fun p => Ep dQ (fun q => (phi7 p q)%xr))) ==> (!res)%xr].
proof.
move=> hmode hu hall.
proc; inline V7(RE.FunRO).distinguish D7(IPG7(RE.FunRO)).run MatchP(CountP(IPG7(RE.FunRO))).guess.
wp.
while ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\
        xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) ws0 /\ Gen.e = invperm RE.FunRO.f Gen.p y1 /\
        sd = Gen.sd /\ om1 = om /\ RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\
        RT.RO.m.[Gen.sd] = Some (zero16, et) /\ RW.RO.m.[Gen.sd] = Some om /\ 0 <= j /\
        (!found => tinv7 RT.RO.m RW.RO.m Gen.sd om)) `|`
       (Phi7 found j (out0.`1 <> sd) Gen.p Gen.q)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hws hp hmd hx he hsd hom hS hT hW hj htv.
  apply xr_ble; rewrite /Phi7; move: hc; case: (found{hr}) => //= hc.
  by move: hc; rewrite hp; smt(index_mem).
- seq 3 : ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\
              xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) ws0 /\ Gen.e = invperm RE.FunRO.f Gen.p y1 /\
              sd = Gen.sd /\ om1 = om /\ RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\
              RT.RO.m.[Gen.sd] = Some (zero16, et) /\ RW.RO.m.[Gen.sd] = Some om /\ 0 <= j /\ !found /\
              tinv7 RT.RO.m RW.RO.m Gen.sd om /\ v = nth witness pairs0 j /\ pass) `|`
             (Psi7 (sg = Gen.sd) j Gen.p Gen.q)%xr).
  + inline *; auto => &hr /=; apply xle_cxr_r => -[[hc hnf] [#] hws hp hmd hx he hsd hom hS hT hW hj htv].
    have hkey : (Gen.p{hr}, Gen.q{hr}) \in pairs0 => j{hr} = index (Gen.p{hr}, Gen.q{hr}) pairs0 =>
                (oget (assoc xsl{hr} (nth witness MatchP.pairs{hr} j{hr}).`1), (nth witness MatchP.pairs{hr} j{hr}).`2)
                = (Gen.e{hr}, Gen.q{hr}).
    - move=> hin hidx; rewrite hp hidx nth_index //= hx he assoc_mapF //.
      by move: hall; rewrite allP => /(_ _ hin).
    apply (xle_trans (Ep dseed (fun _ => (Phi7 false j{hr} false Gen.p{hr} Gen.q{hr})%xr))).
    - apply le_Ep => r _ /=.
      case: ((oget (assoc xsl{hr} (nth witness MatchP.pairs{hr} j{hr}).`1), (nth witness MatchP.pairs{hr} j{hr}).`2)
             \in RS.RO.m{hr}) => hz /=.
      + apply xle_cxr_l; 1: by rewrite hp; smt().
        by apply xr_le; apply psi7_le => // hin hidx; rewrite (hkey hin hidx) hS.
      apply xle_cxr_l; 1: by rewrite hp; smt(get_setE).
      apply xr_le; apply psi7_le => // hin hidx; rewrite get_set_sameE /=.
      by move: hz; rewrite (hkey hin hidx); smt().
    by rewrite EpC dseed_ll smul1m /Phi7 (_ : found{hr} = false) 1:/#.
  have [h0 | [h1 | h2]] : mode0 = 0 \/ mode0 = 1 \/ mode0 = 2 by smt().
  + rcondf 1; 1: by auto => />; smt().
    rcondt 1; 1: by auto => />; smt().
    inline *; auto => &hr /=; apply xle_cxr_r => -[#] hws hp hmd hx he hsd hom hS hT hW hj hnf htv hv hps.
    have [hA0 hA1] := Phi7_bounds (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode.
    case: (sg{hr} = Gen.sd{hr}) => hsg.
    - apply (xle_trans (Ep ddata (fun _ => 0%xr))); 2: by rewrite EpC ddata_ll smul1m /Psi7.
      have hin : Gen.sd{hr} \in RW.RO.m{hr} by rewrite domE hW.
      apply le_Ep => r _ /=; rewrite hsg hin /= hW /= hom /=.
      by apply xle_cxr_l; [rewrite hp; smt() | rewrite /Phi7 hsd].
    apply (xle_trans (Ep ddata (fun r => (Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr} +
             (1%r - Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr}) * b2r (r = om{hr}))%xr))).
    - apply le_Ep => r _ /=; case: (sg{hr} \in RW.RO.m{hr}) => hin /=.
      + have hno : oget RW.RO.m{hr}.[sg{hr}] <> om{hr} by have := htv sg{hr} hsg; smt().
        rewrite hom hno /=; apply xle_cxr_l; 1: by rewrite hp; smt().
        by apply xr_le; rewrite /Phi7 /=; smt(b2r_ge0).
      rewrite get_set_sameE /= hom; case: (r = om{hr}) => hr /=.
      + by apply xle_cxr_l; [rewrite hp; smt(get_setE) | apply xr_le; rewrite /Phi7 /=; smt()].
      apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7 /=; smt().
      have ht' : tinv7 RT.RO.m{hr} RW.RO.m{hr}.[sg{hr} <- r] Gen.sd{hr} om{hr}.
      + by move=> s hs; have := htv s hs; rewrite h0 /= mem_set get_setE; smt().
      by rewrite hp; smt(get_setE).
    rewrite Ep_cbs ?ddata_ll //; 1: smt().
    by apply xr_le; rewrite /Psi7 /= (mu_eq _ _ (pred1 om{hr})) 1:/# ddata1 /tw h0 /=; smt().
  + rcondt 1; 1: by auto => />; smt().
    rcondf 3; 1: by inline *; auto => />; smt().
    inline *; auto => &hr /=; apply xle_cxr_r => -[#] hws hp hmd hx he hsd hom hS hT hW hj hnf htv hv hps.
    have [hA0 hA1] := Phi7_bounds (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode.
    case: (sg{hr} = Gen.sd{hr}) => hsg.
    - apply (xle_trans (Ep dct (fun _ => 0%xr))); 2: by rewrite EpC dct_ll smul1m /Psi7.
      have hin : Gen.sd{hr} \in RT.RO.m{hr} by rewrite domE hT.
      apply le_Ep => r _ /=; rewrite hsg hin /= hT /=.
      by apply xle_cxr_l; [rewrite hp; smt() | rewrite /Phi7 hsd].
    apply (xle_trans (Ep dct (fun (r : W16.word * W240.word) => (Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr} +
             (1%r - Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr}) * b2r (r.`1 = zero16))%xr))).
    - apply le_Ep => r _ /=; case: (sg{hr} \in RT.RO.m{hr}) => hin /=.
      + have hno : (oget RT.RO.m{hr}.[sg{hr}]).`1 <> zero16 by have := htv sg{hr} hsg; smt().
        rewrite hno /=; apply xle_cxr_l; 1: by rewrite hp; smt().
        by apply xr_le; rewrite /Phi7 /=; smt(b2r_ge0).
      rewrite get_set_sameE /=; case: (r.`1 = zero16) => hr /=.
      + by apply xle_cxr_l; [rewrite hp; smt(get_setE) | apply xr_le; rewrite /Phi7 /=; smt()].
      apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7 /=; smt().
      have ht' : tinv7 RT.RO.m{hr}.[sg{hr} <- r] RW.RO.m{hr} Gen.sd{hr} om{hr}.
      + by move=> s hs; have := htv s hs; rewrite h1 /= mem_set get_setE; smt().
      by rewrite hp; smt(get_setE).
    rewrite Ep_cbs ?dct_ll //; 1: smt().
    have hm : mu dct (fun (r : W16.word * W240.word) => r.`1 = zero16) = pk.
    + by rewrite /dct (dprodEl W16.DWord.dunifin W240.DWord.dunifin (fun r => r = zero16)) W240.DWord.dunifin_ll dW16_zero.
    by apply xr_le; rewrite /Psi7 /= hm /tw h1 /pk /=; smt().
  rcondt 1; 1: by auto => />; smt().
  seq 2 : ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\
            xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) ws0 /\ Gen.e = invperm RE.FunRO.f Gen.p y1 /\
            sd = Gen.sd /\ om1 = om /\ RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\
            RT.RO.m.[Gen.sd] = Some (zero16, et) /\ RW.RO.m.[Gen.sd] = Some om /\ 0 <= j /\ !found /\
            v = nth witness pairs0 j /\ sg \in RT.RO.m /\ (sg = Gen.sd => pass) /\
            (pass => sg <> Gen.sd => sg \in RW.RO.m => oget RW.RO.m.[sg] <> om) /\
            (forall s, s <> Gen.sd => (s <> sg \/ !pass) =>
               (s \in RT.RO.m => (oget RT.RO.m.[s]).`1 = zero16 => s \in RW.RO.m) /\
               (s \in RW.RO.m => oget RW.RO.m.[s] <> om) /\ (s \in RW.RO.m => s \in RT.RO.m))) `|`
           (if pass then
              (if sg = Gen.sd then 0%r
               else if sg \in RW.RO.m then Phi7 false (j + 1) false Gen.p Gen.q
               else Phi7 false (j + 1) false Gen.p Gen.q +
                    (1%r - Phi7 false (j + 1) false Gen.p Gen.q) * inv (2%r ^ lambda))
            else Phi7 false (j + 1) false Gen.p Gen.q)%xr).
  + inline *; auto => &hr /=; apply xle_cxr_r => -[#] hws hp hmd hx he hsd hom hS hT hW hj hnf htv hv hps.
    have [hA0 hA1] := Phi7_bounds (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode.
    have htv2 : forall s, s <> Gen.sd{hr} =>
                (s \in RT.RO.m{hr} => (oget RT.RO.m{hr}.[s]).`1 = zero16 => s \in RW.RO.m{hr}) /\
                (s \in RW.RO.m{hr} => oget RW.RO.m{hr}.[s] <> om{hr}) /\ (s \in RW.RO.m{hr} => s \in RT.RO.m{hr}).
    - by move=> s hs; have := htv s hs; rewrite h2.
    case: (sg{hr} = Gen.sd{hr}) => hsg.
    - apply (xle_trans (Ep dct (fun _ => 0%xr))); 2: by rewrite EpC dct_ll smul1m /Psi7.
      have hin : Gen.sd{hr} \in RT.RO.m{hr} by rewrite domE hT.
      apply le_Ep => r _ /=; rewrite hsg hin /= hT /=.
      by apply xle_cxr_l; [rewrite hp; smt() | done].
    apply (xle_trans (Ep dct (fun (r : W16.word * W240.word) => (Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr} +
             ((1%r - Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr}) * inv (2%r ^ lambda)) *
             b2r (r.`1 = zero16))%xr))).
    - have hl : 0%r <= inv (2%r ^ lambda) by smt(expr_gt0 invr_gt0).
      apply le_Ep => r _ /=; case: (sg{hr} \in RT.RO.m{hr}) => hin /=.
      + have [h21 [h22 h23]] := htv2 sg{hr} hsg.
        case: ((oget RT.RO.m{hr}.[sg{hr}]).`1 = zero16) => hc /=.
        * have hw := h21 hin hc; rewrite hw /=.
          apply xle_cxr_l; [rewrite hp; smt() | apply xr_le; smt(b2r_ge0)].
        by apply xle_cxr_l; [rewrite hp; smt() | apply xr_le; smt(b2r_ge0)].
      have hnw : sg{hr} \notin RW.RO.m{hr} by have [_ [_ h23]] := htv2 sg{hr} hsg; smt().
      rewrite get_set_sameE /=; case: (r.`1 = zero16) => hr /=.
      + rewrite hnw /=; apply xle_cxr_l; 2: by apply xr_le; rewrite /=.
        by rewrite hp; smt(get_setE mem_set).
      by apply xle_cxr_l; [rewrite hp; smt(get_setE mem_set) | apply xr_le; rewrite /=].
    rewrite Ep_cbs ?dct_ll //; 1: smt(expr_gt0 invr_gt0).
    have hm : mu dct (fun (r : W16.word * W240.word) => r.`1 = zero16) = pk.
    + by rewrite /dct (dprodEl W16.DWord.dunifin W240.DWord.dunifin (fun r => r = zero16)) W240.DWord.dunifin_ll dW16_zero.
    have ht : tw mode0 = inv (2%r ^ lambda) * pk.
    + rewrite /tw h2 /pk /= RField.exprD_nneg; [smt(gt0_lambda) | done |].
      by rewrite RField.invrM //; smt(expr_gt0).
    by apply xr_le; rewrite /Psi7 /= hm ht; smt().
  if.
  + inline *; auto => &hr /=; apply xle_cxr_r => -[[hps _] [#] hws hp hmd hx he hsd hom hS hT hW hj
      hnf hv hsT hsd2 hsw hall2].
    have [hA0 hA1] := Phi7_bounds (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode.
    have ht' : forall (mW : (seed, data) fmap), (forall s, s <> Gen.sd{hr} => s <> sg{hr} => mW.[s] = RW.RO.m{hr}.[s]) =>
               sg{hr} \in mW => oget mW.[sg{hr}] <> om{hr} => (forall s, s \in RW.RO.m{hr} => s \in mW) =>
               tinv7 RT.RO.m{hr} mW Gen.sd{hr} om{hr}.
    - move=> mW heq hin hne hsub s hs; rewrite h2 /=.
      case: (s = sg{hr}) => hss.
      + by rewrite hss hin /=; split; [smt() | rewrite -hss; smt()].
      have [h21 [h22 h23]] := hall2 s hs _; 1: by left.
      by rewrite /dom (heq s hs hss); smt().
    case: (sg{hr} = Gen.sd{hr}) => hsg.
    - apply (xle_trans (Ep ddata (fun _ => 0%xr))); 2: by rewrite EpC ddata_ll smul1m hps /=.
      have hin : Gen.sd{hr} \in RW.RO.m{hr} by rewrite domE hW.
      apply le_Ep => r _ /=; rewrite hsg hin /= hW /= hom /=.
      by apply xle_cxr_l; [rewrite hp; smt() | rewrite /Phi7 hsd].
    case: (sg{hr} \in RW.RO.m{hr}) => hin.
    - have hno : oget RW.RO.m{hr}.[sg{hr}] <> om{hr} by smt().
      apply (xle_trans (Ep ddata (fun _ => (Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr})%xr))).
      + apply le_Ep => r _ /=; rewrite hom hno /=.
        apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7 (_ : found{hr} = false) 1:/#.
        by rewrite hp; have := ht' RW.RO.m{hr} _ hin hno _ => //; smt().
      by rewrite EpC ddata_ll smul1m ?hps.
    apply (xle_trans (Ep ddata (fun r => (Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr} +
             (1%r - Phi7 false (j{hr} + 1) false Gen.p{hr} Gen.q{hr}) * b2r (r = om{hr}))%xr))).
    - apply le_Ep => r _ /=; rewrite ?hin /= get_set_sameE /= hom; case: (r = om{hr}) => hr /=.
      + by apply xle_cxr_l; [rewrite hp; smt(get_setE) | apply xr_le; rewrite /Phi7 /=; smt()].
      apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7 /=; smt().
      have := ht' RW.RO.m{hr}.[sg{hr} <- r] _ _ _ _; 1: by move=> s _ hs; rewrite get_setE hs.
      + by rewrite mem_set.
      + by rewrite get_set_sameE.
      + by move=> s; rewrite mem_set => ->.
      by rewrite hp; smt(get_setE).
    rewrite Ep_cbs ?ddata_ll //; 1: smt().
    by apply xr_le; rewrite ?hps ?hsg ?hin /= (mu_eq _ _ (pred1 om{hr})) 1:/# ddata1; smt().
  auto => &hr /=; apply xle_cxr_r => -[hnp [#] hws hp hmd hx he hsd hom hS hT hW hj
    hnf hv hsT hsd2 hsw hall2].
  have hnp' : !pass{hr} by smt().
  rewrite hnp' /=; apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7 (_ : found{hr} = false) 1:/#.
  rewrite hp /=; do !split => //; 1: smt().
  move=> _ s hs; rewrite h2 /=; have := hall2 s hs _; [by right | smt()].
wp.
while ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\ 0 <= j <= size ws0 /\
        xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) (take j ws0) /\
        s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
        Gen.e = invperm RE.FunRO.f Gen.p y1 /\ sd = Gen.sd /\ om1 = om /\
        RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\ RT.RO.m.[Gen.sd] = Some (zero16, et) /\
        RW.RO.m.[Gen.sd] = Some om /\ tinv7 RT.RO.m RW.RO.m Gen.sd om) `|` (phi7 Gen.p Gen.q)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hws hp hmd hj0 hj1 hx hs11 he hsd hom hS hT hW htv.
  apply xle_cxr_l.
  + by rewrite hx (_ : j{hr} = size ws0) 1:/# take_size; smt().
  by apply xr_le; rewrite /Phi7 /phi7 /=; smt(index_ge0).
- wp; while ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\ 0 <= j < size ws0 /\
              xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) (take j ws0) /\
              s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
              Gen.e = invperm RE.FunRO.f Gen.p y1 /\ sd = Gen.sd /\ om1 = om /\
              RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\ RT.RO.m.[Gen.sd] = Some (zero16, et) /\
              RW.RO.m.[Gen.sd] = Some om /\ tinv7 RT.RO.m RW.RO.m Gen.sd om /\
              w = nth witness ws0 j /\ -1 <= i <= 11 /\
              z = foldl (fun (u : state) k => unround (mask RE.FunRO.f w (rd k) u.`1) u) y1
                        (rev (iota_ (i + 1) (11 - i)))) `|` (phi7 Gen.p Gen.q)%xr).
  + move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hws hp hmd hj0 hj1 hx hs11 he hsd hom hS hT hW htv
      hw hi0 hi1 hz /=.
    apply xle_cxr_l; 2: by [].
    have hi : i{hr} = -1 by smt().
    have hzx : z{hr} = invperm RE.FunRO.f{hr} w{hr} y1{hr} by rewrite hz hi /invperm.
    have hxs : rcons xsl{hr} (w{hr}, z{hr}) =
               map (fun w0 => (w0, invperm RE.FunRO.f{hr} w0 y1{hr})) (take (j{hr} + 1) ws0).
    - by rewrite (take_nth witness) 1:/# map_rcons hx /= hzx hw.
    by rewrite hws; smt().
  + inline *; auto => &hr /=; apply xle_cxr_r => -[hc [#] hws hp hmd hj0 hj1 hx hs11 he hsd hom hS hT hW htv
      hw hi0 hi1 hz].
    have hstep : forall s0, s0 = salt_of (RE.FunRO.f{hr} (PB (rd i{hr}, z{hr}.`1))) =>
      unround (mask_of (RE.FunRO.f{hr} (PH (key_of (RE.FunRO.f{hr} (PA (w{hr}, s0))), rd i{hr}, z{hr}.`1)))) z{hr} =
      foldl (fun (u : state) k => unround (mask RE.FunRO.f{hr} w{hr} (rd k) u.`1) u) y1{hr}
            (rev (iota_ i{hr} (11 - (i{hr} - 1)))).
    - move=> s0 ->; rewrite (_ : 11 - (i{hr} - 1) = (11 - i{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons -hz.
      by rewrite /mask.
    case: (i{hr} = 11) => hi11 /=.
    - apply xle_cxr_l; 2: by [].
      have hz1 : z{hr} = y1{hr} by rewrite hz hi11 /= iota0.
      have h := hstep s11{hr} _; 1: by rewrite hs11 hz1 hi11.
      by rewrite h; smt().
    apply xle_cxr_l; 2: by [].
    have h := hstep (salt_of (RE.FunRO.f{hr} (PB (rd i{hr}, z{hr}.`1)))) _ => //.
    by rewrite h; smt().
  auto => &hr /=; apply xle_cxr_r => -[hc [#] hws hp hmd hj0 hj1 hx hs11 he hsd hom hS hT hW htv].
  by apply xle_cxr_l => //; rewrite hws iota0 /=; smt().
inline *; wp.
conseq (_ : _ ==> (y2 = invperm RE.FunRO.f Gen.p y /\ RS.RO.m = empty /\ RT.RO.m = empty /\ RW.RO.m = empty) `|`
                  (phi7 Gen.p Gen.q)%xr).
- move=> _; apply xle_cxr_l => // p2 q0 sd0 m1 m2 m3 f om2 y6 y2_0; apply xle_cxr_r => -[#] hy h1 h2 h3.
  apply (xle_trans (Ep W240.DWord.dunifin (fun _ => (phi7 p2 q0)%xr))); 2: by rewrite EpC W240.DWord.dunifin_ll smul1m.
  apply le_Ep => et0 _ /=; apply xle_cxr_l => //.
  rewrite h1 h2 h3 hy /= !get_set_sameE take0 size_ge0 /= /tinv7 => s hs.
  by rewrite !mem_set !mem_empty hs.
- move=> &hr; apply xle_cxr_r => h.
  exact (h Gen.p{hr} Gen.q{hr} Gen.sd{hr} RS.RO.m{hr} RT.RO.m{hr} RW.RO.m{hr} RE.FunRO.f{hr} om{hr} y{hr} y2{hr}).
while ((p0 = Gen.p /\ -1 <= i0 <= 11 /\ RS.RO.m = empty /\ RT.RO.m = empty /\ RW.RO.m = empty /\
        y2 = foldl (fun (u : state) k => unround (mask RE.FunRO.f Gen.p (rd k) u.`1) u) y
                   (rev (iota_ (i0 + 1) (11 - i0)))) `|` (phi7 Gen.p Gen.q)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hp hi0 hi1 hS hT hW hy.
  by apply xle_cxr_l => //; rewrite hS hT hW hy /= (_ : i0{hr} = -1) 1:/# /invperm.
- auto => &hr /=; apply xle_cxr_r => -[hc [#] hp hi0 hi1 hS hT hW hy].
  apply xle_cxr_l => //; rewrite hp hS hT hW /=; split; 1: smt().
  rewrite (_ : 11 - (i0{hr} - 1) = (11 - i0{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons -hy /=.
  by rewrite /mask.
wp; skip => &hr /=.
apply (xle_trans (Ep (RE.MUniFinFun.dfun (fun (_ : point) => dans))
         (fun _ => Ep dP (fun (p2 : pw) => Ep dQ (fun (q0 : pp) => (phi7 p2 q0)%xr))))).
- apply le_Ep => f _ /=; apply le_Ep => p2 _ /=; apply le_Ep => q0 _ /=.
  apply (xle_trans (Ep dstate (fun _ => (phi7 p2 q0)%xr))); 2: by rewrite EpC dstate_ll smul1m.
  apply le_Ep => y6 _ /=; apply (xle_trans (Ep ddata (fun _ => (phi7 p2 q0)%xr))); 2: by rewrite EpC ddata_ll smul1m.
  apply le_Ep => om6 _ /=; apply (xle_trans (Ep dseed (fun _ => (phi7 p2 q0)%xr))); 2: by rewrite EpC dseed_ll smul1m.
  by apply le_Ep => sd6 _ /=; apply xle_cxr_l; [rewrite iota0 | done].
have hll : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
- by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
by rewrite EpC hll smul1m.
qed.

(* The matching in Θ1: the pair (P, Q) passes, and a wrong pair before it passes with chance at most
   tw. *)
local lemma core7 &m : 0 <= mode0 <= 2 => uniq pairs0 => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                        * (1%r - j%r * tw mode0)) 0 (size pairs0)
  <= Pr[R.MainD(V7, RE.FunRO).distinguish() @ &m : res].
proof.
move=> hmode hu hall; have [ht0 ht1] := tw_bounds hmode.
have hS := sum_pairs pairs0 (fun z => (index z pairs0)%r * tw mode0) hu.
have hR : bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
             * (1%r - (fun z => (index z pairs0)%r * tw mode0) (nth witness pairs0 j))) 0 (size pairs0) =
          bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
             * (1%r - j%r * tw mode0)) 0 (size pairs0).
- by apply eq_big_int => j hj /=; rewrite index_uniq // /#.
move: hS; rewrite hR => hS.
have hE : Ep dP (fun p => Ep dQ (fun q => (phi7 p q)%xr)) <=
          (1%r - bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                                      * (1%r - j%r * tw mode0)) 0 (size pairs0))%xr.
- apply (xle_trans (Ep dP (fun p => Ep dQ (fun q => ((fun (z : pw * pp) =>
           if z \in pairs0 then (index z pairs0)%r * tw mode0 else 1%r) (p, q))%xr)))).
  + by apply le_Ep => p _ /=; apply le_Ep => q _; apply xr_le => /=; rewrite /phi7; smt().
  by rewrite Ep_dPQ => [z | ]; [case: (z \in pairs0) => _ //; smt(index_ge0) | rewrite hS].
have hll : islossless R.MainD(V7, RE.FunRO).distinguish.
- have hdf : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
  + by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
  proc; inline V7(RE.FunRO).distinguish D7(IPG7(RE.FunRO)).run; wp.
  call (matchp_ll (CountP(IPG7(RE.FunRO))) _ _ _ _ _ _).
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto; smt(dseed_ll).
  + by proc; inline *; auto; smt(dct_ll).
  + by proc; inline *; auto; smt(ddata_ll).
  inline *; wp; rnd; wp; while true (i + 1); 1: by auto => /#.
  by auto => />; smt(dP_ll dQ_ll dstate_ll ddata_ll dseed_ll W240.DWord.dunifin_ll).
have h1 : Pr[R.MainD(V7, RE.FunRO).distinguish() @ &m : !res] <=
          1%r - bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                                     * (1%r - j%r * tw mode0)) 0 (size pairs0).
- byehoare (_ : (Ep dP (fun p => Ep dQ (fun q => (phi7 p q)%xr))) ==> (!res)%xr) => //.
  + exact (core7_e hmode hu hall).
  rewrite -hS; apply Bigreal.sumr_ge0 => z _ /=.
  by case: (z \in pairs0) => _; smt(ge0_mu index_ge0 mulr_ge0).
have h2 : Pr[R.MainD(V7, RE.FunRO).distinguish() @ &m : true] = 1%r by byphoare => //; apply hll.
have h3 : Pr[R.MainD(V7, RE.FunRO).distinguish() @ &m : !res] =
          Pr[R.MainD(V7, RE.FunRO).distinguish() @ &m : true] - Pr[R.MainD(V7, RE.FunRO).distinguish() @ &m : res].
- by rewrite Pr[mu_not].
smt().
qed.

(* Seed game, with the pairs in the order of [pairs0], for the rule cut off after ntr trials and
   without refusal; W7R below states it for every covered rule with refusal. *)
lemma W7_seed_cut &m :
  0 <= mode0 <= 2 => uniq ws0 => uniq pairs0 => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                        * (1%r - j%r * tw mode0)) 0 (size pairs0)
    - deltacut (size pairs0) (if mode0 = 0 then 0 else size pairs0)
  <= Pr[GameP(Setup0P(Seq), MatchP).main() @ &m : res.`1 = Gen.sd].
proof.
move=> hmode hwu hu hall hws hp hmd.
have h1 := red7 (fun (out : seed * (pw * pp)) _ _ _ (sd : seed) => out.`1 = sd) &m hmode hws hp hmd.
have h2 := eager7 &m.
have h3 := core7 &m hmode hu hall.
by move: h1 h2 h3 => /=; smt().
qed.

(* The attack with its lists fixed is an adversary of Theorem 5 with the budgets of W7_budget, so
   Theorem 5 bounds its success from above (for the cut rule; W7R below gives the bracket). *)
lemma W7_upper_cut &m (n : int) : 0 <= mode0 <= 2 => size pairs0 <= n =>
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  Pr[GameP(Setup0P(Seq), MatchP).main() @ &m : res.`1 = Gen.sd] <=
    top2 (size ws0) n +
    epsC (12 * size ws0) n (11 * size ws0 + 1) (12 * size ws0) (if mode0 = 0 then 0 else n)
         (if mode0 = 1 then 0 else n) +
    deltacut n (if mode0 = 0 then 0 else n) + inv (2%r ^ 512).
proof.
move=> hmode hn hws hpairs hmd.
move: (fixed7 (fun (out : seed * (pw * pp)) _ _ _ (sd : seed) => out.`1 = sd) &m hws hpairs hmd) => /= ->.
have := theorem5_seed_cut (12 * size ws0) (11 * size ws0 + 1) (12 * size ws0) n
          (if mode0 = 0 then 0 else n) (if mode0 = 1 then 0 else n) M7 _ _ &m _ _ _ _ _ _;
  3..8: smt(size_ge0).
- move=> O; proc; call (W7_budget O (size ws0) (size pairs0)); auto => />; smt().
- by move=> O ha hb hh hs ht hw; proc; call (matchp_ll O ha hb hh hs ht hw); auto.
by rewrite (_ : 12 * size ws0 %/ 12 = size ws0) 1:/#.
qed.

(* ---- The pair game: a wrong pair before (P, Q) passes with chance at most c7 = tw + 2^-512 (its
   answer of S is fresh and differs from seed* except with chance 2^-512), unless the inversion under
   another password meets e* (coll7, the pair lemma). *)
op c7 : real = tw mode0 + inv (2%r ^ 512).
op coll7 (f : point -> ans) (y : state) (p : pw) : bool =
  has (fun w => w <> p /\ invperm f w y = invperm f p y) ws0.

(* No stored answer of S other than the programmed one is seed*. *)
op sinv7 (m : (state * pp, seed) fmap) (e : state) (q : pp) (sd : seed) =
  forall x, x \in m => x <> (e, q) => oget m.[x] <> sd.

op Phi7p (coll found : bool) (j : int) (bad : bool) (p : pw) (q : pp) : real =
  if found then b2r bad
  else if (p, q) \in pairs0 /\ j <= index (p, q) pairs0 /\ !coll
  then minr 1%r ((index (p, q) pairs0 - j)%r * c7) else 1%r.

op Psi7p (coll sgsd bad : bool) (j : int) (p : pw) (q : pp) : real =
  if sgsd then b2r bad
  else Phi7p coll false (j + 1) false p q + tw mode0 * (1%r - Phi7p coll false (j + 1) false p q).

lemma Phi7p_bounds coll j p q : 0 <= mode0 <= 2 => 0%r <= Phi7p coll false j false p q <= 1%r.
proof. by move=> hm; have := tw_bounds hm; rewrite /Phi7p /c7 /=; smt(index_ge0 e512_gt0). qed.

lemma Psi7p_le1 coll sgsd bad j p q : 0 <= mode0 <= 2 => Psi7p coll sgsd bad j p q <= 1%r.
proof.
move=> hm; have [ht0 ht1] := tw_bounds hm; have [hA0 hA1] := Phi7p_bounds coll (j + 1) p q hm.
by rewrite /Psi7p; case: sgsd => _ /=; [smt() | smt()].
qed.

(* The query of S for pair j: e is the chance that a fresh answer is seed*. *)
lemma psi7p_le coll j p q (e : real) : 0 <= mode0 <= 2 => 0 <= j => 0%r <= e <= inv (2%r ^ 512) =>
  ((p, q) \in pairs0 => j = index (p, q) pairs0 => coll) =>
  e + (1%r - e) * Psi7p coll false false j p q <= Phi7p coll false j false p q.
proof.
move=> hm hj [he0 he1] hs; have [ht0 ht1] := tw_bounds hm.
have he2 : inv (2%r ^ 512) <= 1%r by rewrite invr_le1; smt(expr_gt0 exprn_ege1).
have hX := Psi7p_le1 coll false false j p q hm.
have hX0 : 0%r <= Psi7p coll false false j p q.
- by have := Phi7p_bounds coll (j + 1) p q hm; rewrite /Psi7p /=; smt().
have h1 : e + (1%r - e) * Psi7p coll false false j p q <= 1%r.
- by have := ler_wpmul2l (1%r - e) _ _ _ hX; [smt() | smt()].
case: ((p, q) \in pairs0 /\ j <= index (p, q) pairs0 /\ !coll) => hc; last first.
- by have -> : Phi7p coll false j false p q = 1%r by rewrite /Phi7p /= hc.
have [hin [hji hnc]] := hc; have hlt : j + 1 <= index (p, q) pairs0 by smt().
have h2 : e + (1%r - e) * Psi7p coll false false j p q <= e + Psi7p coll false false j p q.
- by have := ler_wpmul2r (Psi7p coll false false j p q) hX0 (1%r - e) 1%r _; [smt() | smt()].
move: h1 h2; rewrite /Psi7p /Phi7p /= hin hnc hji hlt /= /minr /c7.
have -> : (index (p, q) pairs0 - j)%r = (index (p, q) pairs0 - (j + 1))%r + 1%r.
- by rewrite !fromintB fromintD; ring.
have : 0%r <= (index (p, q) pairs0 - (j + 1))%r by smt().
case: (1%r <= (index (p, q) pairs0 - (j + 1))%r * (tw mode0 + inv (2%r ^ 512))) => hcase /=; smt().
qed.

lemma sinv7_set m e q sd x r : sinv7 m e q sd => r <> sd => sinv7 m.[x <- r] e q sd.
proof.
move=> h hr y; rewrite mem_set get_setE.
by case: (y = x) => [-> | hy] /=; [smt() | move=> hm hne; exact (h y hm hne)].
qed.

(* At the start of the pair game: (P, Q) is a pair, the wrong pairs before it pass with chance at most
   c7 each, and the inversions under the other passwords miss e* except with chance (|ws| - 1)
   delta_X. *)
op phi7pb (p : pw) (q : pp) : real =
  if (p, q) \in pairs0 then (size ws0 - 1)%r * deltaX + (index (p, q) pairs0)%r * c7 else 1%r.

local lemma core7p_e : 0 <= mode0 <= 2 => uniq ws0 => uniq pairs0 =>
  all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  ehoare [R.MainD(V7p, RE.FunRO).distinguish :
    (Ep dP (fun p => Ep dQ (fun q => (phi7pb p q)%xr))) ==> (!res)%xr].
proof.
move=> hmode hwu hu hall.
proc; inline V7p(RE.FunRO).distinguish D7p(IPG7(RE.FunRO)).run MatchP(CountP(IPG7(RE.FunRO))).guess.
wp.
while ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\
        xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) ws0 /\ Gen.e = invperm RE.FunRO.f Gen.p y1 /\
        sd = Gen.sd /\ p = Gen.p /\ q = Gen.q /\ om1 = om /\ RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\
        RT.RO.m.[Gen.sd] = Some (zero16, et) /\ RW.RO.m.[Gen.sd] = Some om /\ 0 <= j /\
        (!found => tinv7 RT.RO.m RW.RO.m Gen.sd om /\ sinv7 RS.RO.m Gen.e Gen.q Gen.sd)) `|`
       (Phi7p (coll7 RE.FunRO.f y1 Gen.p) found j (out0.`2 <> (Gen.p, Gen.q)) Gen.p Gen.q)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hws hp hmd hx he hsd hpp hqq hom hS hT hW hj htv.
  rewrite hpp hqq; apply xr_ble; rewrite /Phi7p; move: hc; case: (found{hr}) => //= hc.
  by move: hc; rewrite hp; smt(index_mem).
- seq 3 : ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\
              xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) ws0 /\ Gen.e = invperm RE.FunRO.f Gen.p y1 /\
              sd = Gen.sd /\ p = Gen.p /\ q = Gen.q /\ om1 = om /\ RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\
              RT.RO.m.[Gen.sd] = Some (zero16, et) /\ RW.RO.m.[Gen.sd] = Some om /\ 0 <= j /\ !found /\
              tinv7 RT.RO.m RW.RO.m Gen.sd om /\ (sg <> Gen.sd => sinv7 RS.RO.m Gen.e Gen.q Gen.sd) /\
              v = nth witness pairs0 j /\ pass) `|`
             (Psi7p (coll7 RE.FunRO.f y1 Gen.p) (sg = Gen.sd) (v <> (Gen.p, Gen.q)) j Gen.p Gen.q)%xr).
  + inline *; auto => &hr /=; apply xle_cxr_r => -[[hc hnf] [#] hws hp hmd hx he hsd hpp hqq hom hS hT hW hj htv].
    have [htv' hsv] := htv hnf; have hv0 : nth witness pairs0 j{hr} \in pairs0 by apply mem_nth; smt().
    have hx0 : oget (assoc xsl{hr} (nth witness pairs0 j{hr}).`1) =
               invperm RE.FunRO.f{hr} (nth witness pairs0 j{hr}).`1 y1{hr}.
    - by rewrite hx assoc_mapF //; move: hall; rewrite allP => /(_ _ hv0).
    rewrite hp hx0 (_ : found{hr} = false) 1:/#.
    have -> : Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false j{hr} (out0{hr}.`2 <> (Gen.p{hr}, Gen.q{hr}))
                Gen.p{hr} Gen.q{hr} = Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false j{hr} false Gen.p{hr} Gen.q{hr}.
    - by rewrite /Phi7p.
    have hS' : forall r, (invperm RE.FunRO.f{hr} (nth witness pairs0 j{hr}).`1 y1{hr}, (nth witness pairs0 j{hr}).`2) \notin RS.RO.m{hr} => RS.RO.m{hr}.[(invperm RE.FunRO.f{hr} (nth witness pairs0 j{hr}).`1 y1{hr}, (nth witness pairs0 j{hr}).`2) <- r].[(Gen.e{hr}, Gen.q{hr})] = Some Gen.sd{hr}.
    - by move=> r hz; rewrite get_set_neqE //; apply/negP => h; move: hz; rewrite -h domE hS.
    case: (Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false j{hr} false Gen.p{hr} Gen.q{hr} = 1%r) => hA.
    - rewrite hA; apply (xle_trans (Ep dseed (fun _ => 1%xr))); 2: by rewrite EpC dseed_ll smul1m.
      apply le_Ep => r _ /=; case: ((invperm RE.FunRO.f{hr} (nth witness pairs0 j{hr}).`1 y1{hr}, (nth witness pairs0 j{hr}).`2) \in RS.RO.m{hr}) => hz /=.
      + by apply xle_cxr_l; [smt() | apply xr_le; apply Psi7p_le1].
      apply xle_cxr_l; 2: by apply xr_le; apply Psi7p_le1.
      by rewrite hS' //= get_set_sameE /=; do !split => //; move=> hr0; apply sinv7_set.
    have [hnc [hin hji]] : !coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr} /\ (Gen.p{hr}, Gen.q{hr}) \in pairs0 /\
                           j{hr} <= index (Gen.p{hr}, Gen.q{hr}) pairs0.
    - by move: hA; rewrite /Phi7p /=; smt().
    case: (j{hr} = index (Gen.p{hr}, Gen.q{hr}) pairs0) => hji2.
    - have hv : nth witness pairs0 j{hr} = (Gen.p{hr}, Gen.q{hr}) by rewrite hji2 nth_index.
      have hxe : (invperm RE.FunRO.f{hr} (nth witness pairs0 j{hr}).`1 y1{hr}, (nth witness pairs0 j{hr}).`2) = (Gen.e{hr}, Gen.q{hr}) by rewrite hv /= he.
      apply (xle_trans (Ep dseed (fun _ => 0%xr))); 2: by rewrite EpC dseed_ll smul1m; apply xr_le; smt().
      apply le_Ep => r _ /=; rewrite hxe domE hS /= hv /=.
      by apply xle_cxr_l; [smt() | rewrite /Psi7p].
    have hne : (invperm RE.FunRO.f{hr} (nth witness pairs0 j{hr}).`1 y1{hr}, (nth witness pairs0 j{hr}).`2) <> (Gen.e{hr}, Gen.q{hr}).
    - have hw : (nth witness pairs0 j{hr}).`1 \in ws0 by move: hall; rewrite allP => /(_ _ hv0).
      have hnth : nth witness pairs0 j{hr} <> (Gen.p{hr}, Gen.q{hr}).
      + by apply/negP => h4; apply hji2; rewrite -h4 index_uniq //; smt().
      move: hnc; rewrite /coll7 he hasP negb_exists /= => /(_ (nth witness pairs0 j{hr}).`1); rewrite hw /=.
      smt().
    have hX := psi7p_le (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) j{hr} Gen.p{hr} Gen.q{hr}.
    case: ((invperm RE.FunRO.f{hr} (nth witness pairs0 j{hr}).`1 y1{hr}, (nth witness pairs0 j{hr}).`2) \in RS.RO.m{hr}) => hz.
    - have hno : oget RS.RO.m{hr}.[(invperm RE.FunRO.f{hr} (nth witness pairs0 j{hr}).`1 y1{hr}, (nth witness pairs0 j{hr}).`2)] <> Gen.sd{hr} by apply hsv.
      apply (xle_trans (Ep dseed (fun _ => (Psi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false false j{hr}
               Gen.p{hr} Gen.q{hr})%xr))).
      + apply le_Ep => r _ /=; rewrite hno /=.
        by apply xle_cxr_l; [smt() | rewrite /Psi7p].
      rewrite EpC dseed_ll smul1m; apply xr_le.
      by have := hX 0%r hmode hj _ _; [smt(e512_gt0) | smt() | smt()].
    apply (xle_trans (Ep dseed (fun r => (if r <> Gen.sd{hr} then
             Psi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false false j{hr} Gen.p{hr} Gen.q{hr} else 1%r)%xr))).
    - apply le_Ep => r _ /=; rewrite get_set_sameE /=.
      case: (r = Gen.sd{hr}) => hr /=.
      + by apply xle_cxr_l; [rewrite hS' //=; smt() | apply xr_le; apply Psi7p_le1].
      apply xle_cxr_l; 2: by rewrite /Psi7p.
      by rewrite hS' //= ?get_set_sameE /=; do !split => //; apply sinv7_set.
    have hP1 := Psi7p_le1 (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false false j{hr} Gen.p{hr} Gen.q{hr} hmode.
    have hP0 : 0%r <= Psi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false false j{hr} Gen.p{hr} Gen.q{hr}.
    - by have := Phi7p_bounds (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode;
         have := tw_bounds hmode; rewrite /Psi7p /=; smt().
    rewrite Ep_two ?dseed_ll //; apply xr_le.
    have hm : mu dseed (fun r => r <> Gen.sd{hr}) = 1%r - inv (2%r ^ 512).
    - rewrite (mu_eq _ _ (predC (pred1 Gen.sd{hr}))) => [r | ]; 1: by rewrite /predC /pred1.
      by rewrite mu_not dseed_ll dseed1.
    by rewrite hm; have := hX (inv (2%r ^ 512)) hmode hj _ _; [smt(e512_gt0) | smt() | smt()].
  have [h0 | [h1 | h2]] : mode0 = 0 \/ mode0 = 1 \/ mode0 = 2 by smt().
  + rcondf 1; 1: by auto => />; smt().
    rcondt 1; 1: by auto => />; smt().
    inline *; auto => &hr /=; apply xle_cxr_r => -[#] hws hp hmd hx he hsd hpp hqq hom hS hT hW hj hnf htv hsv hv hps.
    have [hA0 hA1] := Phi7p_bounds (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode.
    case: (sg{hr} = Gen.sd{hr}) => hsg.
    - apply (xle_trans (Ep ddata (fun _ => (b2r (v{hr} <> (Gen.p{hr}, Gen.q{hr})))%xr))); 2: by rewrite EpC ddata_ll smul1m /Psi7p.
      have hin : Gen.sd{hr} \in RW.RO.m{hr} by rewrite domE hW.
      apply le_Ep => r _ /=; rewrite hsg hin /= hW /= hom /=.
      by apply xle_cxr_l; [rewrite hp; smt() | rewrite /Phi7p].
    have hsv' := hsv hsg.
    apply (xle_trans (Ep ddata (fun r => (Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr} +
             (1%r - Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr}) * b2r (r = om{hr}))%xr))).
    - apply le_Ep => r _ /=; case: (sg{hr} \in RW.RO.m{hr}) => hin /=.
      + have hno : oget RW.RO.m{hr}.[sg{hr}] <> om{hr} by have := htv sg{hr} hsg; smt().
        rewrite hom hno /=; apply xle_cxr_l; 1: by rewrite hp; smt().
        by apply xr_le; rewrite /Phi7p /=; smt(b2r_ge0).
      rewrite get_set_sameE /= hom; case: (r = om{hr}) => hr /=.
      + by apply xle_cxr_l; [rewrite hp; smt(get_setE) | apply xr_le; rewrite /Phi7p /=; smt()].
      apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7p /=; smt().
      have ht' : tinv7 RT.RO.m{hr} RW.RO.m{hr}.[sg{hr} <- r] Gen.sd{hr} om{hr}.
      + by move=> s hs; have := htv s hs; rewrite h0 /= mem_set get_setE; smt().
      by rewrite hp; smt(get_setE).
    rewrite Ep_cbs ?ddata_ll //; 1: smt().
    by apply xr_le; rewrite /Psi7p /= (mu_eq _ _ (pred1 om{hr})) 1:/# ddata1 /tw h0 /=; smt().
  + rcondt 1; 1: by auto => />; smt().
    rcondf 3; 1: by inline *; auto => />; smt().
    inline *; auto => &hr /=; apply xle_cxr_r => -[#] hws hp hmd hx he hsd hpp hqq hom hS hT hW hj hnf htv hsv hv hps.
    have [hA0 hA1] := Phi7p_bounds (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode.
    case: (sg{hr} = Gen.sd{hr}) => hsg.
    - apply (xle_trans (Ep dct (fun _ => (b2r (v{hr} <> (Gen.p{hr}, Gen.q{hr})))%xr))); 2: by rewrite EpC dct_ll smul1m /Psi7p.
      have hin : Gen.sd{hr} \in RT.RO.m{hr} by rewrite domE hT.
      apply le_Ep => r _ /=; rewrite hsg hin /= hT /=.
      by apply xle_cxr_l; [rewrite hp; smt() | rewrite /Phi7p].
    have hsv' := hsv hsg.
    apply (xle_trans (Ep dct (fun (r : W16.word * W240.word) => (Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr} +
             (1%r - Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr}) * b2r (r.`1 = zero16))%xr))).
    - apply le_Ep => r _ /=; case: (sg{hr} \in RT.RO.m{hr}) => hin /=.
      + have hno : (oget RT.RO.m{hr}.[sg{hr}]).`1 <> zero16 by have := htv sg{hr} hsg; smt().
        rewrite hno /=; apply xle_cxr_l; 1: by rewrite hp; smt().
        by apply xr_le; rewrite /Phi7p /=; smt(b2r_ge0).
      rewrite get_set_sameE /=; case: (r.`1 = zero16) => hr /=.
      + by apply xle_cxr_l; [rewrite hp; smt(get_setE) | apply xr_le; rewrite /Phi7p /=; smt()].
      apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7p /=; smt().
      have ht' : tinv7 RT.RO.m{hr}.[sg{hr} <- r] RW.RO.m{hr} Gen.sd{hr} om{hr}.
      + by move=> s hs; have := htv s hs; rewrite h1 /= mem_set get_setE; smt().
      by rewrite hp; smt(get_setE).
    rewrite Ep_cbs ?dct_ll //; 1: smt().
    have hm : mu dct (fun (r : W16.word * W240.word) => r.`1 = zero16) = pk.
    + by rewrite /dct (dprodEl W16.DWord.dunifin W240.DWord.dunifin (fun r => r = zero16)) W240.DWord.dunifin_ll dW16_zero.
    by apply xr_le; rewrite /Psi7p /= hm /tw h1 /pk /=; smt().
  rcondt 1; 1: by auto => />; smt().
  seq 2 : ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\
            xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) ws0 /\ Gen.e = invperm RE.FunRO.f Gen.p y1 /\
            sd = Gen.sd /\ p = Gen.p /\ q = Gen.q /\ om1 = om /\ RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\
            RT.RO.m.[Gen.sd] = Some (zero16, et) /\ RW.RO.m.[Gen.sd] = Some om /\ 0 <= j /\ !found /\
            (sg <> Gen.sd => sinv7 RS.RO.m Gen.e Gen.q Gen.sd) /\ v = nth witness pairs0 j /\ sg \in RT.RO.m /\ (sg = Gen.sd => pass) /\
            (pass => sg <> Gen.sd => sg \in RW.RO.m => oget RW.RO.m.[sg] <> om) /\
            (forall s, s <> Gen.sd => (s <> sg \/ !pass) =>
               (s \in RT.RO.m => (oget RT.RO.m.[s]).`1 = zero16 => s \in RW.RO.m) /\
               (s \in RW.RO.m => oget RW.RO.m.[s] <> om) /\ (s \in RW.RO.m => s \in RT.RO.m))) `|`
           (if pass then
              (if sg = Gen.sd then b2r (v <> (Gen.p, Gen.q))
               else if sg \in RW.RO.m then Phi7p (coll7 RE.FunRO.f y1 Gen.p) false (j + 1) false Gen.p Gen.q
               else Phi7p (coll7 RE.FunRO.f y1 Gen.p) false (j + 1) false Gen.p Gen.q +
                    (1%r - Phi7p (coll7 RE.FunRO.f y1 Gen.p) false (j + 1) false Gen.p Gen.q) * inv (2%r ^ lambda))
            else Phi7p (coll7 RE.FunRO.f y1 Gen.p) false (j + 1) false Gen.p Gen.q)%xr).
  + inline *; auto => &hr /=; apply xle_cxr_r => -[#] hws hp hmd hx he hsd hpp hqq hom hS hT hW hj hnf htv hsv hv hps.
    have [hA0 hA1] := Phi7p_bounds (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode.
    have htv2 : forall s, s <> Gen.sd{hr} =>
                (s \in RT.RO.m{hr} => (oget RT.RO.m{hr}.[s]).`1 = zero16 => s \in RW.RO.m{hr}) /\
                (s \in RW.RO.m{hr} => oget RW.RO.m{hr}.[s] <> om{hr}) /\ (s \in RW.RO.m{hr} => s \in RT.RO.m{hr}).
    - by move=> s hs; have := htv s hs; rewrite h2.
    case: (sg{hr} = Gen.sd{hr}) => hsg.
    - apply (xle_trans (Ep dct (fun _ => (b2r (v{hr} <> (Gen.p{hr}, Gen.q{hr})))%xr))); 2: by rewrite EpC dct_ll smul1m /Psi7p.
      have hin : Gen.sd{hr} \in RT.RO.m{hr} by rewrite domE hT.
      apply le_Ep => r _ /=; rewrite hsg hin /= hT /=.
      by apply xle_cxr_l; [rewrite hp; smt() | done].
    apply (xle_trans (Ep dct (fun (r : W16.word * W240.word) => (Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr} +
             ((1%r - Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr}) * inv (2%r ^ lambda)) *
             b2r (r.`1 = zero16))%xr))).
    - have hl : 0%r <= inv (2%r ^ lambda) by smt(expr_gt0 invr_gt0).
      apply le_Ep => r _ /=; case: (sg{hr} \in RT.RO.m{hr}) => hin /=.
      + have [h21 [h22 h23]] := htv2 sg{hr} hsg.
        case: ((oget RT.RO.m{hr}.[sg{hr}]).`1 = zero16) => hc /=.
        * have hw := h21 hin hc; rewrite hw /=.
          apply xle_cxr_l; [rewrite hp; smt() | apply xr_le; smt(b2r_ge0)].
        by apply xle_cxr_l; [rewrite hp; smt() | apply xr_le; smt(b2r_ge0)].
      have hnw : sg{hr} \notin RW.RO.m{hr} by have [_ [_ h23]] := htv2 sg{hr} hsg; smt().
      rewrite get_set_sameE /=; case: (r.`1 = zero16) => hr /=.
      + rewrite hnw /=; apply xle_cxr_l; 2: by apply xr_le; rewrite /=.
        by rewrite hp; smt(get_setE mem_set).
      by apply xle_cxr_l; [rewrite hp; smt(get_setE mem_set) | apply xr_le; rewrite /=].
    rewrite Ep_cbs ?dct_ll //; 1: smt(expr_gt0 invr_gt0).
    have hm : mu dct (fun (r : W16.word * W240.word) => r.`1 = zero16) = pk.
    + by rewrite /dct (dprodEl W16.DWord.dunifin W240.DWord.dunifin (fun r => r = zero16)) W240.DWord.dunifin_ll dW16_zero.
    have ht : tw mode0 = inv (2%r ^ lambda) * pk.
    + rewrite /tw h2 /pk /= RField.exprD_nneg; [smt(gt0_lambda) | done |].
      by rewrite RField.invrM //; smt(expr_gt0).
    by apply xr_le; rewrite /Psi7p /= hm ht; smt().
  if.
  + inline *; auto => &hr /=; apply xle_cxr_r => -[[hps _] [#] hws hp hmd hx he hsd hpp hqq hom hS hT hW hj
      hnf hsv hv hsT hsd2 hsw hall2].
    have [hA0 hA1] := Phi7p_bounds (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) (j{hr} + 1) Gen.p{hr} Gen.q{hr} hmode.
    have ht' : forall (mW : (seed, data) fmap), (forall s, s <> Gen.sd{hr} => s <> sg{hr} => mW.[s] = RW.RO.m{hr}.[s]) =>
               sg{hr} \in mW => oget mW.[sg{hr}] <> om{hr} => (forall s, s \in RW.RO.m{hr} => s \in mW) =>
               tinv7 RT.RO.m{hr} mW Gen.sd{hr} om{hr}.
    - move=> mW heq hin hne hsub s hs; rewrite h2 /=.
      case: (s = sg{hr}) => hss.
      + by rewrite hss hin /=; split; [smt() | rewrite -hss; smt()].
      have [h21 [h22 h23]] := hall2 s hs _; 1: by left.
      by rewrite /dom (heq s hs hss); smt().
    case: (sg{hr} = Gen.sd{hr}) => hsg.
    - apply (xle_trans (Ep ddata (fun _ => (b2r (v{hr} <> (Gen.p{hr}, Gen.q{hr})))%xr))); 2: by rewrite EpC ddata_ll smul1m hps /=.
      have hin : Gen.sd{hr} \in RW.RO.m{hr} by rewrite domE hW.
      apply le_Ep => r _ /=; rewrite hsg hin /= hW /= hom /=.
      by apply xle_cxr_l; [rewrite hp; smt() | rewrite /Phi7p].
    have hsv' := hsv hsg.
    case: (sg{hr} \in RW.RO.m{hr}) => hin.
    - have hno : oget RW.RO.m{hr}.[sg{hr}] <> om{hr} by smt().
      apply (xle_trans (Ep ddata (fun _ => (Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr})%xr))).
      + apply le_Ep => r _ /=; rewrite hom hno /=.
        apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7p (_ : found{hr} = false) 1:/#.
        by rewrite hp; have := ht' RW.RO.m{hr} _ hin hno _ => //; smt().
      by rewrite EpC ddata_ll smul1m ?hps.
    apply (xle_trans (Ep ddata (fun r => (Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr} +
             (1%r - Phi7p (coll7 RE.FunRO.f{hr} y1{hr} Gen.p{hr}) false (j{hr} + 1) false Gen.p{hr} Gen.q{hr}) * b2r (r = om{hr}))%xr))).
    - apply le_Ep => r _ /=; rewrite ?hin /= get_set_sameE /= hom; case: (r = om{hr}) => hr /=.
      + by apply xle_cxr_l; [rewrite hp; smt(get_setE) | apply xr_le; rewrite /Phi7p /=; smt()].
      apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7p /=; smt().
      have := ht' RW.RO.m{hr}.[sg{hr} <- r] _ _ _ _; 1: by move=> s _ hs; rewrite get_setE hs.
      + by rewrite mem_set.
      + by rewrite get_set_sameE.
      + by move=> s; rewrite mem_set => ->.
      by rewrite hp; smt(get_setE).
    rewrite Ep_cbs ?ddata_ll //; 1: smt().
    by apply xr_le; rewrite ?hps ?hsg ?hin /= (mu_eq _ _ (pred1 om{hr})) 1:/# ddata1; smt().
  auto => &hr /=; apply xle_cxr_r => -[hnp [#] hws hp hmd hx he hsd hpp hqq hom hS hT hW hj
    hnf hsv hv hsT hsd2 hsw hall2].
  have hnp' : !pass{hr} by smt().
  rewrite hnp' /=; apply xle_cxr_l; 2: by apply xr_le; rewrite /Phi7p (_ : found{hr} = false) 1:/#.
  rewrite hp /=; do !split => //; 1: smt().
  move=> _; split; 2: by apply hsv; smt().
  move=> s hs; rewrite h2 /=; have := hall2 s hs _; [by right | smt()].
wp.
while ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\ 0 <= j <= size ws0 /\
        xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) (take j ws0) /\
        s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
        Gen.e = invperm RE.FunRO.f Gen.p y1 /\ sd = Gen.sd /\ p = Gen.p /\ q = Gen.q /\ om1 = om /\
        RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\ RT.RO.m.[Gen.sd] = Some (zero16, et) /\
        RW.RO.m.[Gen.sd] = Some om /\ tinv7 RT.RO.m RW.RO.m Gen.sd om /\ sinv7 RS.RO.m Gen.e Gen.q Gen.sd) `|`
       (Phi7p (coll7 RE.FunRO.f y1 Gen.p) false 0 false Gen.p Gen.q)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hws hp hmd hj0 hj1 hx hs11 he hsd hpp hqq hom hS hT hW htv hsv.
  apply xle_cxr_l; 2: by rewrite /Phi7p.
  by rewrite hx (_ : j{hr} = size ws0) 1:/# take_size; smt().
- wp; while ((MatchP.ws = ws0 /\ MatchP.pairs = pairs0 /\ MatchP.mode = mode0 /\ 0 <= j < size ws0 /\
              xsl = map (fun w => (w, invperm RE.FunRO.f w y1)) (take j ws0) /\
              s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
              Gen.e = invperm RE.FunRO.f Gen.p y1 /\ sd = Gen.sd /\ p = Gen.p /\ q = Gen.q /\ om1 = om /\
              RS.RO.m.[(Gen.e, Gen.q)] = Some Gen.sd /\ RT.RO.m.[Gen.sd] = Some (zero16, et) /\
              RW.RO.m.[Gen.sd] = Some om /\ tinv7 RT.RO.m RW.RO.m Gen.sd om /\ sinv7 RS.RO.m Gen.e Gen.q Gen.sd /\
              w = nth witness ws0 j /\ -1 <= i <= 11 /\
              z = foldl (fun (u : state) k => unround (mask RE.FunRO.f w (rd k) u.`1) u) y1
                        (rev (iota_ (i + 1) (11 - i)))) `|` (Phi7p (coll7 RE.FunRO.f y1 Gen.p) false 0 false Gen.p Gen.q)%xr).
  + move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hws hp hmd hj0 hj1 hx hs11 he hsd hpp hqq hom hS hT hW htv hsv
      hw hi0 hi1 hz /=.
    apply xle_cxr_l; 2: by [].
    have hi : i{hr} = -1 by smt().
    have hzx : z{hr} = invperm RE.FunRO.f{hr} w{hr} y1{hr} by rewrite hz hi /invperm.
    have hxs : rcons xsl{hr} (w{hr}, z{hr}) =
               map (fun w0 => (w0, invperm RE.FunRO.f{hr} w0 y1{hr})) (take (j{hr} + 1) ws0).
    - by rewrite (take_nth witness) 1:/# map_rcons hx /= hzx hw.
    by rewrite hws; smt().
  + inline *; auto => &hr /=; apply xle_cxr_r => -[hc [#] hws hp hmd hj0 hj1 hx hs11 he hsd hpp hqq hom hS hT hW htv hsv
      hw hi0 hi1 hz].
    have hstep : forall s0, s0 = salt_of (RE.FunRO.f{hr} (PB (rd i{hr}, z{hr}.`1))) =>
      unround (mask_of (RE.FunRO.f{hr} (PH (key_of (RE.FunRO.f{hr} (PA (w{hr}, s0))), rd i{hr}, z{hr}.`1)))) z{hr} =
      foldl (fun (u : state) k => unround (mask RE.FunRO.f{hr} w{hr} (rd k) u.`1) u) y1{hr}
            (rev (iota_ i{hr} (11 - (i{hr} - 1)))).
    - move=> s0 ->; rewrite (_ : 11 - (i{hr} - 1) = (11 - i{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons -hz.
      by rewrite /mask.
    case: (i{hr} = 11) => hi11 /=.
    - apply xle_cxr_l; 2: by [].
      have hz1 : z{hr} = y1{hr} by rewrite hz hi11 /= iota0.
      have h := hstep s11{hr} _; 1: by rewrite hs11 hz1 hi11.
      by rewrite h; smt().
    apply xle_cxr_l; 2: by [].
    have h := hstep (salt_of (RE.FunRO.f{hr} (PB (rd i{hr}, z{hr}.`1)))) _ => //.
    by rewrite h; smt().
  auto => &hr /=; apply xle_cxr_r => -[hc [#] hws hp hmd hj0 hj1 hx hs11 he hsd hpp hqq hom hS hT hW htv hsv].
  by apply xle_cxr_l => //; rewrite hws iota0 /=; smt().
inline *; wp.
conseq (_ : _ ==> (y2 = invperm RE.FunRO.f Gen.p y /\ RS.RO.m = empty /\ RT.RO.m = empty /\ RW.RO.m = empty) `|`
                  (Phi7p (coll7 RE.FunRO.f y Gen.p) false 0 false Gen.p Gen.q)%xr).
- move=> _; apply xle_cxr_l => // p2 q0 sd0 m1 m2 m3 f om2 y6 y2_0; apply xle_cxr_r => -[#] hy h1 h2 h3 /=.
  apply (xle_trans (Ep W240.DWord.dunifin (fun _ => (Phi7p (coll7 f y6 p2) false 0 false p2 q0)%xr))).
  + apply le_Ep => et0 _ /=; apply xle_cxr_l => //.
    rewrite h1 h2 h3 hy /= !get_set_sameE take0 size_ge0 /=; split.
    * by rewrite /tinv7 => s hs; rewrite !mem_set !mem_empty hs.
    by move=> x; rewrite mem_set mem_empty /= => ->.
  by rewrite EpC W240.DWord.dunifin_ll smul1m.
- move=> &hr; apply xle_cxr_r => h.
  exact (h Gen.p{hr} Gen.q{hr} Gen.sd{hr} RS.RO.m{hr} RT.RO.m{hr} RW.RO.m{hr} RE.FunRO.f{hr} om{hr} y{hr} y2{hr}).
while ((p0 = Gen.p /\ -1 <= i0 <= 11 /\ RS.RO.m = empty /\ RT.RO.m = empty /\ RW.RO.m = empty /\
        y2 = foldl (fun (u : state) k => unround (mask RE.FunRO.f Gen.p (rd k) u.`1) u) y
                   (rev (iota_ (i0 + 1) (11 - i0)))) `|` (Phi7p (coll7 RE.FunRO.f y Gen.p) false 0 false Gen.p Gen.q)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hp hi0 hi1 hS hT hW hy.
  by apply xle_cxr_l => //; rewrite hS hT hW hy /= (_ : i0{hr} = -1) 1:/# /invperm.
- auto => &hr /=; apply xle_cxr_r => -[hc [#] hp hi0 hi1 hS hT hW hy].
  apply xle_cxr_l => //; rewrite hp hS hT hW /=; split; 1: smt().
  rewrite (_ : 11 - (i0{hr} - 1) = (11 - i0{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons -hy /=.
  by rewrite /mask.
wp; skip => &hr /=.
have hll : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
- by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
have [ht0 _] := tw_bounds hmode; have he5 := e512_gt0.
apply (xle_trans (Ep (RE.MUniFinFun.dfun (fun (_ : point) => dans)) (fun f => Ep dP (fun (p2 : pw) =>
         Ep dQ (fun (q0 : pp) => Ep dstate (fun y6 => (Phi7p (coll7 f y6 p2) false 0 false p2 q0)%xr)))))).
- apply le_Ep => f _ /=; apply le_Ep => p2 _ /=; apply le_Ep => q0 _ /=; apply le_Ep => y6 _ /=.
  apply (xle_trans (Ep ddata (fun _ => (Phi7p (coll7 f y6 p2) false 0 false p2 q0)%xr))); 2: by rewrite EpC ddata_ll smul1m.
  apply le_Ep => om6 _ /=; apply (xle_trans (Ep dseed (fun _ => (Phi7p (coll7 f y6 p2) false 0 false p2 q0)%xr))).
  + by apply le_Ep => sd6 _ /=; apply xle_cxr_l; [rewrite iota0 | done].
  by rewrite EpC dseed_ll smul1m.
rewrite Ep_swap; apply le_Ep => p2 _ /=; rewrite Ep_swap; apply le_Ep => q0 _ /=; rewrite Ep_swap.
apply (xle_trans (Ep dstate (fun _ => (phi7pb p2 q0)%xr))); 2: by rewrite EpC dstate_ll smul1m.
apply le_Ep => y6 _ /=; case: ((p2, q0) \in pairs0) => hin.
- have hp2 : p2 \in ws0 by move: hall; rewrite allP => /(_ _ hin).
  apply (xle_trans (Ep (RE.MUniFinFun.dfun (fun (_ : point) => dans))
           (fun f => ((index (p2, q0) pairs0)%r * c7 + 1%r * b2r (coll7 f y6 p2))%xr))).
  + apply le_Ep => f _; apply xr_le => /=; rewrite /Phi7p hin /= /c7.
    by case: (coll7 f y6 p2) => hc /=; smt(index_ge0).
  rewrite Ep_cbs ?hll //; 1: by rewrite /c7; smt(index_ge0).
  have hmc : mu (RE.MUniFinFun.dfun (fun (_ : point) => dans)) (fun f => coll7 f y6 p2) <= (size ws0 - 1)%r * deltaX.
  + exact (mu_coll &hr ws0 y6 p2 hwu hp2).
  by apply xr_le; rewrite /phi7pb hin /=; smt().
rewrite (eq_Ep _ _ (fun _ => 1%xr)) => [f _ /= | ]; 1: by rewrite /Phi7p hin.
by rewrite EpC hll smul1m /phi7pb hin.
qed.

local lemma core7p &m : 0 <= mode0 <= 2 => uniq ws0 => uniq pairs0 => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                        * (1%r - j%r * c7 - (size ws0 - 1)%r * deltaX)) 0 (size pairs0)
  <= Pr[R.MainD(V7p, RE.FunRO).distinguish() @ &m : res].
proof.
move=> hmode hwu hu hall; have [ht0 ht1] := tw_bounds hmode.
have hdx : 0%r <= deltaX by rewrite /deltaX; smt(expr_gt0 invr_gt0).
have hc7 : 0%r <= c7 by rewrite /c7; smt(e512_gt0).
pose g := fun (z : pw * pp) => (size ws0 - 1)%r * deltaX + (index z pairs0)%r * c7.
have hS := sum_pairs pairs0 g hu.
have hR : bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
             * (1%r - g (nth witness pairs0 j))) 0 (size pairs0) =
          bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
             * (1%r - j%r * c7 - (size ws0 - 1)%r * deltaX)) 0 (size pairs0).
- by apply eq_big_int => j hj /=; rewrite /g index_uniq // 1:/#; ring.
move: hS; rewrite hR => hS.
have hg : forall z, 0%r <= (if z \in pairs0 then g z else 1%r).
- move=> z; case: (z \in pairs0) => hz //=.
  have : z.`1 \in ws0 by move: hall; rewrite allP => /(_ _ hz).
  by rewrite /g; smt(index_mem index_ge0 mulr_ge0).
have hE : Ep dP (fun p => Ep dQ (fun q => (phi7pb p q)%xr)) <=
          (1%r - bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                                      * (1%r - j%r * c7 - (size ws0 - 1)%r * deltaX)) 0 (size pairs0))%xr.
- apply (xle_trans (Ep dP (fun p => Ep dQ (fun q => ((fun (z : pw * pp) =>
           if z \in pairs0 then g z else 1%r) (p, q))%xr)))).
  + by apply le_Ep => p _ /=; apply le_Ep => q _; apply xr_le => /=; rewrite /phi7pb /g.
  by rewrite Ep_dPQ // hS.
have hll : islossless R.MainD(V7p, RE.FunRO).distinguish.
- have hdf : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
  + by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
  proc; inline V7p(RE.FunRO).distinguish D7p(IPG7(RE.FunRO)).run; wp.
  call (matchp_ll (CountP(IPG7(RE.FunRO))) _ _ _ _ _ _).
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto.
  + by proc; inline *; auto; smt(dseed_ll).
  + by proc; inline *; auto; smt(dct_ll).
  + by proc; inline *; auto; smt(ddata_ll).
  inline *; wp; rnd; wp; while true (i + 1); 1: by auto => /#.
  by auto => />; smt(dP_ll dQ_ll dstate_ll ddata_ll dseed_ll W240.DWord.dunifin_ll).
have h1 : Pr[R.MainD(V7p, RE.FunRO).distinguish() @ &m : !res] <=
          1%r - bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                                     * (1%r - j%r * c7 - (size ws0 - 1)%r * deltaX)) 0 (size pairs0).
- byehoare (_ : (Ep dP (fun p => Ep dQ (fun q => (phi7pb p q)%xr))) ==> (!res)%xr) => //.
  + exact (core7p_e hmode hwu hu hall).
  rewrite -hS; apply Bigreal.sumr_ge0 => z _ /=.
  by apply mulr_ge0; [apply mulr_ge0; apply ge0_mu | apply hg].
have h2 : Pr[R.MainD(V7p, RE.FunRO).distinguish() @ &m : true] = 1%r by byphoare => //; apply hll.
have h3 : Pr[R.MainD(V7p, RE.FunRO).distinguish() @ &m : !res] =
          Pr[R.MainD(V7p, RE.FunRO).distinguish() @ &m : true] - Pr[R.MainD(V7p, RE.FunRO).distinguish() @ &m : res].
- by rewrite Pr[mu_not].
smt().
qed.

(* Pair game: the output is the pair (P, Q); cut rule, no refusal. *)
lemma W7_pair_cut &m :
  0 <= mode0 <= 2 => uniq ws0 => uniq pairs0 => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  mass2 pairs0 * (1%r - (size pairs0 - 1)%r * (tw mode0 + inv (2%r ^ 512)) - (size ws0 - 1)%r * deltaX)
    - deltacut (size pairs0) (if mode0 = 0 then 0 else size pairs0)
  <= Pr[GameP(Setup0P(Seq), MatchP).main() @ &m : res.`2 = (Gen.p, Gen.q)].
proof.
move=> hmode hwu hu hall hws hp hmd.
have /= h1 := red7 (fun (out : seed * (pw * pp)) (p : pw) (q : pp) _ _ => out.`2 = (p, q)) &m hmode hws hp hmd.
have h2 := eager7p &m.
have h3 := core7p &m hmode hwu hu hall.
have h4 : mass2 pairs0 * (1%r - (size pairs0 - 1)%r * c7 - (size ws0 - 1)%r * deltaX) <=
          bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                               * (1%r - j%r * c7 - (size ws0 - 1)%r * deltaX)) 0 (size pairs0).
- rewrite /mass2 (StdBigop.Bigreal.BRA.big_nth witness) StdBigop.Bigreal.BRA.mulr_suml.
  apply StdBigop.Bigreal.ler_sum_seq => j /mem_range hj _ /=.
  apply ler_wpmul2l; 1: by apply mulr_ge0; apply ge0_mu.
  have : j%r <= (size pairs0 - 1)%r by smt().
  have : 0%r <= c7 by rewrite /c7; smt(tw_bounds e512_gt0).
  smt().
have -> : tw mode0 + inv (2%r ^ 512) = c7 by done.
smt().
qed.
end section W7.

(* ---- Proposition W7 for every covered rule ----------------------------------------------------- *)
section W7R.
declare op ws0 : pw list.
declare op pairs0 : (pw * pp) list.
declare op mode0 : int.
declare module Rl <: RULE {-R.RO, -RS.RO, -RS.FRO, -RSE.FunRO, -RT.RO, -RT.FRO, -RTE.FunRO, -RW.RO,
                           -Trials, -Gen, -Count, -CountP, -MatchP}.
declare axiom Rl_pass (T <: TRIALS {-Rl, -Trials}) :
  hoare [Rl(Rec(T)).select : Trials.outs = [] ==>
           0 <= res < size Trials.outs /\ nth false Trials.outs res].
declare axiom Rl_ll (T <: TRIALS {-Rl}) (P : glob T -> bool) (b : real) :
  0%r < b => phoare [T.trial : P (glob T) ==> P (glob T) /\ res] = b =>
  phoare [T.trial : P (glob T) ==> P (glob T)] = 1%r =>
  phoare [Rl(T).select : P (glob T) ==> true] = 1%r.
declare module Rf <: AFTERP {-Gen}.
declare axiom Rf_ll : islossless Rf.run.

(* Seed game, with the pairs in the order of [pairs0]. *)
lemma W7_seed &m :
  0 <= mode0 <= 2 => uniq ws0 => uniq pairs0 => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                        * (1%r - j%r * tw mode0)) 0 (size pairs0)
    - deltagen (size pairs0) (if mode0 = 0 then 0 else size pairs0) - inv (2%r ^ 256)
  <= Pr[GamePR(Setup0P(Rl), MatchP, Rf).main() @ &m : res.`1 = Gen.sd].
proof.
move=> hmode hwu hu hall hws hp hmd.
have h1 := rule_lo (fun (out : seed * (pw * pp)) _ _ (sd : seed) => out.`1 = sd) Rl Rl_pass Rl_ll
             MatchP matchp_ll Rf Rf_ll &m.
have h2 := W7_seed_cut ws0 pairs0 mode0 &m hmode hwu hu hall hws hp hmd.
have h3 := deltacut_le (size pairs0) (if mode0 = 0 then 0 else size pairs0) _ _; 1,2: smt(size_ge0).
by move: h1 h2 h3 => /=; smt(expr_gt0 invr_gt0).
qed.

(* Pair game: the output is the pair (P, Q). *)
lemma W7_pair &m :
  0 <= mode0 <= 2 => uniq ws0 => uniq pairs0 => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  mass2 pairs0 * (1%r - (size pairs0 - 1)%r * (tw mode0 + inv (2%r ^ 512)) - (size ws0 - 1)%r * deltaX)
    - deltagen (size pairs0) (if mode0 = 0 then 0 else size pairs0) - inv (2%r ^ 256)
  <= Pr[GamePR(Setup0P(Rl), MatchP, Rf).main() @ &m : res.`2 = (Gen.p, Gen.q)].
proof.
move=> hmode hwu hu hall hws hp hmd.
have h1 := rule_lo (fun (out : seed * (pw * pp)) (p : pw) (q : pp) _ => out.`2 = (p, q)) Rl Rl_pass Rl_ll
             MatchP matchp_ll Rf Rf_ll &m.
have h2 := W7_pair_cut ws0 pairs0 mode0 &m hmode hwu hu hall hws hp hmd.
have h3 := deltacut_le (size pairs0) (if mode0 = 0 then 0 else size pairs0) _ _; 1,2: smt(size_ge0).
by move: h1 h2 h3 => /=; smt(expr_gt0 invr_gt0).
qed.

(* The two games in the form of the text, for each of the three tests: the passwords w_1 ... w_m and
   at most n pairs among them of total probability top2(m, n). Mode 0 is the text's statement with
   2^-lambda; modes 1 and 2 put 2^-16 and 2^-(lambda + 16) in its place. *)
lemma W7_top2 &m (m n : int) :
  1 <= m => 1 <= n => 0 <= mode0 <= 2 => ws0 = take m ranked => m <= PwT.card =>
  uniq pairs0 => size pairs0 <= n => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  mass2 pairs0 = top2 m n =>
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  top2 m n * (1%r - (n - 1)%r * tw mode0) - deltagen n (if mode0 = 0 then 0 else n) - inv (2%r ^ 256)
    <= Pr[GamePR(Setup0P(Rl), MatchP, Rf).main() @ &m : res.`1 = Gen.sd] /\
  top2 m n * (1%r - (n - 1)%r * (tw mode0 + inv (2%r ^ 512)) - (m - 1)%r * deltaX)
    - deltagen n (if mode0 = 0 then 0 else n) - inv (2%r ^ 256)
    <= Pr[GamePR(Setup0P(Rl), MatchP, Rf).main() @ &m : res.`2 = (Gen.p, Gen.q)].
proof.
move=> hm hn hmode hws hmc hu hsz hall hmass hws' hp' hmd'.
have hwu : uniq ws0 by rewrite hws; apply uniq_take; rewrite /ranked sort_uniq PwT.enum_uniq.
have hsw : size ws0 = m.
- rewrite hws size_take; 1: smt().
  by rewrite /ranked size_sort /PwT.card; smt().
have ht : 0%r <= tw mode0 by rewrite /tw; smt(expr_gt0 invr_gt0).
have hX : 0%r <= deltaX by rewrite /deltaX; smt(expr_gt0 invr_gt0).
have hd := deltagen_mono (size pairs0) n (if mode0 = 0 then 0 else size pairs0)
             (if mode0 = 0 then 0 else n) hsz _; 1: smt().
have h0 : 0%r <= top2 m n by rewrite -hmass /mass2; apply StdBigop.Bigreal.sumr_ge0 => z _ /=; smt(ge0_mu).
split.
- have h := W7_seed &m hmode hwu hu hall hws' hp' hmd'.
  have hs : top2 m n * (1%r - (n - 1)%r * tw mode0) <=
            bigi predT (fun j => mu1 dP (nth witness pairs0 j).`1 * mu1 dQ (nth witness pairs0 j).`2
                                 * (1%r - j%r * tw mode0)) 0 (size pairs0).
  + rewrite -hmass /mass2 (StdBigop.Bigreal.BRA.big_nth witness) StdBigop.Bigreal.BRA.mulr_suml.
    apply StdBigop.Bigreal.ler_sum_seq => j /mem_range hj _ /=.
    apply ler_wpmul2l; 1: by apply mulr_ge0; apply ge0_mu.
    have : j%r <= (n - 1)%r by smt().
    smt().
  smt().
have h := W7_pair &m hmode hwu hu hall hws' hp' hmd'.
have : top2 m n * (1%r - (n - 1)%r * (tw mode0 + inv (2%r ^ 512)) - (m - 1)%r * deltaX) <=
       mass2 pairs0 * (1%r - (size pairs0 - 1)%r * (tw mode0 + inv (2%r ^ 512)) - (size ws0 - 1)%r * deltaX).
- rewrite hmass hsw; apply ler_wpmul2l => //.
  have : (size pairs0 - 1)%r <= (n - 1)%r by smt().
  have : 0%r <= tw mode0 + inv (2%r ^ 512) by smt(expr_gt0 invr_gt0).
  smt().
smt().
qed.

(* Proposition W7 and Theorem 5 bracket the best attack on the seed: with the m likeliest passwords
   and at most n pairs of total probability top2(m, n), the attack succeeds with a probability
   between the bound of W7 and the bound of Theorem 5 at k_A = 12m and k_S = n. *)
lemma W7_bracket &m (m n : int) :
  1 <= m => 1 <= n => 0 <= mode0 <= 2 => ws0 = take m ranked => m <= PwT.card =>
  uniq pairs0 => size pairs0 <= n => all (fun (x : pw * pp) => x.`1 \in ws0) pairs0 =>
  mass2 pairs0 = top2 m n =>
  MatchP.ws{m} = ws0 => MatchP.pairs{m} = pairs0 => MatchP.mode{m} = mode0 =>
  top2 m n * (1%r - (n - 1)%r * tw mode0) - deltagen n (if mode0 = 0 then 0 else n) - inv (2%r ^ 256)
    <= Pr[GamePR(Setup0P(Rl), MatchP, Rf).main() @ &m : res.`1 = Gen.sd] /\
  Pr[GamePR(Setup0P(Rl), MatchP, Rf).main() @ &m : res.`1 = Gen.sd] <=
    top2 m n + epsW (12 * m) n (11 * m + 1) (12 * m) (if mode0 = 0 then 0 else n)
                    (if mode0 = 1 then 0 else n) + inv (2%r ^ 512).
proof.
move=> hm hn hmode hws hmc hu hsz hall hmass hws' hp' hmd'.
have [hlo _] := W7_top2 &m m n hm hn hmode hws hmc hu hsz hall hmass hws' hp' hmd'.
split => //.
have hsw : size ws0 = m.
- rewrite hws size_take; 1: smt().
  by rewrite /ranked size_sort /PwT.card; smt().
have h1 := rule_up (fun (out : seed * (pw * pp)) _ _ (sd : seed) => out.`1 = sd) Rl Rl_pass Rl_ll
             MatchP matchp_ll Rf Rf_ll &m.
have h2 := W7_upper_cut ws0 pairs0 mode0 &m n hmode hsz hws' hp' hmd'.
have h3 := deltacut_le n (if mode0 = 0 then 0 else n) _ _; 1,2: smt().
by move: h1 h2 h3; rewrite hsw /epsW /=; smt().
qed.
end section W7R.
