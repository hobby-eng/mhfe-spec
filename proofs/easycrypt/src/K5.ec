(* Proposition K5: the matching attack on a known pair (DESIGN-NOTES A.5). *)
require import AllCore List Distr DBool DInterval FMap IntDiv StdBigop StdOrder Xreal.
require import Suite3 Chain Collision KnownPair Delta2 Theorem4.
require RealSeries DProd Mu_mem.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- Proposition K5: the matching attack ----------------------------------------------------- *)
(* For each of the first m candidates, evaluates rounds 11 ... 1 backward from Y and accepts the
   password if the resulting L_1 equals R_0; otherwise outputs the last candidate. The first B point
   (11, L_12) is queried once and shared. *)
module MatchK (O : ABH) = {
  var cands : pw list
  proc guess(x : state, y : state) : pw = {
    var s11, j, w, i, z, s, k, m, found, out;
    s11 <@ O.b(rd 11, y.`1);
    found <- false;
    out <- nth witness cands (size cands - 1);
    j <- 0;
    while (j < size cands - 1 /\ !found) {
      w <- nth witness cands j;
      z <- y;
      i <- 11;
      while (1 <= i) {
        if (i = 11) { s <- s11; } else { s <@ O.b(rd i, z.`1); }
        k <@ O.a(w, s);
        m <@ O.h(k, rd i, z.`1);
        z <- unround m z;
        i <- i - 1;
      }
      if (z.`1 = x.`2) { found <- true; out <- w; }
      j <- j + 1;
    }
    return out;
  }
}.

(* The loss of one wrong candidate: its fresh mask of round 1, or one of its at most eleven keys
   equal to the key of the real path's H point of round 1. *)
op deltaK : real = inv (2%r ^ 128) + 11%r / 2%r ^ 256.

lemma deltaKE : deltaK = e128 + 11%r * e256.
proof. by rewrite /deltaK /e128 /e256. qed.

lemma deltaK_ge0 : 0%r <= deltaK.
proof. by rewrite deltaKE; smt(e128_gt0 e256_gt0). qed.

(* ---- The pair lemma in the lazy oracle ------------------------------------------------------- *)
(* The proof follows the text: whether a wrong candidate w is accepted depends only on the real path
   and on the chain of w, so each candidate is bounded on its own (the pair lemma) and the attack by
   a union bound over the candidates before P on the whole function. *)

(* An A point of w has the key of an H point of round 1. *)
op collK (w : pw) (m : (point, ans) fmap) =
  exists s R, PA (w, s) \in m /\ PH (key_of (oget m.[PA (w, s)]), rd 1, R) \in m.

(* At most n keys among the H points of round 1. *)
op fewH1 (m : (point, ans) fmap) (n : int) =
  exists (L : W256.word list), size L <= n /\ forall k R, PH (k, rd 1, R) \in m => k \in L.

lemma fewH1_set m n c v : (forall k R, c <> PH (k, rd 1, R)) => fewH1 m n => fewH1 m.[c <- v] n.
proof. by move=> hc [L [hs hL]]; exists L; split => // k R; rewrite mem_set => -[h | h]; [apply (hL k R) | smt()]. qed.

lemma fewH1_setH m n k0 R0 v : fewH1 m n => fewH1 m.[PH (k0, rd 1, R0) <- v] (n + 1).
proof. by move=> [L [hs hL]]; exists (k0 :: L); split; [smt() | move=> k R; rewrite mem_set; smt()]. qed.

lemma collK_set w m c v : (forall s, c <> PA (w, s)) => (forall k R, c <> PH (k, rd 1, R)) =>
  collK w m.[c <- v] = collK w m.
proof.
move=> hA hH; rewrite /collK; apply eq_iff; split => -[s R [h1 h2]]; exists s R.
- move: h1 h2; rewrite !mem_set get_set_neqE; 1: by smt().
  by move=> [h1 | h1] [h2 | h2]; smt().
by rewrite !mem_set get_set_neqE; [smt() | smt()].
qed.

lemma collK_setA w s0 (m : (point, ans) fmap) r : PA (w, s0) \notin m =>
  collK w m.[PA (w, s0) <- r] => collK w m \/ exists R, PH (key_of r, rd 1, R) \in m.
proof.
move=> hin [s R [h1 h2]]; move: h1 h2; rewrite !mem_set /=.
case: (s = s0) => [-> | hs] /=; 1: by rewrite get_set_sameE /= => h; right; exists R.
by rewrite get_set_neqE 1:/# => h1 h2; left; exists s R.
qed.

(* A fresh key hits one of n keys with probability at most n e256. *)
lemma mu_fewH1 m n : fewH1 m n => mu dans (fun r => exists R, PH (key_of r, rd 1, R) \in m) <= n%r * e256.
proof.
move=> [L [hs hL]]; apply (ler_trans (mu dans (fun r => key_of r \in L))).
- by apply mu_le => r _ /= [R h]; apply (hL _ R).
rewrite (dans_key (fun k => k \in L)) /=.
apply (ler_trans ((size L)%r * inv (2%r ^ 256))).
- by apply Mu_mem.mu_mem_le_size => k _; rewrite dkey1.
by rewrite /e256; have := e256_gt0; rewrite /e256; smt().
qed.

(* The encryption of x under p, then the test of w: rounds 11 ... 1 backward from the result. *)
module TwoK (G : R.RO) = {
  var p, w : pw
  var x : state
  proc distinguish() : bool = {
    var y, z;
    y <@ Net(Orc(G)).enc(p, x);
    z <@ Part(Orc(G)).bwd(w, y, 11, 1);
    return z.`1 = x.`2;
  }
}.

(* The risk of the test of w before round i, and its outcome after round 1. *)
op phiK (w : pw) (m : (point, ans) fmap) (i : int) (z x : state) : real =
  if i < 1 then b2r (z.`1 = x.`2) else b2r (collK w m) + e128 + i%r * e256.

lemma two_k_e (pv wv : pw) : pv <> wv =>
  ehoare [R.MainD(TwoK, R.RO).distinguish :
    (TwoK.p = pv /\ TwoK.w = wv) `|` deltaK%xr ==> (res)%xr].
proof.
move=> hpw; proc; inline *; wp.
while ((p0 = wv /\ lo = 1 /\ 0 <= i0 <= 11 /\ (1 <= i0 => fewH1 R.RO.m 1)) `|`
       (phiK wv R.RO.m i0 y0 TwoK.x)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hp hlo hi0 hi1 hf.
  by rewrite /phiK (_ : i0{hr} < 1) 1:/#.
- seq 7 : ((p0 = wv /\ lo = 1 /\ 1 <= i0 <= 11 /\ fewH1 R.RO.m 1) `|` (phiK wv R.RO.m i0 y0 TwoK.x)%xr).
  + auto => &hr /=; apply xle_cxr_r => -[hc [#] hp hlo hi0 hi1 hf].
    apply (xle_trans (Ep dans (fun _ => (phiK wv R.RO.m{hr} i0{hr} y0{hr} TwoK.x{hr})%xr))).
    * apply le_Ep => r _ /=; case: (PB (rd i0{hr}, y0{hr}.`1) \in R.RO.m{hr}) => hin /=.
      - by apply xle_cxr_l => //; rewrite hp hlo; smt().
      apply xle_cxr_l.
      - by rewrite hp hlo /=; split; [smt() | apply fewH1_set; [by move=> k R | apply hf; smt()]].
      by rewrite /phiK collK_set.
    by rewrite EpC dans_ll smul1m.
  seq 7 : ((p0 = wv /\ lo = 1 /\ 1 <= i0 <= 11 /\ fewH1 R.RO.m 1 /\ PA (wv, s2) \in R.RO.m /\
            k0 = key_of (oget R.RO.m.[PA (wv, s2)])) `|`
           (b2r (collK wv R.RO.m) + e128 + (i0 - 1)%r * e256)%xr).
  + auto => &hr /=; apply xle_cxr_r => -[#] hp hlo hi0 hi1 hf.
    rewrite /phiK (_ : !(i0{hr} < 1)) 1:/# /= hp hlo.
    case: (PA (wv, s0{hr}) \in R.RO.m{hr}) => hin /=.
    * rewrite EpC dans_ll smul1m; apply xle_cxr_l => //.
      by apply xr_le; smt(e256_gt0).
    apply (xle_trans (Ep dans (fun r => (b2r (collK wv R.RO.m{hr}) + e128 + (i0{hr} - 1)%r * e256 +
             1%r * b2r (exists R, PH (key_of r, rd 1, R) \in R.RO.m{hr}))%xr))).
    * apply le_Ep => r _ /=; apply xle_cxr_l.
      - by rewrite mem_set /=; split; [smt() | apply fewH1_set; [by move=> k R | done]].
      by apply xr_le; have := collK_setA wv s0{hr} R.RO.m{hr} r hin; smt(b2r_ge0).
    rewrite Ep_cbs ?dans_ll //; 1: smt(e128_gt0 e256_gt0 b2r_ge0).
    by apply xr_le; have := mu_fewH1 _ _ hf; smt().
  auto => &hr /=; apply xle_cxr_r => -[#] hp hlo hi0 hi1 hf hA hk.
  case: (i0{hr} = 1) => hz.
  + rewrite hz /= /phiK /=; case: (collK wv R.RO.m{hr}) => hc.
    * apply (xle_trans (Ep dans (fun _ => 1%xr))); 2: by rewrite EpC dans_ll smul1m; apply xr_le; smt(e128_gt0).
      apply le_Ep => r _ /=; case: (PH (k0{hr}, rd 1, y0{hr}.`1) \in R.RO.m{hr}) => hin /=.
      - by apply xle_cxr_l; [rewrite hp hlo | apply xr_le; smt()].
      by apply xle_cxr_l; [rewrite hp hlo | apply xr_le; smt()].
    have hnin : PH (k0{hr}, rd 1, y0{hr}.`1) \notin R.RO.m{hr}.
    * by apply/negP => h; apply hc; exists s2{hr} y0{hr}.`1; rewrite hA -hk.
    rewrite hnin /=; apply (xle_trans (Ep dans (fun r => ((unround (mask_of r) y0{hr}).`1 = TwoK.x{hr}.`2)%xr))).
    * by apply le_Ep => r _ /=; apply xle_cxr_l; [rewrite hp hlo | rewrite get_set_sameE].
    by rewrite Ep_mu mu_mask0; apply xr_le; smt(b2r_ge0).
  rewrite /phiK (_ : !(i0{hr} - 1 < 1)) 1:/# /=.
  apply (xle_trans (Ep dans (fun _ => (b2r (collK wv R.RO.m{hr}) + e128 + (i0{hr} - 1)%r * e256)%xr))).
  + have hne : forall k R, PH (k0{hr}, rd i0{hr}, y0{hr}.`1) <> PH (k, rd 1, R).
    * by move=> k R /=; have := rd_inj i0{hr} 1; smt().
    apply le_Ep => r _ /=; case: (PH (k0{hr}, rd i0{hr}, y0{hr}.`1) \in R.RO.m{hr}) => hin /=.
    * by apply xle_cxr_l; [rewrite hp hlo; smt() | apply xr_le; smt()].
    have hc : collK wv R.RO.m{hr}.[PH (k0{hr}, rd i0{hr}, y0{hr}.`1) <- r] = collK wv R.RO.m{hr}.
    * by apply collK_set => // s.
    apply xle_cxr_l; 1: by rewrite hp hlo /=; split; [smt() | move=> _; apply fewH1_set].
    by rewrite hc; apply xr_le; smt().
  by rewrite EpC dans_ll smul1m.
wp; while ((p = pv /\ TwoK.w = wv /\ 0 <= i <= 12 /\ fewH1 R.RO.m (if i <= 1 then 0 else 1) /\
            forall s, PA (wv, s) \notin R.RO.m) `|` deltaK%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hp hw hi0 hi1 hf hn.
  apply xle_cxr_l; 1: by rewrite hw /=; move: hf; rewrite (_ : !(i{hr} <= 1)) 1:/#.
  have hc0 : !collK wv R.RO.m{hr} by apply/negP; rewrite /collK => -[s R [h _]]; have := hn s; rewrite h.
  by rewrite /phiK /= (negbTE _ hc0) deltaKE /=.
- seq 7 : ((p = pv /\ TwoK.w = wv /\ 0 <= i < 12 /\ fewH1 R.RO.m (if i <= 1 then 0 else 1) /\
            forall s, PA (wv, s) \notin R.RO.m) `|` deltaK%xr).
  + auto => &hr /=; apply Ep_guard => -[hc [#] hp hw hi0 hi1 hf hn]; split => [hnin r | hin] /=.
    * by rewrite hp hw /=; split; [smt() | split; [apply fewH1_set | move=> s; rewrite mem_set hn]].
    by rewrite hp hw /=; smt().
  seq 7 : ((p = pv /\ TwoK.w = wv /\ 0 <= i < 12 /\ fewH1 R.RO.m (if i <= 1 then 0 else 1) /\
            forall s, PA (wv, s) \notin R.RO.m) `|` deltaK%xr).
  + auto => &hr /=; apply Ep_guard => -[#] hp hw hi0 hi1 hf hn; split => [hnin r | hin].
    * by rewrite hp hw /=; split; [smt() | split; [apply fewH1_set | move=> s; rewrite mem_set hn /= /#]].
    by rewrite hp hw /=; smt().
  auto => &hr /=; apply Ep_guard => -[#] hp hw hi0 hi1 hf hn; split => [hnin r | hin].
  + rewrite hp hw /=; split; 1: smt(); split; 2: by move=> s; rewrite mem_set hn.
    case: (i{hr} = 1) => hz.
    * rewrite hz /=; have := fewH1_setH R.RO.m{hr} 0 k{hr} x0{hr}.`2 r _; 2: by [].
      by move: hf; rewrite hz.
    rewrite (_ : (if i{hr} + 1 <= 1 then 0 else 1) = (if i{hr} <= 1 then 0 else 1)) 1:/#.
    by apply fewH1_set => // k R /=; have := rd_inj i{hr} 1; smt().
  rewrite hp hw /=; split; 1: smt(); split => //.
  by move: hf => [L [hs hL]]; exists L; smt().
auto => &hr; apply xle_cxr_r => -[hp hw]; apply xle_cxr_l => //.
by rewrite hp hw /=; split; [exists []; smt(mem_empty) | move=> s; rewrite mem_empty].
qed.

(* ---- The pair lemma over the whole function ---------------------------------------------------- *)
(* The test of a candidate w on the pair (x, y): rounds 11 ... 1 backward from y give L_1 = R_0. *)
op accK f (w : pw) (x y : state) : bool = (bwdp f w y 11 1).`1 = x.`2.

lemma fwdp1_1 f p (x : state) : (fwdp f p x 0 1).`1 = x.`2.
proof. by rewrite (fwdpS _ _ _ 0) // /fwdp iota0 // /round. qed.

(* The real password passes its own test. *)
lemma accK_real f p (x : state) : accK f p x (perm f p x).
proof.
have e : perm f p x = fwdp f p (fwdp f p x 0 1) 1 12.
- by rewrite /perm /fwdp /= (_ : 12 = 11 + 1) // iotaS //= iota1.
have h := bwdp_fwdp f p (fwdp f p x 0 1) 1 12 _; 1: done.
by move: h; rewrite /= => h; rewrite /accK e h fwdp1_1.
qed.

module TwoKM (G : R.RO) = {
  proc main(p w : pw, x : state) : bool = {
    var b;
    TwoK.p <- p; TwoK.w <- w; TwoK.x <- x;
    b <@ R.MainD(TwoK, G).distinguish();
    return b;
  }
}.

module SampK = {
  proc main(p w : pw, x : state) : bool = {
    var f;
    f <$ RE.MUniFinFun.dfun (fun _ => dans);
    return accK f w x (perm f p x);
  }
}.

lemma eager_pairK &m (pv wv : pw) (xv : state) :
  Pr[TwoKM(RE.FunRO).main(pv, wv, xv) @ &m : res] =
  mu (RE.MUniFinFun.dfun (fun _ => dans)) (fun f => accK f wv xv (perm f pv xv)).
proof.
have -> : Pr[TwoKM(RE.FunRO).main(pv, wv, xv) @ &m : res] = Pr[SampK.main(pv, wv, xv) @ &m : res].
- byequiv (_ : ={arg} /\ arg{1} = (pv, wv, xv) ==> ={res}) => //.
  proc; inline R.MainD(TwoK, RE.FunRO).distinguish TwoK(RE.FunRO).distinguish RE.FunRO.init.
  seq 6 1 : (RE.FunRO.f{1} = f{2} /\ TwoK.p{1} = pv /\ TwoK.w{1} = wv /\ TwoK.x{1} = xv /\
             p{2} = pv /\ w{2} = wv /\ x{2} = xv).
  + by wp; rnd; wp; skip => />.
  exlim RE.FunRO.f{1} => f0.
  wp; call{1} (bwd_fun_ph wv (perm f0 pv xv) 11 1); call{1} (enc_fun_ph pv xv).
  by skip => />; rewrite /accK.
by byphoare (_ : arg = (pv, wv, xv) ==> _) => //; proc; rnd; skip => />.
qed.

(* The pair lemma for a known pair. *)
lemma pairK &m (p w : pw) (x : state) : p <> w =>
  mu (RE.MUniFinFun.dfun (fun _ => dans)) (fun f => accK f w x (perm f p x)) <= deltaK.
proof.
move=> hpw; rewrite -(eager_pairK &m).
have <- : Pr[TwoKM(R.RO).main(p, w, x) @ &m : res] = Pr[TwoKM(RE.FunRO).main(p, w, x) @ &m : res].
- by byequiv (_ : ={arg} ==> ={res}) => //; proc; call (RO_FunRO TwoK); auto.
byehoare (_ : (arg = (p, w, x)) `|` deltaK%xr ==> (res)%xr) => //.
- proc; call (two_k_e p w hpw); auto => &hr; apply xle_cxr_r => h.
  by apply xle_cxr_l => //; move: h => /= [-> [-> _]].
smt(deltaK_ge0).
qed.

(* ---- The attack on the whole function ---------------------------------------------------------- *)
(* Δ0 as a program on the oracle; x is stored in DK. *)
module DK (G : R.RO) = {
  var x : state
  proc distinguish() : bool = {
    var p, y, b;
    p <$ dP;
    y <@ Net(Orc(G)).enc(p, x);
    Count(Orc(G)).init();
    b <@ PlayK(MatchK, Count(Orc(G))).play(p, x, y);
    return b;
  }
}.

module DKM (G : R.RO) = {
  proc main(x : state) : bool = {
    var b;
    DK.x <- x;
    b <@ R.MainD(DK, G).distinguish();
    return b;
  }
}.

(* With the function fixed the tests are deterministic: each candidate before P still to be tested
   is accepted exactly when accK holds. *)
op SK (f : point -> ans) (x y : state) (ws : pw list) (p : pw) (j : int) : real =
  bigi predT (fun i => b2r (accK f (nth witness ws i) x y)) j (index p ws).

op PhiK (f : point -> ans) (x y : state) (ws : pw list) (found : bool) (out : pw) (j : int) (p : pw) : real =
  if found then b2r (out <> p) else if p \in ws /\ j <= index p ws then SK f x y ws p j else 1%r.

op phiKs (ws : pw list) (p : pw) : real = if p \in ws then (index p ws)%r * deltaK else 1%r.

(* The potential at the start: every candidate before P is still to be tested. *)
op PhiKb (f : point -> ans) (x : state) (ws : pw list) (p : pw) : real =
  if p \in ws then SK f x (perm f p x) ws p 0 else 1%r.

lemma SK_ge0 f x y ws p j : 0%r <= SK f x y ws p j.
proof. by rewrite /SK; apply Bigreal.sumr_ge0 => i _; apply b2r_ge0. qed.

lemma coreK_e (ws : pw list) (M : int) : uniq ws => size ws = M + 1 => 0 <= M =>
  ehoare [DKM(RE.FunRO).main :
    (MatchK.cands = ws) `|` (Ep dP (fun p => (phiKs ws p)%xr)) ==> (!res)%xr].
proof.
move=> hu hs hM; proc.
inline R.MainD(DK, RE.FunRO).distinguish DK(RE.FunRO).distinguish
  PlayK(MatchK, Count(Orc(RE.FunRO))).play MatchK(Count(Orc(RE.FunRO))).guess.
wp.
while ((MatchK.cands = ws /\ y1 = perm RE.FunRO.f p0 x2 /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
        0 <= j /\ (!found => out = nth witness ws M)) `|`
       (PhiK RE.FunRO.f x2 y1 ws found out j p0)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hc8 hy hs11 hj hout.
  apply xr_ble; rewrite /PhiK; move: hc hout; case: (found{hr}) => /= [// | hnf hc hout].
  case: (p0{hr} \in ws /\ j{hr} <= index p0{hr} ws) => hc2 /=; 2: by smt().
  have hk : index p0{hr} ws = M by move: hc; rewrite hc8 hs; smt(index_mem).
  rewrite hout -hk nth_index 1:/# /=.
  by apply SK_ge0.
- seq 4 : ((MatchK.cands = ws /\ y1 = perm RE.FunRO.f p0 x2 /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
            0 <= j < M /\ !found /\ out = nth witness ws M /\ w = nth witness ws j /\
            z = bwdp RE.FunRO.f w y1 11 1) `|`
           (PhiK RE.FunRO.f x2 y1 ws found out j p0)%xr).
  + while ((MatchK.cands = ws /\ y1 = perm RE.FunRO.f p0 x2 /\ s11 = salt_of (RE.FunRO.f (PB (rd 11, y1.`1))) /\
            0 <= j < M /\ !found /\ out = nth witness ws M /\ w = nth witness ws j /\ 0 <= i <= 11 /\
            z = foldl (fun (u : state) k => unround (mask RE.FunRO.f w (rd k) u.`1) u) y1
                      (rev (iota_ (i + 1) (11 - i)))) `|`
           (PhiK RE.FunRO.f x2 y1 ws found out j p0)%xr).
    * move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hc8 hy hs11 hj0 hj1 hnf hout hw hi0 hi1 hz /=.
      apply xle_cxr_l; 2: by [].
      have hzx : z{hr} = bwdp RE.FunRO.f{hr} w{hr} y1{hr} 11 1 by rewrite hz (_ : i{hr} = 0) 1:/# /bwdp.
      by rewrite hzx /=; smt().
    * inline *; auto => &hr /=; apply xle_cxr_r => -[hc [#] hc8 hy hs11 hj0 hj1 hnf hout hw hi0 hi1 hz].
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
    auto => &hr /=; apply xle_cxr_r => -[[hc hnf] [#] hc8 hy hs11 hj hout].
    by apply xle_cxr_l => //; rewrite iota0 //=; smt().
  auto => &hr /=; apply xle_cxr_r => -[#] hc8 hy hs11 hj0 hj1 hnf hout hw hz.
  have hf : found{hr} = false by smt().
  have hwin : w{hr} \in ws by rewrite hw; apply mem_nth; smt().
  case: (accK RE.FunRO.f{hr} w{hr} x2{hr} y1{hr}) => ha.
  - have -> /= : (z{hr}.`1 = x2{hr}.`2) = true by move: ha; rewrite /accK -hz => ->.
    apply xle_cxr_l; 1: by rewrite hc8 hy hs11 /=; smt().
    apply xr_le; rewrite /PhiK hf /=.
    case: (p0{hr} \in ws /\ j{hr} <= index p0{hr} ws) => hc2 /=; 2: smt(b2r_ge0).
    case: (j{hr} = index p0{hr} ws) => hjk.
    + have -> // : w{hr} = p0{hr} by rewrite hw hjk nth_index; smt().
      by apply SK_ge0.
    rewrite /SK big_ltn 1:/# /= -hw ha /=.
    by have := SK_ge0 RE.FunRO.f{hr} x2{hr} y1{hr} ws p0{hr} (j{hr} + 1); rewrite /SK; smt(b2r_ge0).
  have -> /= : (z{hr}.`1 = x2{hr}.`2) = false by move: ha; rewrite /accK -hz => /negbTE.
  apply xle_cxr_l; 1: by rewrite hc8 hy hs11 /=; smt().
  apply xr_le; rewrite /PhiK hf /=.
  case: (p0{hr} \in ws /\ j{hr} < index p0{hr} ws) => hc2.
  - rewrite (_ : p0{hr} \in ws /\ j{hr} + 1 <= index p0{hr} ws) 1:/# (_ : p0{hr} \in ws /\ j{hr} <= index p0{hr} ws) 1:/# /=.
    by rewrite {2}/SK big_ltn 1:/# /= -hw ha /=.
  case: (p0{hr} \in ws /\ j{hr} = index p0{hr} ws) => hc3.
  - have hwp : w{hr} = p0{hr} by rewrite hw; smt(nth_index).
    by move: ha; rewrite hwp hy accK_real.
  smt().
inline *; wp.
while ((MatchK.cands = ws /\ p1 = p /\ 0 <= i0 <= 12 /\ x3 = fwdp RE.FunRO.f p DK.x 0 i0) `|`
       (PhiKb RE.FunRO.f DK.x ws p)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hc8 hp1 hi0 hi1 hx /=.
  have hx3 : x3{hr} = perm RE.FunRO.f{hr} p{hr} DK.x{hr} by rewrite hx (_ : i0{hr} = 12) 1:/# /fwdp /perm.
  apply xle_cxr_l; 1: by rewrite hc8 hx3 /=; smt().
  by apply xr_le; rewrite /PhiK /PhiKb hx3 /=; smt(index_ge0).
- auto => &hr /=; apply xle_cxr_r => -[hc [#] hc8 hp1 hi0 hi1 hx].
  apply xle_cxr_l => //; rewrite hc8 hp1 /=; split; 1: smt().
  by rewrite (fwdpS _ _ _ i0{hr}) // -hx /mask.
wp; skip => &hr /=; apply xle_cxr_r => hc8.
have hll : is_lossless (RE.MUniFinFun.dfun (fun (_ : point) => dans)).
- by apply RE.MUniFinFun.dfun_ll => z /=; apply dans_ll.
apply (xle_trans (Ep (RE.MUniFinFun.dfun (fun (_ : point) => dans))
         (fun f => Ep dP (fun pv => (PhiKb f x{hr} ws pv)%xr)))).
- apply le_Ep => f _ /=; apply le_Ep => pv _ /=.
  by apply xle_cxr_l; [rewrite hc8 /fwdp iota0 | done].
rewrite Ep_swap; apply le_Ep => pv _ /=.
case: (pv \in ws) => hin; last first.
- by rewrite /PhiKb /phiKs hin /= EpC hll smul1m.
rewrite /PhiKb hin /= /SK Ep_sum => [i f | ]; 1: smt(b2r_ge0).
rewrite (BXA.eq_bigr _ _ (fun i => (mu (RE.MUniFinFun.dfun (fun (_ : point) => dans))
            (fun f => accK f (nth witness ws i) x{hr} (perm f pv x{hr})))%xr)) => [i _ /= | ].
- by rewrite Ep_mu.
rewrite bigXR => [i _ | ]; 1: smt(ge0_mu).
apply xr_le; rewrite /phiKs hin /=.
apply (ler_trans (bigi predT (fun _ => deltaK) 0 (index pv ws))).
- apply Bigreal.ler_sum_seq => i /mem_range hi _ /=.
  have hne : pv <> nth witness ws i.
  + by apply/negP => h; have := before_index witness pv ws i _; [smt() | rewrite -h].
  exact (pairK &hr pv (nth witness ws i) x{hr} hne).
by rewrite sumri_const; [smt(index_ge0) | rewrite RField.intmulr; smt()].
qed.

(* The matching attack halts whenever its oracles do. *)
lemma matchK_guess_ll (O <: ABH {-MatchK}) :
  islossless O.a => islossless O.b => islossless O.h => islossless MatchK(O).guess.
proof.
move=> ha hb hh; proc; while (true) (size MatchK.cands - 1 - j).
- move=> z0; wp; while (true) i.
  + move=> z1; wp; call hh; call ha.
    by if; [auto => /# | call hb; auto => /#].
  by auto => /#.
by wp; call hb; auto => /#.
qed.

lemma matchK_ll : islossless Delta0(PlayK(MatchK)).main.
proof.
have [he _] := net_ll Ideal _ _ _; 1..3: by proc; inline *; auto; smt(dans_ll).
proc; inline PlayK(MatchK, Count(Ideal)).play Setup0K.run Count(Ideal).init.
wp; call (matchK_guess_ll (Count(Ideal)) _ _ _); 1..3: by proc; inline *; auto; smt(dans_ll).
by wp; call he; inline *; auto; smt(dP_ll).
qed.

lemma K5 &m (x : state) (ws : pw list) (m : int) :
  MatchK.cands{m} = ws => uniq ws => size ws = m + 1 =>
  bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * deltaK)) 0 (m + 1)
    <= Pr[Delta0(PlayK(MatchK)).main(x) @ &m : res].
proof.
move=> hc hu hs; case: (m < 0) => hm.
- by rewrite big_geq 1:/#; smt(mu_bounded).
have hdl := deltaK_ge0.
have hS := sum_cands ws (fun p => (index p ws)%r * deltaK) hu.
have hR : bigi predT (fun j => mu1 dP (nth witness ws j) *
            (1%r - (fun p => (index p ws)%r * deltaK) (nth witness ws j))) 0 (size ws) =
          bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * deltaK)) 0 (m + 1).
- by rewrite hs; apply eq_big_int => j hj /=; rewrite index_uniq // /#.
move: hS; rewrite hR => hS.
have hge : 0%r <= 1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * deltaK)) 0 (m + 1).
- rewrite -hS; apply Bigreal.sumr_ge0 => p _ /=.
  by case: (p \in ws) => _; smt(ge0_mu index_ge0 mulr_ge0).
have hE : Ep dP (fun p => (phiKs ws p)%xr) =
          (1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * deltaK)) 0 (m + 1))%xr.
- rewrite (eq_Ep _ _ (fun p => ((if p \in ws then (index p ws)%r * deltaK else 1%r))%xr)) => [p _ /= | ].
  + by rewrite /phiKs.
  by rewrite Ep_dP => [p | ]; [case: (p \in ws) => _ //; smt(index_ge0) | rewrite hS].
have e1 : Pr[Delta0(PlayK(MatchK)).main(x) @ &m : !res] = Pr[DKM(R.RO).main(x) @ &m : !res].
- by byequiv => //; proc; inline *; sim.
have e2 : Pr[DKM(R.RO).main(x) @ &m : !res] = Pr[DKM(RE.FunRO).main(x) @ &m : !res].
- by byequiv (_ : ={arg, glob DK} ==> ={res}) => //; proc; call (RO_FunRO DK); auto.
have h1 : Pr[DKM(RE.FunRO).main(x) @ &m : !res] <=
          1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - j%r * deltaK)) 0 (m + 1).
- byehoare (_ : (MatchK.cands = ws) `|` (Ep dP (fun p => (phiKs ws p)%xr)) ==> (!res)%xr) => //.
  + by apply (coreK_e ws m hu hs); smt().
  by rewrite hc /= hE.
have h2 : Pr[Delta0(PlayK(MatchK)).main(x) @ &m : true] = 1%r by byphoare => //; apply matchK_ll.
have h3 : Pr[Delta0(PlayK(MatchK)).main(x) @ &m : !res] =
          Pr[Delta0(PlayK(MatchK)).main(x) @ &m : true] - Pr[Delta0(PlayK(MatchK)).main(x) @ &m : res].
- by rewrite Pr[mu_not].
smt().
qed.

lemma K5_top &m (x : state) (m : int) :
  0 <= m => m + 1 <= PwT.card => MatchK.cands{m} = take (m + 1) ranked =>
  top (m + 1) * (1%r - m%r * deltaK) <= Pr[Delta0(PlayK(MatchK)).main(x) @ &m : res].
proof.
move=> hm hcard hc; have [hu [hs ht]] := ranked_top m deltaK hm hcard deltaK_ge0.
exact (ler_trans _ _ _ ht (K5 &m x (take (m + 1) ranked) m hc hu hs)).
qed.

lemma K5_budget (O <: ABH {-Count, -MatchK}) (m : int) : 0 <= m =>
  hoare [MatchK(Count(O)).guess :
    size MatchK.cands = m + 1 /\ Count.ca = 0 /\ Count.cb = 0 /\ Count.ch = 0 ==>
    Count.ca <= 11 * m /\ Count.cb <= 10 * m + 1 /\ Count.ch <= 11 * m].
proof.
move=> hm; proc.
while (0 <= j <= m /\ size MatchK.cands = m + 1 /\ Count.ca = 11 * j /\ Count.cb = 1 + 10 * j /\
       Count.ch = 11 * j).
- wp; while (0 <= i <= 11 /\ 0 <= j < m /\ size MatchK.cands = m + 1 /\ Count.ca = 11 * j + (11 - i) /\
             Count.cb = 1 + 10 * j + max 0 (10 - i) /\ Count.ch = 11 * j + (11 - i)).
  + inline *; wp; call (_ : true); wp; call (_ : true); wp.
    if; 1: by auto => /> /#.
    by wp; call (_ : true); auto => /> /#.
  by auto => /> /#.
by inline *; wp; call (_ : true); auto => /> /#.
qed.

(* ---- K5 and Theorem 4 bracket the best adversary ----------------------------------------------- *)
section Bracket5.
declare op ws0 : pw list.

(* The attack with its candidate list fixed: an adversary of Theorem 4. *)
local module M5 (O : ABH) = {
  proc guess(x : state, y : state) : pw = {
    var o; MatchK.cands <- ws0; o <@ MatchK(O).guess(x, y); return o;
  }
}.

lemma K5_upper &m (x : state) (m : int) : 0 <= m => size ws0 = m + 1 => MatchK.cands{m} = ws0 =>
  Pr[Delta0(PlayK(MatchK)).main(x) @ &m : res] <= top (m + 1) + epsK (11 * m) (10 * m + 1) (11 * m).
proof.
move=> hm hs hc.
have -> : Pr[Delta0(PlayK(MatchK)).main(x) @ &m : res] = Pr[Delta0(PlayK(M5)).main(x) @ &m : res].
- byequiv (_ : ={glob MatchK, x} /\ MatchK.cands{1} = ws0 ==> ={res}) => //.
  proc; inline PlayK(M5, Count(Ideal)).play M5(Count(Ideal)).guess PlayK(MatchK, Count(Ideal)).play; wp.
  call (_ : ={arg, glob MatchK, glob Count(Ideal)} ==> ={res}); 1: by sim.
  inline Count(Ideal).init; wp.
  by call (_ : ={arg} ==> ={res, R.RO.m}); [sim | auto].
have := theorem4 (11 * m) (10 * m + 1) (11 * m) M5 _ _ &m x _; 3: smt().
- by move=> O; proc; call (K5_budget O m hm); auto => /> /#.
- by move=> O ha hb hh; proc; call (matchK_guess_ll O ha hb hh); auto.
have -> : 1%r + (11 * m)%r / 11%r = (m + 1)%r by rewrite fromintM fromintD; smt().
by rewrite /ftop from_int_floor /=.
qed.
end section Bracket5.

(* With the m + 1 likeliest passwords the attack succeeds with a probability between the lower bound
   of K5 and the bound of Theorem 4 at k_A = 11m, where T(1 + k_A/11) = top(m + 1); so the success of
   the best adversary with the attack's budget lies between the two. *)
lemma K5_bracket &m (x : state) (m : int) :
  0 <= m => m + 1 <= PwT.card => MatchK.cands{m} = take (m + 1) ranked =>
  top (m + 1) * (1%r - m%r * deltaK) <= Pr[Delta0(PlayK(MatchK)).main(x) @ &m : res] /\
  Pr[Delta0(PlayK(MatchK)).main(x) @ &m : res] <= top (m + 1) + epsK (11 * m) (10 * m + 1) (11 * m).
proof.
move=> hm hcard hc; split; 1: exact (K5_top &m x m hm hcard hc).
apply (K5_upper (take (m + 1) ranked) &m x m hm _ hc).
by rewrite size_take 1:/# /ranked size_sort /PwT.card; smt().
qed.
