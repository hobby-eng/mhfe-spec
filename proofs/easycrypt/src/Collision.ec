(* The pair lemma: the inversions of one output under two different passwords give the same L_0 with
   chance at most 2^-128 + 12 2^-256 over A, B, H (delta_X of Proposition W7 and Corollaries G8 and
   G10). The second inversion meets the first only through the fresh mask of its last round, unless
   one of its twelve keys is the key of the first inversion's last H point. *)
require import AllCore List Distr DBool FMap StdBigop StdOrder Xreal.
require import Suite3 Chain.
require Mu_mem.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- The table ------------------------------------------------------------------------------ *)
(* An A point of w has the key of an H point of round 0. *)
op coll0 (w : pw) (m : (point, ans) fmap) =
  exists s R, PA (w, s) \in m /\ PH (key_of (oget m.[PA (w, s)]), rd 0, R) \in m.

(* At most n keys among the H points of round 0. *)
op few0 (m : (point, ans) fmap) (n : int) =
  exists (L : W256.word list), size L <= n /\ forall k R, PH (k, rd 0, R) \in m => k \in L.

lemma few0_set m n c v : (forall k R, c <> PH (k, rd 0, R)) => few0 m n => few0 m.[c <- v] n.
proof. by move=> hc [L [hs hL]]; exists L; split => // k R; rewrite mem_set => -[h | h]; [apply (hL k R) | smt()]. qed.

lemma few0_setH m n k0 R0 v : few0 m n => few0 m.[PH (k0, rd 0, R0) <- v] (n + 1).
proof. by move=> [L [hs hL]]; exists (k0 :: L); split; [smt() | move=> k R; rewrite mem_set; smt()]. qed.

lemma coll0_set w m c v : (forall s, c <> PA (w, s)) => (forall k R, c <> PH (k, rd 0, R)) =>
  coll0 w m.[c <- v] = coll0 w m.
proof.
move=> hA hH; rewrite /coll0; apply eq_iff; split => -[s R [h1 h2]]; exists s R.
- move: h1 h2; rewrite !mem_set get_set_neqE; 1: by smt().
  by move=> [h1 | h1] [h2 | h2]; smt().
by rewrite !mem_set get_set_neqE; [smt() | smt()].
qed.

lemma coll0_setA w m s r : PA (w, s) \notin m =>
  coll0 w m.[PA (w, s) <- r] => coll0 w m \/ exists R, PH (key_of r, rd 0, R) \in m.
proof.
move=> hn [s' R [h1 h2]]; move: h1 h2; rewrite !mem_set /=.
case: (s' = s) => [-> | hs] /=; 1: by rewrite get_set_sameE /= => h; right; exists R.
by rewrite get_set_neqE 1:/# => h1 h2; left; exists s' R.
qed.

(* A fresh key hits one of n keys with probability at most n e256. *)
lemma mu_few0 m n : few0 m n => mu dans (fun r => exists R, PH (key_of r, rd 0, R) \in m) <= n%r * e256.
proof.
move=> [L [hs hL]]; apply (StdOrder.RealOrder.ler_trans (mu dans (fun r => key_of r \in L))).
- by apply mu_le => r _ /= [R h]; apply (hL _ R).
rewrite (dans_key (fun k => k \in L)) /=.
apply (StdOrder.RealOrder.ler_trans ((size L)%r * inv (2%r ^ 256))).
- by apply Mu_mem.mu_mem_le_size => k _; rewrite dkey1.
by rewrite /e256; have := e256_gt0; rewrite /e256; smt().
qed.

(* A fresh mask meets a given half with probability e128. *)
lemma mu_mask0 (z : state) (t : W128.word) : mu dans (fun r => (unround (mask_of r) z).`1 = t) = e128.
proof.
rewrite /unround /= (mu_eq _ _ (fun r => pred1 (z.`2 +^ t) (mask_of r))) => [r | ].
- by rewrite /pred1; smt(xorwA xorwK xorwC xorw0).
by rewrite (dans_maskE (pred1 (z.`2 +^ t))) dhalf1 /e128.
qed.

(* ---- Expectations ------------------------------------------------------------------------- *)
lemma xr_le (a b : real) : a <= b => a%xr <= b%xr.
proof. by move=> h /=; rewrite /(%pos); smt(). qed.

lemma xr_ble (b : bool) (y : real) : b2r b <= y => (b)%xr <= y%xr.
proof. by case: b => h; apply rp_le; smt(). qed.

lemma Ep_cbs ['a] (d : 'a distr) (C c : real) (Q : 'a -> bool) : is_lossless d => 0%r <= C => 0%r <= c =>
  Ep d (fun x => (C + c * b2r (Q x))%xr) = (C + c * mu d Q)%xr.
proof.
move=> hd hC hc.
have hb : forall x, 0%r <= b2r (Q x) by move=> x; apply b2r_ge0.
rewrite (eq_Ep _ _ ((fun _ => C%xr) + (fun x => c%rp ** (b2r (Q x))%xr))) => [x _ /= | ].
- by have := hb x; smt(of_realD of_realM mulr_ge0).
rewrite EpD EpC hd smul1m EpsZ Ep_mu /=.
by have := ge0_mu d Q; smt(of_realD of_realM mulr_ge0).
qed.

(* A constant plus an indicator. *)
lemma Ep_cb ['a] (d : 'a distr) (C : real) (Q : 'a -> bool) : is_lossless d => 0%r <= C =>
  Ep d (fun x => (C + b2r (Q x))%xr) = (C + mu d Q)%xr.
proof.
move=> hd hC.
rewrite (eq_Ep _ _ ((fun _ => C%xr) + (fun x => (b2r (Q x))%xr))) => [x _ /= | ].
- by rewrite of_realD //; apply b2r_ge0.
rewrite EpD EpC hd smul1m Ep_mu.
have hm := ge0_mu d Q.
by rewrite /= -(of_realD C (mu d Q) hC hm).
qed.

(* One oracle step that keeps a guarded constant. *)
lemma Ep_guard (c : point) (m : (point, ans) fmap) (G1 : ans -> bool) (G2 b : bool) (C : xreal) :
  (b => (c \notin m => forall r, G1 r) /\ (c \in m => G2)) =>
  Ep dans (fun r => if c \notin m then G1 r `|` C else G2 `|` C) <= b `|` C.
proof.
move=> h; apply xle_cxr_r => hb; have [h1 h2] := h hb.
case: (c \in m) => hc /=; 1: by rewrite h2 // EpC dans_ll smul1m.
by rewrite (eq_Ep _ _ (fun _ => C)) => [r _ /= | ]; [rewrite h1 | rewrite EpC dans_ll smul1m].
qed.

(* ---- The two inversions in the lazy oracle --------------------------------------------------- *)
module TwoInv (G : R.RO) = {
  var p, w : pw
  var y, e : state
  proc distinguish() : bool = {
    var z;
    e <@ Net(Orc(G)).dec(p, y);
    z <@ Net(Orc(G)).dec(w, y);
    return z.`1 = e.`1;
  }
}.

(* The risk of the second inversion before round i (after it when i < 0). *)
op phiX (w : pw) (m : (point, ans) fmap) (i : int) (z e : state) : real =
  if i < 0 then b2r (z.`1 = e.`1) else b2r (coll0 w m) + e128 + (i + 1)%r * e256.

lemma two_inv_e (pv wv : pw) : pv <> wv =>
  ehoare [R.MainD(TwoInv, R.RO).distinguish :
    (TwoInv.p = pv /\ TwoInv.w = wv) `|` (e128 + 12%r * e256)%xr ==> (res)%xr].
proof.
move=> hpw; proc; inline *; wp.
while ((p0 = wv /\ -1 <= i0 <= 11 /\ (0 <= i0 => few0 R.RO.m 1)) `|` (phiX wv R.RO.m i0 y0 TwoInv.e)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hp hi0 hi1 hf.
  by rewrite /phiX (_ : i0{hr} < 0) 1:/#.
- seq 7 : ((p0 = wv /\ 0 <= i0 <= 11 /\ few0 R.RO.m 1) `|` (phiX wv R.RO.m i0 y0 TwoInv.e)%xr).
  + auto => &hr /=; apply xle_cxr_r => -[hc [#] hp hi0 hi1 hf].
    apply (xle_trans (Ep dans (fun _ => (phiX wv R.RO.m{hr} i0{hr} y0{hr} TwoInv.e{hr})%xr))).
    * apply le_Ep => r _ /=; case: (PB (rd i0{hr}, y0{hr}.`1) \in R.RO.m{hr}) => hin /=.
      - by apply xle_cxr_l => //; rewrite hp; smt().
      apply xle_cxr_l; 1: by rewrite hp /=; split; [smt() | apply few0_set; [by move=> k R | exact (hf hc)]].
      by rewrite /phiX coll0_set.
    by rewrite EpC dans_ll smul1m.
  seq 7 : ((p0 = wv /\ 0 <= i0 <= 11 /\ few0 R.RO.m 1 /\ PA (wv, s2) \in R.RO.m /\
            k0 = key_of (oget R.RO.m.[PA (wv, s2)])) `|` (b2r (coll0 wv R.RO.m) + e128 + i0%r * e256)%xr).
  + auto => &hr /=; apply xle_cxr_r => -[#] hp hi0 hi1 hf.
    rewrite /phiX (_ : !(i0{hr} < 0)) 1:/# /= hp.
    case: (PA (wv, s0{hr}) \in R.RO.m{hr}) => hin /=.
    * rewrite EpC dans_ll smul1m; apply xle_cxr_l => //.
      by apply xr_le; smt(e256_gt0).
    apply (xle_trans (Ep dans (fun r => (b2r (coll0 wv R.RO.m{hr}) + e128 + i0{hr}%r * e256 +
             1%r * b2r (exists R, PH (key_of r, rd 0, R) \in R.RO.m{hr}))%xr))).
    * apply le_Ep => r _ /=; apply xle_cxr_l.
      - by rewrite mem_set /=; split; [smt() | apply few0_set; [by move=> k R | done]].
      by apply xr_le; have := coll0_setA wv R.RO.m{hr} s0{hr} r hin; smt().
    rewrite Ep_cbs ?dans_ll //; 1: smt(e128_gt0 e256_gt0 b2r_ge0).
    by apply xr_le; have := mu_few0 _ _ hf; smt().
  auto => &hr /=; apply xle_cxr_r => -[#] hp hi0 hi1 hf hA hk.
  case: (i0{hr} = 0) => hz.
  + rewrite hz /= /phiX /=; case: (coll0 wv R.RO.m{hr}) => hc.
    * apply (xle_trans (Ep dans (fun _ => 1%xr))); 2: by rewrite EpC dans_ll smul1m; apply xr_le; smt(e128_gt0).
      apply le_Ep => r _ /=; case: (PH (k0{hr}, rd 0, y0{hr}.`1) \in R.RO.m{hr}) => hin /=.
      - by apply xle_cxr_l; [rewrite hp | apply xr_le; smt()].
      by apply xle_cxr_l; [rewrite hp | apply xr_le; smt()].
    have hnin : PH (k0{hr}, rd 0, y0{hr}.`1) \notin R.RO.m{hr}.
    * by apply/negP => h; apply hc; exists s2{hr} y0{hr}.`1; rewrite hA -hk.
    rewrite hnin /=; apply (xle_trans (Ep dans (fun r => ((unround (mask_of r) y0{hr}).`1 = TwoInv.e{hr}.`1)%xr))).
    * by apply le_Ep => r _ /=; apply xle_cxr_l; [rewrite hp | rewrite get_set_sameE].
    by rewrite Ep_mu mu_mask0; apply xr_le.
  rewrite /phiX (_ : !(i0{hr} - 1 < 0)) 1:/# /=.
  apply (xle_trans (Ep dans (fun _ => (b2r (coll0 wv R.RO.m{hr}) + e128 + i0{hr}%r * e256)%xr))).
  + have hne : forall k R, PH (k0{hr}, rd i0{hr}, y0{hr}.`1) <> PH (k, rd 0, R).
    * by move=> k R /=; have := rd_inj i0{hr} 0; smt().
    apply le_Ep => r _ /=; case: (PH (k0{hr}, rd i0{hr}, y0{hr}.`1) \in R.RO.m{hr}) => hin /=.
    * by apply xle_cxr_l; [rewrite hp; smt() | apply xr_le; smt()].
    have hc : coll0 wv R.RO.m{hr}.[PH (k0{hr}, rd i0{hr}, y0{hr}.`1) <- r] = coll0 wv R.RO.m{hr}.
    * by apply coll0_set => // s.
    apply xle_cxr_l; 1: by rewrite hp /=; split; [smt() | move=> _; apply few0_set].
    by rewrite hc; apply xr_le; smt().
  by rewrite EpC dans_ll smul1m.
wp; while ((p = pv /\ TwoInv.w = wv /\ -1 <= i <= 11 /\ few0 R.RO.m (if 0 <= i then 0 else 1) /\
            forall s, PA (wv, s) \notin R.RO.m) `|` (e128 + 12%r * e256)%xr).
- move=> &hr; apply xle_cxr_r => hc; apply xle_cxr_r => -[#] hp hw hi0 hi1 hf hn.
  apply xle_cxr_l; 1: by rewrite hw /=; smt().
  have hc0 : !coll0 wv R.RO.m{hr} by apply/negP; rewrite /coll0 => -[s R [h _]]; have := hn s; rewrite h.
  by rewrite /phiX /= (negbTE _ hc0).
- seq 7 : ((p = pv /\ TwoInv.w = wv /\ 0 <= i <= 11 /\ few0 R.RO.m 0 /\
            forall s, PA (wv, s) \notin R.RO.m) `|` (e128 + 12%r * e256)%xr).
  + auto => &hr /=; apply Ep_guard => -[hc [#] hp hw hi0 hi1 hf hn]; split => [hnin r | hin] /=.
    * have hf0 : few0 R.RO.m{hr} 0 by move: hf; rewrite hc.
      by rewrite hp hw /=; split; [smt() | split; [apply few0_set | move=> s; rewrite mem_set hn]].
    by rewrite hp hw /=; smt().
  seq 7 : ((p = pv /\ TwoInv.w = wv /\ 0 <= i <= 11 /\ few0 R.RO.m 0 /\
            forall s, PA (wv, s) \notin R.RO.m) `|` (e128 + 12%r * e256)%xr).
  + auto => &hr /=; apply Ep_guard => -[#] hp hw hi0 hi1 hf hn; split => [hnin r | hin].
    * by rewrite hp hw /=; split; [smt() | split; [apply few0_set | move=> s; rewrite mem_set hn /= /#]].
    by rewrite hp hw /=; smt().
  auto => &hr /=; apply Ep_guard => -[#] hp hw hi0 hi1 hf hn; split => [hnin r | hin].
  + rewrite hp hw /=; split; 1: smt(); split; 2: by move=> s; rewrite mem_set hn.
    case: (i{hr} = 0) => hz.
    * by rewrite hz /=; have := few0_setH _ 0 k{hr} y{hr}.`1 r hf.
    by rewrite (_ : 0 <= i{hr} - 1) 1:/# /=; apply few0_set => // k R /=; have := rd_inj i{hr} 0; smt().
  rewrite hp hw /=; split; 1: smt(); split => //.
  by case: (0 <= i{hr} - 1) => _ //; move: hf => [L [hs hL]]; exists L; smt().
auto => &hr; apply xle_cxr_r => -[hp hw]; apply xle_cxr_l => //.
by rewrite hp hw /=; split; [exists []; smt(mem_empty) | move=> s; rewrite mem_empty].
qed.

(* ---- The pair lemma over the whole function --------------------------------------------------- *)
module TwoInvM (G : R.RO) = {
  proc main(p w : pw, y : state) : bool = {
    var b;
    TwoInv.p <- p; TwoInv.w <- w; TwoInv.y <- y;
    b <@ R.MainD(TwoInv, G).distinguish();
    return b;
  }
}.

module SampF = {
  proc main(p w : pw, y : state) : bool = {
    var f;
    f <$ RE.MUniFinFun.dfun (fun _ => dans);
    return (invperm f w y).`1 = (invperm f p y).`1;
  }
}.

lemma eager_pair &m (p w : pw) (y : state) :
  Pr[TwoInvM(RE.FunRO).main(p, w, y) @ &m : res] =
  mu (RE.MUniFinFun.dfun (fun _ => dans)) (fun f => (invperm f w y).`1 = (invperm f p y).`1).
proof.
have -> : Pr[TwoInvM(RE.FunRO).main(p, w, y) @ &m : res] = Pr[SampF.main(p, w, y) @ &m : res].
- byequiv (_ : ={arg} /\ arg{1} = (p, w, y) ==> ={res}) => //.
  proc; inline R.MainD(TwoInv, RE.FunRO).distinguish TwoInv(RE.FunRO).distinguish RE.FunRO.init.
  by wp; call{1} (dec_fun_ph w y); call{1} (dec_fun_ph p y); wp; rnd; auto => />.
by byphoare (_ : arg = (p, w, y) ==> _) => //; proc; rnd; skip => />.
qed.

(* The pair lemma. *)
lemma pair_coll &m (p w : pw) (y : state) : p <> w =>
  mu (RE.MUniFinFun.dfun (fun _ => dans)) (fun f => (invperm f w y).`1 = (invperm f p y).`1)
  <= e128 + 12%r * e256.
proof.
move=> hpw; rewrite -(eager_pair &m).
have <- : Pr[TwoInvM(R.RO).main(p, w, y) @ &m : res] = Pr[TwoInvM(RE.FunRO).main(p, w, y) @ &m : res].
- by byequiv (_ : ={arg, TwoInv.e} ==> ={res}) => //; proc; call (RO_FunRO TwoInv); auto.
byehoare (_ : (arg = (p, w, y)) `|` (e128 + 12%r * e256)%xr ==> (res)%xr) => //.
- proc; call (two_inv_e p w hpw); auto => &hr; apply xle_cxr_r => h.
  by apply xle_cxr_l => //; move: h => /= [-> [-> _]].
smt(e128_gt0 e256_gt0).
qed.

(* ---- Union over the other passwords ------------------------------------------------------------ *)
op deltaX : real = inv (2%r ^ 128) + 12%r / 2%r ^ 256.

lemma mu_has_le ['a 'b] (d : 'a distr) (P : 'b -> 'a -> bool) (l : 'b list) :
  mu d (fun x => has (fun w => P w x) l) <= big predT (fun w => mu d (P w)) l.
proof.
elim: l => [|w l ih] /=; 1: by rewrite big_nil mu0_false.
rewrite big_cons /predT /=; apply (ler_trans _ _ _ (mu_or_le d (P w) (fun x => has (fun w => P w x) l))).
by apply ler_add2l.
qed.

(* The inversion under some other password of ws meets the inversion under p. *)
lemma mu_coll &m (ws : pw list) (y : state) (p : pw) : uniq ws => p \in ws =>
  mu (RE.MUniFinFun.dfun (fun _ => dans)) (fun f => has (fun w => w <> p /\ invperm f w y = invperm f p y) ws)
  <= (size ws - 1)%r * deltaX.
proof.
move=> hu hp.
apply (ler_trans _ _ _ (mu_has_le _ (fun w f => w <> p /\ invperm f w y = invperm f p y) ws)).
apply (ler_trans (big predT (fun w => if w <> p then deltaX else 0%r) ws)).
- apply Bigreal.ler_sum => w _ /=; case: (w = p) => hw /=.
  + by rewrite (mu_eq _ _ pred0) 1:/# mu0.
  apply (ler_trans _ _ _ (mu_le _ _ (fun f => (invperm f w y).`1 = (invperm f p y).`1) _)); 1: smt().
  by have := pair_coll &m p w y _; [smt() | rewrite /deltaX /e128 /e256].
rewrite -big_mkcond sumr_const RField.intmulr.
have h1 := count_predC (fun w => w <> p) ws.
have h2 : count (predC (fun w => w <> p)) ws = 1.
- by rewrite (eq_count _ (pred1 p)) => [w | ]; [rewrite /predC /pred1 /# | rewrite count_uniq_mem // hp].
smt().
qed.

(* Fubini for expectations. *)
lemma Ep_swap ['a 'b] (d1 : 'a distr) (d2 : 'b distr) (F : 'a -> 'b -> xreal) :
  Ep d1 (fun x => Ep d2 (fun y => F x y)) = Ep d2 (fun y => Ep d1 (fun x => F x y)).
proof.
have h1 : Ep d1 (fun x => Ep d2 (fun y => F x y)) = Ep (d1 `*` d2) (fun (z : 'a * 'b) => F z.`1 z.`2).
- rewrite dprod_dlet Ep_dlet; apply eq_Ep => x _ /=.
  by rewrite Ep_dlet; apply eq_Ep => y _ /=; rewrite Ep_dunit.
have h2 : Ep d2 (fun y => Ep d1 (fun x => F x y)) = Ep (d2 `*` d1) (fun (z : 'b * 'a) => F z.`2 z.`1).
- rewrite dprod_dlet Ep_dlet; apply eq_Ep => y _ /=.
  by rewrite Ep_dlet; apply eq_Ep => x _ /=; rewrite Ep_dunit.
by rewrite h1 h2 dprodC Ep_dmap.
qed.

(* ---- Sums over the candidates ------------------------------------------------------------------ *)
(* The expectation of a nonnegative function of P as a sum over the passwords. *)
lemma Ep_dP (f : pw -> real) : (forall p, 0%r <= f p) =>
  Ep dP (fun p => (f p)%xr) = (big predT (fun p => mu1 dP p * f p) PwT.enum)%xr.
proof.
move=> hf; rewrite (Ep_fin PwT.enum) ?PwT.enum_uniq => [p _ | ]; 1: by apply PwT.enumP.
rewrite (BXA.eq_bigr _ _ (fun p => (mu1 dP p * f p)%xr)) => [p _ /= | ].
- by rewrite -(of_realM _ _ (ge0_mu dP (pred1 p)) (hf p)).
by rewrite bigXR // => p _; have := hf p; have := ge0_mu dP (pred1 p); smt().
qed.

(* The weight of the candidates, and their weighted indices. *)
lemma sum_cands (ws : pw list) (g : pw -> real) : uniq ws =>
  big predT (fun p => mu1 dP p * (if p \in ws then g p else 1%r)) PwT.enum =
  1%r - bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - g (nth witness ws j))) 0 (size ws).
proof.
move=> hu.
have hX : big predT (fun p => if p \in ws then mu1 dP p * (1%r - g p) else 0%r) PwT.enum =
          bigi predT (fun j => mu1 dP (nth witness ws j) * (1%r - g (nth witness ws j))) 0 (size ws).
- rewrite -(big_mkcond (mem ws)) -big_filter.
  rewrite (eq_big_perm _ _ (filter (mem ws) PwT.enum) ws).
  + apply uniq_perm_eq; [apply filter_uniq; apply PwT.enum_uniq | exact hu | by move=> p; rewrite mem_filter PwT.enumP andbT].
  by rewrite (big_nth witness) /(\o).
rewrite (eq_bigr _ _ (fun p => mu1 dP p + (- (if p \in ws then mu1 dP p * (1%r - g p) else 0%r)))) => [p _ /= | ].
- by case: (p \in ws) => _; ring.
by rewrite big_split sum_dP -hX -sumrN.
qed.

(* The top-ranked candidates: each term is at least its share of top(m + 1). *)
lemma ranked_top (m : int) (dl : real) : 0 <= m => m + 1 <= PwT.card => 0%r <= dl =>
  uniq (take (m + 1) ranked) /\ size (take (m + 1) ranked) = m + 1 /\
  top (m + 1) * (1%r - m%r * dl) <=
  bigi predT (fun j => mu1 dP (nth witness (take (m + 1) ranked) j) * (1%r - j%r * dl)) 0 (m + 1).
proof.
move=> hm hcard hdl; have hp : perm_eq ranked PwT.enum by rewrite /ranked; apply perm_sort.
have hsz : size ranked = PwT.card by rewrite (perm_eq_size _ _ hp) /PwT.card.
split; 1: by apply uniq_take; rewrite (perm_eq_uniq _ _ hp) PwT.enum_uniq.
split; 1: by rewrite size_take /#.
rewrite top_shift mulr_suml; apply StdBigop.Bigreal.ler_sum_seq => j /mem_range hj _ /=.
rewrite nth_take 1,2:/# /pr (_ : 1 <= j + 1 <= size ranked) 1:/# /=.
have := ge0_mu dP (pred1 (nth witness ranked j)); have : j%r <= m%r by smt().
smt().
qed.

(* An expectation of a sum of nonnegative terms. *)
lemma Ep_sum ['a] (d : 'a distr) (F : int -> 'a -> real) (l : int list) : (forall i v, 0%r <= F i v) =>
  Ep d (fun v => (big predT (fun i => F i v) l)%xr) = BXA.big predT (fun i => Ep d (fun v => (F i v)%xr)) l.
proof.
move=> hF; elim: l => [|i l ih] /=.
- by rewrite BXA.big_nil (eq_Ep _ _ (fun _ => 0%xr)) => [v _ /= | ]; [rewrite big_nil | rewrite EpC].
rewrite BXA.big_cons /predT /= -ih -EpD; apply eq_Ep => v _ /=.
by rewrite big_cons /predT /= of_realD //; [apply hF | apply Bigreal.sumr_ge0 => *; apply hF].
qed.

(* Two independent samples as one sample of the product. *)
lemma Ep_dprod ['a 'b] (d1 : 'a distr) (d2 : 'b distr) (F : 'a -> 'b -> xreal) :
  Ep d1 (fun x => Ep d2 (fun y => F x y)) = Ep (d1 `*` d2) (fun (z : 'a * 'b) => F z.`1 z.`2).
proof.
rewrite dprod_dlet Ep_dlet; apply eq_Ep => x _ /=.
by rewrite Ep_dlet; apply eq_Ep => y _ /=; rewrite Ep_dunit.
qed.
