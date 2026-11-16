(* The ideal model shared by all results (DESIGN-NOTES A.1): the twelve-round Feistel network keyed
   by a password, the functions A, B, H as one lazily sampled random oracle on their query points,
   and the ranked password masses. The half width is a parameter: suite 3 has 128-bit halves and
   suite 4 ENT/2-bit halves. *)
require import AllCore List Distr DBool DProd DList FMap StdBigop StdOrder.
require (*--*) FinType PROM Subtype DList.
import StdBigop.Bigreal StdBigop.Bigreal.BRA RealOrder.

abstract theory Feistel.

(* ---- Halves with xor; salts, keys and normalized passwords, all finite ---------------------- *)
type half, salt, key, pw.

op (+^) : half -> half -> half.
op zero : half.
axiom xorA : associative (+^).
axiom xorC : commutative (+^).
axiom xor0 (x : half) : x +^ zero = x.
axiom xorK (x : half) : x +^ x = zero.

clone FinType.FinType as HalfT with type t <- half.
clone FinType.FinType as SaltT with type t <- salt.
clone FinType.FinType as KeyT with type t <- key.
clone FinType.FinType as PwT with type t <- pw.

op dhalf : half distr.
axiom dhalf_ll : is_lossless dhalf.
axiom dhalf_funi : is_funiform dhalf.
op dsalt : salt distr.
axiom dsalt_ll : is_lossless dsalt.
axiom dsalt_funi : is_funiform dsalt.
op dkey : key distr.
axiom dkey_ll : is_lossless dkey.
axiom dkey_funi : is_funiform dkey.

(* The password distribution over normalized encodings. *)
op dP : pw distr.
axiom dP_ll : is_lossless dP.

type state = half * half.
op dstate : state distr = dhalf `*` dhalf.

(* ---- Round indices 0 .. 11 ------------------------------------------------------------------ *)
subtype ridx as Ridx = { i : int | 0 <= i < 12 }.
realize inhabited by exists 0.

op rd (i : int) : ridx = Ridx.insubd i.

lemma rdK (i : int) : 0 <= i < 12 => Ridx.val (rd i) = i.
proof. by move=> hi; rewrite /rd Ridx.insubdK. qed.

clone FinType.FinType as RidxT with type t <- ridx, op enum = map rd (iota_ 0 12)
proof enum_spec.
realize enum_spec.
proof.
move=> x; rewrite count_uniq_mem.
- rewrite map_inj_in_uniq ?iota_uniq // => i j /mem_iota hi /mem_iota hj.
  by move/(congr1 Ridx.val); smt(rdK).
rewrite b2i_eq1; apply/mapP; exists (Ridx.val x).
by rewrite mem_iota /rd Ridx.valKd /=; smt(Ridx.valP).
qed.

(* ---- Query points and the random oracle ----------------------------------------------------- *)
(* A query point names its function: A at (password, salt), B at (round, half), H at (key, round,
   half). One oracle answers all points; A, B and H read their own component of its answer, so they
   are independent uniform functions. *)
type point = [
  | PA of (pw * salt)
  | PB of (ridx * half)
  | PH of (key * ridx * half) ].

op isA (c : point) = with c = PA _ => true with c = PB _ => false with c = PH _ => false.
op isB (c : point) = with c = PA _ => false with c = PB _ => true with c = PH _ => false.

op point_enum : point list =
  map PA (allpairs (fun p s => (p, s)) PwT.enum SaltT.enum) ++
  (map PB (allpairs (fun i r => (i, r)) RidxT.enum HalfT.enum) ++
   map PH (allpairs (fun k (ir : ridx * half) => (k, ir.`1, ir.`2)) KeyT.enum
             (allpairs (fun i r => (i, r)) RidxT.enum HalfT.enum))).

lemma point_enum_uniq : uniq point_enum.
proof.
rewrite /point_enum !cat_uniq !map_inj_in_uniq; 1..3: smt().
do! split.
- by apply allpairs_uniq; [apply PwT.enum_uniq | apply SaltT.enum_uniq | smt()].
- rewrite has_cat negb_or !has_map; split; apply/hasPn => x _ /=;
    by apply/negP => /mapP [y] [_].
- by apply allpairs_uniq; [apply RidxT.enum_uniq | apply HalfT.enum_uniq | smt()].
- rewrite has_map; apply/hasPn => x _ /=.
  by apply/negP => /mapP [y] [_].
apply allpairs_uniq; [apply KeyT.enum_uniq | | smt()].
by apply allpairs_uniq; [apply RidxT.enum_uniq | apply HalfT.enum_uniq | smt()].
qed.

lemma point_enumP (c : point) : c \in point_enum.
proof.
rewrite /point_enum !mem_cat.
case: c => [[p s]|[i r]|[k i r]] /=.
- left; apply/mapP; exists (p, s) => /=; rewrite allpairsP.
  by exists (p, s); rewrite PwT.enumP SaltT.enumP.
- right; left; apply/mapP; exists (i, r) => /=; rewrite allpairsP.
  by exists (i, r); rewrite RidxT.enumP HalfT.enumP.
right; right; apply/mapP; exists (k, i, r) => /=; rewrite allpairsP.
exists (k, (i, r)); rewrite KeyT.enumP /= allpairsP.
by exists (i, r); rewrite RidxT.enumP HalfT.enumP.
qed.

clone FinType.FinType as PointT with type t = point, op enum = point_enum
proof enum_spec.
realize enum_spec.
proof. by move=> c; rewrite count_uniq_mem 1:point_enum_uniq point_enumP. qed.

type ans = key * (salt * half).
op dans : ans distr = dkey `*` (dsalt `*` dhalf).
op key_of (r : ans) : key = r.`1.
op salt_of (r : ans) : salt = r.`2.`1.
op mask_of (r : ans) : half = r.`2.`2.

clone import PROM.FullRO as R with
  type in_t <- point, type out_t <- ans, op dout <- (fun _ => dans),
  type d_in_t <- unit, type d_out_t <- bool.
clone R.FinEager as RE with theory FinFrom <- PointT.

(* ---- The network as a pure function of the oracle ------------------------------------------ *)
op round (m : half) (w : state) : state = (w.`2, w.`1 +^ m).
op unround (m : half) (w : state) : state = (w.`2 +^ m, w.`1).

(* The mask of round i for password p at right half r: H(A(p, B(i, r)), i, r). *)
op mask (f : point -> ans) (p : pw) (i : ridx) (r : half) : half =
  let s = salt_of (f (PB (i, r))) in
  let k = key_of (f (PA (p, s))) in
  mask_of (f (PH (k, i, r))).

op perm f p (x : state) : state =
  foldl (fun (w : state) i => round (mask f p (rd i) w.`2) w) x (iota_ 0 12).

op invperm f p (y : state) : state =
  foldl (fun (w : state) i => unround (mask f p (rd i) w.`1) w) y (rev (iota_ 0 12)).

(* Lemma 1 (consistency): for any functions, Inv_p and Perm_p are inverse permutations. *)
lemma unround_round f p i (w : state) :
  unround (mask f p i (round (mask f p i w.`2) w).`1) (round (mask f p i w.`2) w) = w.
proof. by case: w => l r; rewrite /round /unround /= -xorA xorK xor0. qed.

lemma round_unround f p i (w : state) :
  round (mask f p i (unround (mask f p i w.`1) w).`2) (unround (mask f p i w.`1) w) = w.
proof. by case: w => l r; rewrite /round /unround /= -xorA xorK xor0. qed.

lemma invpermK f p (x : state) : invperm f p (perm f p x) = x.
proof.
rewrite /invperm /perm; elim: (iota_ 0 12) x => [|k ks ih] x //=.
by rewrite rev_cons foldl_rcons ih /= unround_round.
qed.

lemma permK f p (y : state) : perm f p (invperm f p y) = y.
proof.
rewrite /invperm /perm; elim/last_ind: (iota_ 0 12) y => [|ks k ih] y //=.
by rewrite rev_rcons /= foldl_rcons ih /= round_unround.
qed.

(* Lemma 2 (uniformity): F(Z) is uniform and independent of a permutation F chosen independently of
   a uniform Z. *)
lemma dstate_ll : is_lossless dstate.
proof. by apply/dprod_ll; split; apply dhalf_ll. qed.

lemma dstate_funi : is_funiform dstate.
proof. exact (dprod_funi _ _ dhalf_funi dhalf_funi). qed.

lemma dstate_full (x : state) : x \in dstate.
proof. by case: x => a b; rewrite /dstate supp_dprod; smt(funi_ll_full dhalf_funi dhalf_ll). qed.

lemma lemma2 (dF : (state -> state) distr) :
  (forall F, F \in dF => bijective F) =>
  dlet dF (fun F => dmap dstate (fun z => (F, F z))) = dF `*` dstate.
proof.
move=> hbij; rewrite dprod_dlet; apply in_eq_dlet => F hF /=.
have ->: dmap dstate (fun z => (F, F z)) = dmap (dmap dstate F) (fun z => (F, z)).
+ by rewrite dmap_comp.
have ->: dmap dstate F = dstate.
+ apply eq_funi_ll.
  - exact (dmap_funi _ _ (hbij F hF) dstate_funi).
  - exact (dmap_ll _ _ dstate_ll).
  - exact dstate_funi.
  - exact dstate_ll.
by rewrite /dmap /(\o).
qed.

(* ---- The oracles of the adversary ------------------------------------------------------------ *)
module type ABH = {
  proc a(p : pw, s : salt) : key
  proc b(i : ridx, r : half) : salt
  proc h(k : key, i : ridx, r : half) : half
}.

module Orc (G : RO) : ABH = {
  proc a(p : pw, s : salt) = { var x; x <@ G.get(PA (p, s)); return key_of x; }
  proc b(i : ridx, r : half) = { var x; x <@ G.get(PB (i, r)); return salt_of x; }
  proc h(k : key, i : ridx, r : half) = { var x; x <@ G.get(PH (k, i, r)); return mask_of x; }
}.

module Ideal = Orc(RO).

(* Counts every call, repeated points included. *)
module Count (O : ABH) = {
  var ca, cb, ch : int
  proc init() = { ca <- 0; cb <- 0; ch <- 0; }
  proc a(p : pw, s : salt) = { var k; ca <- ca + 1; k <@ O.a(p, s); return k; }
  proc b(i : ridx, r : half) = { var s; cb <- cb + 1; s <@ O.b(i, r); return s; }
  proc h(k : key, i : ridx, r : half) = { var m; ch <- ch + 1; m <@ O.h(k, i, r); return m; }
}.

(* Encryption and decryption of one state through the oracles: twelve B, A, H calls each. *)
module Net (O : ABH) = {
  proc enc(p : pw, x : state) : state = {
    var i, s, k, m;
    i <- 0;
    while (i < 12) {
      s <@ O.b(rd i, x.`2);
      k <@ O.a(p, s);
      m <@ O.h(k, rd i, x.`2);
      x <- round m x;
      i <- i + 1;
    }
    return x;
  }
  proc dec(p : pw, y : state) : state = {
    var i, s, k, m;
    i <- 11;
    while (0 <= i) {
      s <@ O.b(rd i, y.`1);
      k <@ O.a(p, s);
      m <@ O.h(k, rd i, y.`1);
      y <- unround m y;
      i <- i - 1;
    }
    return y;
  }
}.

lemma net_ll (O <: ABH) : islossless O.a => islossless O.b => islossless O.h =>
  islossless Net(O).enc /\ islossless Net(O).dec.
proof.
move=> ha hb hh; split; proc.
- by while true (12 - i); [move=> z; wp; call hh; call ha; call hb | ]; auto => /#.
by while true (i + 1); [move=> z; wp; call hh; call ha; call hb | ]; auto => /#.
qed.

(* ---- The oracle as a whole function --------------------------------------------------------- *)
(* PROM.FinEager: on the finite set of query points, the lazy oracle and a function sampled in advance
   give the same result to every program that uses the oracle only through its procedures. *)
lemma dans_ll : is_lossless dans.
proof. by rewrite /dans; apply/dprod_ll; rewrite dkey_ll /=; apply/dprod_ll; rewrite dsalt_ll dhalf_ll. qed.

section FunRO.
declare module D <: RE.FinRO_Distinguisher {-RO, -FRO, -RE.FunRO}.

equiv RO_FunRO : MainD(D, RO).distinguish ~ MainD(D, RE.FunRO).distinguish :
  ={glob D, arg} ==> ={res, glob D}.
proof.
transitivity MainD(D, RE.FinRO).distinguish
  (={glob D, arg} ==> ={res, glob D}) (={glob D, arg} ==> ={res, glob D}) => //.
- by move=> &1 &2 h; exists (glob D){1} arg{1}.
- by apply (RE.RO_FinRO_D _ D) => _; exact dans_ll.
by apply (RE.FinRO_FunRO_D _ D) => _; exact dans_ll.
qed.
end section FunRO.

(* Through the whole function, the network computes Perm and Inv. *)
lemma enc_fun (p0 : pw) (x0 : state) :
  hoare [Net(Orc(RE.FunRO)).enc : p = p0 /\ x = x0 ==> res = perm RE.FunRO.f p0 x0].
proof.
proc; inline *.
while (0 <= i <= 12 /\ p = p0 /\
       x = foldl (fun (w : state) j => round (mask RE.FunRO.f p0 (rd j) w.`2) w) x0 (iota_ 0 i)).
- auto => /> &hr ge0i _ lti; split; 1: smt().
  by rewrite iotaSr // -cats1 foldl_cat /= /mask.
by auto => />; rewrite /perm iota0 //=; smt().
qed.

lemma dec_fun (p0 : pw) (y0 : state) :
  hoare [Net(Orc(RE.FunRO)).dec : p = p0 /\ y = y0 ==> res = invperm RE.FunRO.f p0 y0].
proof.
proc; inline *.
while (-1 <= i <= 11 /\ p = p0 /\
       y = foldl (fun (w : state) j => unround (mask RE.FunRO.f p0 (rd j) w.`1) w) y0
                 (rev (iota_ (i + 1) (11 - i)))).
- auto => /> &hr h1 h2 h3; split; 1: by split => [|_]; smt().
  rewrite (_ : 11 - (i{hr} - 1) = (11 - i{hr}) + 1) 1:/# iotaS 1:/# rev_cons foldl_rcons /=.
  by rewrite /mask.
by auto => />; rewrite /invperm iota0 //=; smt().
qed.

lemma enc_fun_ph (p0 : pw) (x0 : state) :
  phoare [Net(Orc(RE.FunRO)).enc : p = p0 /\ x = x0 ==> res = perm RE.FunRO.f p0 x0] = 1%r.
proof.
conseq (: true ==> true) (enc_fun p0 x0) => //.
by proc; inline *; while true (12 - i); auto => /#.
qed.

lemma dec_fun_ph (p0 : pw) (y0 : state) :
  phoare [Net(Orc(RE.FunRO)).dec : p = p0 /\ y = y0 ==> res = invperm RE.FunRO.f p0 y0] = 1%r.
proof.
conseq (: true ==> true) (dec_fun p0 y0) => //.
by proc; inline *; while true (i + 1); auto => /#.
qed.

(* ---- Ranked password masses ------------------------------------------------------------------ *)
(* Passwords w_1, w_2, ... by decreasing probability, p_i = Pr[P = w_i] (0 past the last one) and
   top(m) = p_1 + ... + p_m, as in A.1. *)
op ranked : pw list = sort (fun (u w : pw) => mu1 dP w <= mu1 dP u) PwT.enum.
op pr (i : int) : real = if 1 <= i <= size ranked then mu1 dP (nth witness ranked (i - 1)) else 0%r.
op top (m : int) : real = bigi predT pr 1 (m + 1).
op p1 : real = pr 1.

(* The fractional top of Theorem 4: T(x) = top(floor x) + (x - floor x) * p_(floor x + 1). *)
op ftop (x : real) : real = top (floor x) + (x - (floor x)%r) * pr (floor x + 1).

op mass (s : pw list) : real = big predT (mu1 dP) s.

lemma pr_ge0 (i : int) : 0%r <= pr i.
proof. by rewrite /pr; case: (1 <= i <= size ranked) => _ //; apply ge0_mu. qed.

lemma sorted_nth (e : 'a -> 'a -> bool) (s : 'a list) (x0 : 'a) (i j : int) :
  (forall y x z, e x y => e y z => e x z) => (forall x, e x x) =>
  sorted e s => 0 <= i <= j < size s => e (nth x0 s i) (nth x0 s j).
proof.
move=> tr rf; elim: s i j => [|x s ih] i j /=; 1: smt().
move=> hp hij; case: (i = 0) => hi0.
- case: (j = 0) => hj0; 1: by apply rf.
  have /allP := order_path_min e tr x s hp; apply; apply mem_nth; smt().
have hj0 : j <> 0 by smt().
rewrite hj0 /=; apply (ih (i - 1) (j - 1)); [exact (path_sorted _ _ _ hp) | smt()].
qed.

lemma pr_mono (i j : int) : 1 <= i <= j => pr j <= pr i.
proof.
move=> hij; case: (j <= size ranked) => hj; last by rewrite {1}/pr; smt(pr_ge0).
rewrite /pr (_ : 1 <= j <= size ranked) 1:/# (_ : 1 <= i <= size ranked) 1:/# /=.
apply (sorted_nth (fun (u w : pw) => mu1 dP w <= mu1 dP u) ranked witness (i - 1) (j - 1)).
- smt().
- smt().
- by apply sort_sorted => u w /=; smt().
smt().
qed.

(* For non-increasing terms, k distinct indices >= 0 weigh at most the first k. *)
lemma sum_distinct_le (a : int -> real) (I : int list) :
  (forall i j, 0 <= i <= j => a j <= a i) =>
  uniq I => (forall i, i \in I => 0 <= i) => big predT a I <= bigi predT a 0 (size I).
proof.
move=> mono; move: {-1}(size I) (eq_refl (size I)) => n; elim/natind: n I.
- move=> n le0n I eqs _ _; have ->: I = [] by smt(size_eq0 size_ge0).
  by rewrite big_nil big_geq.
move=> n ge0n ih I eqs uI geI.
have [M [MI geM]] : exists M, M \in I /\ n <= M.
- case: (exists M, M \in I /\ n <= M) => // nex.
  have : size I <= size (range 0 n).
  + by apply uniq_leq_size => // z zI; rewrite mem_range; smt().
  by rewrite size_range; smt().
rewrite (big_rem _ _ _ M) // big_int_recr 1:/#.
have -> : (if predT M then a M else 0%r) = a M by done.
have h1 : size (rem M I) = n by rewrite List.size_rem // /#.
have h2 : uniq (rem M I) by apply List.rem_uniq.
have h3 : forall i, i \in rem M I => 0 <= i by move=> i hi; apply geI; apply (List.mem_rem M I i hi).
have := ih (rem M I) h1 h2 h3.
have := mono n M _; smt().
qed.

lemma rankedP (u : pw) : u \in ranked.
proof. by rewrite /ranked mem_sort PwT.enumP. qed.

lemma pr_index (u : pw) : pr (index u ranked + 1) = mu1 dP u.
proof.
rewrite /pr (_ : 1 <= index u ranked + 1 <= size ranked) /=; 1: smt(index_ge0 index_mem rankedP).
by rewrite nth_index // rankedP.
qed.

lemma mu1_p1 (w : pw) : mu1 dP w <= p1.
proof. by rewrite -pr_index /p1; apply pr_mono; smt(index_ge0). qed.

lemma top_shift (m : int) : top m = bigi predT (fun i => pr (i + 1)) 0 m.
proof. by rewrite /top (big_addn 0 (m + 1) 1). qed.

(* Distinct passwords weigh at most as many top-ranked ones; so Pr[P in C] <= top(|C|) for a set C
   chosen independently of P. *)
lemma mass_top (s : pw list) : uniq s => mass s <= top (size s).
proof.
move=> us; rewrite /mass top_shift -(size_map (fun u => index u ranked) s).
have -> : big predT (mu1 dP) s = big predT (fun i => pr (i + 1)) (map (fun u => index u ranked) s).
- by rewrite big_map; apply eq_big => //= u _; rewrite /(\o) /= pr_index.
apply sum_distinct_le.
- by move=> i j hij; apply pr_mono; smt().
- rewrite map_inj_in_uniq // => u v _ _ /= h.
  by rewrite -(nth_index witness u ranked) ?rankedP // h nth_index // rankedP.
by move=> i /mapP [u] [_ ->]; apply index_ge0.
qed.

lemma top_mono (m n : int) : m <= n => top m <= top n.
proof.
move=> le_mn; rewrite !top_shift; case: (m < 0) => [lt0m | ge0m].
- by rewrite big_geq 1:/#; apply sumr_ge0 => i _; apply pr_ge0.
by rewrite (big_cat_int m 0 n) 1,2:/# ler_addl; apply sumr_ge0 => i _; apply pr_ge0.
qed.

lemma big_ranked (F : pw -> real) :
  big predT F PwT.enum = bigi predT (fun i => F (nth witness ranked i)) 0 (size ranked).
proof.
have hp : perm_eq ranked PwT.enum by rewrite /ranked; apply perm_sort.
by rewrite -(eq_big_perm _ _ _ _ hp) (big_nth witness); apply eq_big.
qed.

(* Greedy filling: with non-increasing terms, weights in [0, 1] of total at most x give at most the
   first floor x terms and a fraction of the next one. *)
lemma knapsack (a u : int -> real) (N k : int) (x : real) :
  0 <= N => 0 <= k => k%r <= x =>
  (forall i j, 0 <= i <= j => a j <= a i) => (forall i, 0 <= i => 0%r <= a i) =>
  (forall i, 0 <= i < N => 0%r <= u i <= 1%r) => bigi predT u 0 N <= x =>
  bigi predT (fun i => a i * u i) 0 N <= bigi predT a 0 k + (x - k%r) * a k.
proof.
move=> ge0N ge0k lekx mono ge0a hu hsum.
have h1 : bigi predT (fun i => a i * u i) 0 N <=
          a k * bigi predT u 0 N + bigi predT (fun i => if i < k then a i - a k else 0%r) 0 N.
- rewrite mulr_sumr -big_split; apply ler_sum_seq => i /mem_range hi _ /=.
  have := hu i hi; case: (i < k) => hik.
  + by have := mono i k _; [smt() | smt()].
  by have := mono k i _; [smt() | smt()].
have h2 : bigi predT (fun i => if i < k then a i - a k else 0%r) 0 N <=
          bigi predT (fun i => a i - a k) 0 k.
- have ge0c : forall i, 0 <= i < k => 0%r <= a i - a k.
  + by move=> i hi; have := mono i k _; smt().
  case: (N <= k) => hNk.
  + rewrite (big_cat_int N 0 k) 1,2:/#.
    have -> : bigi predT (fun i => if i < k then a i - a k else 0%r) 0 N =
              bigi predT (fun i => a i - a k) 0 N.
    * by apply eq_big_seq => i /mem_range hi /=; rewrite (_ : i < k) 1:/#.
    by rewrite ler_addl; apply sumr_ge0_seq => i /mem_range hi _ /=; apply ge0c; smt().
  rewrite (big_cat_int k 0 N) 1,2:/#.
  have -> : bigi predT (fun i => if i < k then a i - a k else 0%r) k N = 0%r.
  + by rewrite big1_seq // => i [_ /mem_range hi] /=; rewrite (_ : !(i < k)) 1:/#.
  rewrite RField.addr0; apply lerr_eq; apply eq_big_seq => i /mem_range hi /=.
  by rewrite (_ : i < k) 1:/#.
have h3 : bigi predT (fun i => a i - a k) 0 k = bigi predT a 0 k - k%r * a k.
- by rewrite -(sumrB predT a (fun _ => a k)) /= Bigreal.sumri_const.
have := ler_wpmul2l (a k) (ge0a k ge0k) _ _ hsum.
smt().
qed.

(* T(x) bounds every sum of Pr[P = w] * u_w over weights 0 <= u_w <= 1 that sum to at most x, and it
   lies between top(floor x) and top(ceil x). *)
lemma ftop_max (u : pw -> real) (x : real) :
  (forall w, 0%r <= u w <= 1%r) => big predT u PwT.enum <= x =>
  big predT (fun w => mu1 dP w * u w) PwT.enum <= ftop x.
proof.
move=> hu hx.
have ge0x : 0%r <= x by apply (ler_trans _ _ _ _ hx); apply sumr_ge0 => w _; smt().
rewrite big_ranked in hx; rewrite big_ranked /ftop top_shift.
have := knapsack (fun i => pr (i + 1)) (fun i => u (nth witness ranked i)) (size ranked) (floor x) x
          (size_ge0 ranked) _ (floor_le x) _ _ _ hx.
- smt(floor_gt).
- by move=> i j hij /=; apply pr_mono; smt().
- by move=> i _ /=; apply pr_ge0.
- by move=> i _ /=; apply hu.
have -> // : bigi predT (fun i => mu1 dP (nth witness ranked i) * u (nth witness ranked i)) 0 (size ranked)
           = bigi predT (fun i => pr (i + 1) * u (nth witness ranked i)) 0 (size ranked).
by apply eq_big_int => i hi /=; rewrite /pr (_ : 1 <= i + 1 <= size ranked) 1:/#.
qed.

(* Weight 1 on the first k terms and t on the next one. *)
lemma sum_frac (a : int -> real) (k M : int) (t : real) : 0 <= k < M =>
  bigi predT (fun i => a i * (if i < k then 1%r else if i = k then t else 0%r)) 0 M =
  bigi predT a 0 k + a k * t.
proof.
move=> hk; rewrite (big_cat_int k) 1,2:/# (big_ltn k) 1:/#.
have -> : bigi predT (fun i => a i * (if i < k then 1%r else if i = k then t else 0%r)) (k + 1) M = 0%r.
- by apply big1_seq => i [_ /mem_range hi] /=; smt().
have -> : bigi predT (fun i => a i * (if i < k then 1%r else if i = k then t else 0%r)) 0 k = bigi predT a 0 k.
- by apply eq_big_int => i hi /=; smt().
smt().
qed.

(* T(x) is attained, so it is the largest such sum: weight 1 on the first floor x ranked passwords
   and x - floor x on the next one. *)
lemma ftop_attained (x : real) : 0%r <= x =>
  exists (u : pw -> real), (forall w, 0%r <= u w <= 1%r) /\ big predT u PwT.enum <= x /\
    big predT (fun w => mu1 dP w * u w) PwT.enum = ftop x.
proof.
move=> ge0x; pose k := floor x; pose t := x - k%r.
have hk : 0 <= k by rewrite /k; smt(floor_gt).
have ht : 0%r <= t < 1%r by rewrite /t /k; smt(floor_le floor_gt).
pose c := fun (i : int) => if i < k then 1%r else if i = k then t else 0%r.
have hu : uniq ranked by rewrite /ranked sort_uniq PwT.enum_uniq.
have hidx : forall i, 0 <= i < size ranked => index (nth witness ranked i) ranked = i.
- by move=> i hi; apply index_uniq.
pose M := max (size ranked) (k + 1).
exists (fun w => c (index w ranked)); split; 1: by move=> w /=; rewrite /c; smt().
split.
- rewrite big_ranked (eq_big_int 0 (size ranked) _ (fun i => 1%r * c i)).
  + by move=> i hi /=; rewrite hidx.
  apply (ler_trans (bigi predT (fun i => 1%r * c i) 0 M)).
  + rewrite (big_cat_int (size ranked) 0 M); 1,2: smt(size_ge0).
    by rewrite ler_addl; apply sumr_ge0_seq => i _ _ /=; rewrite /c; smt().
  by rewrite (sum_frac (fun _ => 1%r) k M t) 1:/# /= Bigreal.sumri_const 1:// /t; smt().
rewrite big_ranked (eq_big_int 0 (size ranked) _ (fun i => pr (i + 1) * c i)).
- by move=> i hi /=; rewrite hidx // /pr (_ : 1 <= i + 1 <= size ranked) 1:/#.
have -> : bigi predT (fun i => pr (i + 1) * c i) 0 (size ranked) = bigi predT (fun i => pr (i + 1) * c i) 0 M.
- rewrite (big_cat_int (size ranked) 0 M); 1,2: smt(size_ge0).
  rewrite (big1_seq _ _ (range (size ranked) M)) //.
  by move=> i [_ /mem_range hi] /=; rewrite /pr (_ : !(1 <= i + 1 <= size ranked)) 1:/#.
by rewrite (sum_frac (fun i => pr (i + 1)) k M t) 1:/# /ftop top_shift /t /k /=; smt().
qed.

lemma ftop_top (x : real) : 0%r <= x => top (floor x) <= ftop x <= top (ceil x).
proof.
move=> ge0x; have hfl := floor_le x; have hfg := floor_gt x.
have h0 : 0%r <= (x - (floor x)%r) * pr (floor x + 1) by smt(pr_ge0).
rewrite /ftop; split; 1: smt().
case: ((floor x)%r = x) => hxi.
- have -> : ceil x = floor x by smt(ceil_ge ceil_lt).
  smt().
have hc : ceil x = floor x + 1 by smt(ceil_ge ceil_lt).
rewrite hc !top_shift big_int_recr /=; 1: smt().
smt(pr_ge0).
qed.

(* ---- Lemma 3 (one input, two rounds) ------------------------------------------------------------ *)
(* With independent random round functions and a fixed input, the output of n >= 2 rounds is
   uniform. *)
clone PROM.FullRO as RF with
  type in_t <- int * half, type out_t <- half, op dout <- (fun _ => dhalf).

module Rounds = {
  proc run(n : int, x : state) : state = {
    var i, m;
    RF.RO.init();
    i <- 0;
    while (i < n) { m <@ RF.RO.get(i, x.`2); x <- round m x; i <- i + 1; }
    return x;
  }
}.

op rounds (x : state) (ms : half list) : state = foldl (fun (w : state) m => round m w) x ms.

lemma unroundK (m : half) (w : state) : unround m (round m w) = w.
proof. by case: w => l r; rewrite /round /unround /= -xorA xorK xor0. qed.

lemma roundK (m : half) (w : state) : round m (unround m w) = w.
proof. by case: w => l r; rewrite /round /unround /= -xorA xorK xor0. qed.

lemma rounds_bij (ms : half list) : bijective (fun x => rounds x ms).
proof.
exists (fun y => foldl (fun (w : state) m => unround m w) y (rev ms)); split => w /=; rewrite /rounds.
- elim: ms w => [|m ms ih] w //=.
  by rewrite rev_cons foldl_rcons ih /= unroundK.
elim/last_ind: ms w => [|ms m ih] w //=.
by rewrite rev_rcons /= foldl_rcons ih /= roundK.
qed.

(* The first two masks alone make the output uniform. *)
lemma rounds_uniform (x : state) (ms : half list) :
  dmap dstate (fun (m01 : state) => rounds x (m01.`1 :: m01.`2 :: ms)) = dstate.
proof.
have hb : bijective (fun (m01 : state) => rounds x (m01.`1 :: m01.`2 :: ms)).
- have -> : (fun (m01 : state) => rounds x (m01.`1 :: m01.`2 :: ms)) =
            (fun y => rounds y ms) \o (fun (m01 : state) => (x.`1 +^ m01.`1, x.`2 +^ m01.`2)).
  + by apply fun_ext => -[m0 m1]; rewrite /(\o) /rounds /= /round.
  apply bij_comp; 1: exact rounds_bij.
  exists (fun (w : state) => (x.`1 +^ w.`1, x.`2 +^ w.`2)); split => -[a b] /=.
  + by rewrite !xorA !xorK; smt(xorC xor0).
  by rewrite !xorA !xorK; smt(xorC xor0).
apply eq_funi_ll.
- exact (dmap_funi _ _ hb dstate_funi).
- exact (dmap_ll _ _ dstate_ll).
- exact dstate_funi.
exact dstate_ll.
qed.

lemma dlist_rounds (x : state) (n : int) :
  2 <= n => dmap (dlist dhalf n) (fun ms => rounds x ms) = dstate.
proof.
move=> ge2n; have -> : n = 2 + (n - 2) by ring.
have h2 : dlist dhalf 2 = dmap dstate (fun (m01 : state) => [m01.`1; m01.`2]).
- by rewrite (_ : 2 = 1 + 1) // dlistS // dlist1 dmap_dprodR dapply_dmap dmap_comp.
rewrite dlist_add // 1:/# dmap_comp dmap_dprodE.
have -> : (fun a => dmap (dlist dhalf (n - 2))
             (fun b => ((fun ms => rounds x ms) \o (fun (p : half list * half list) => p.`1 ++ p.`2)) (a, b)))
        = (fun a => dlet (dlist dhalf (n - 2)) (fun b => dunit (rounds x (a ++ b)))).
- by apply fun_ext => a; rewrite /dmap /(\o).
rewrite dlet_swap.
have -> : (fun b => dlet (dlist dhalf 2) (fun a => dunit (rounds x (a ++ b)))) = (fun _ => dstate).
- apply fun_ext => b /=; rewrite h2 dlet_dmap /=.
  by rewrite -{2}(rounds_uniform x b) /dmap.
by rewrite dlet_cst // dlist_ll dhalf_ll.
qed.

section Lemma3.
local clone DList.Program as DLP with type t <- half, op d <- dhalf.

local module R3 = {
  proc run(n : int, x : state) : state = { var ms; ms <@ DLP.LoopSnoc.sample(n); return rounds x ms; }
}.

local equiv rounds_R3 : Rounds.run ~ R3.run : ={n, x} ==> ={res}.
proof.
proc; inline *; wp.
while (={i} /\ n{1} = n0{2} /\ x{1} = rounds x{2} l{2} /\
       (forall j r, (j, r) \in RF.RO.m{1} => j < i{1})).
- rcondt{1} ^if; 1: by auto => /> /#.
  auto => /> &1 &2 inv _ r _; split; 1: by rewrite /rounds foldl_cat get_set_sameE.
  by move=> j r'; rewrite mem_set; smt().
by auto => />; smt(mem_empty).
qed.

lemma lemma3 &m (n : int) (x y : state) :
  2 <= n => Pr[Rounds.run(n, x) @ &m : res = y] = mu1 dstate y.
proof.
move=> ge2n.
have -> : Pr[Rounds.run(n, x) @ &m : res = y] = Pr[R3.run(n, x) @ &m : res = y].
- by byequiv rounds_R3.
have -> : Pr[R3.run(n, x) @ &m : res = y] = Pr[DLP.Sample.sample(n) @ &m : rounds x res = y].
- byequiv => //; proc *; inline R3.run; wp.
  by symmetry; call DLP.Sample_LoopSnoc_eq; auto.
byphoare (_ : arg = n ==> rounds x res = y) => //; proc; rnd; skip => /> .
by rewrite -(dlist_rounds x n ge2n) dmap1E; congr; apply fun_ext => ms; rewrite /(\o) /pred1 eq_sym.
qed.
end section Lemma3.

(* The mask component of an answer is uniform. *)
lemma dans_mask : dmap dans mask_of = dhalf.
proof.
rewrite /dans /mask_of dmap_dprodE /= dlet_cst ?dkey_ll // dmap_dprodE /= dlet_cst ?dsalt_ll //.
by rewrite dmap_id.
qed.

(* Over a table without H points, the twelve rounds of any password make the output uniform: their
   masks are fresh, with distinct round indices. Lemma 3 for the network; it gives Remark G9. *)
(* Twelve rounds with fresh masks, and a uniform state. *)
module Masks = {
  proc run(x : state) : state = {
    var i, r;
    i <- 0;
    while (i < 12) { r <$ dans; x <- round (mask_of r) x; i <- i + 1; }
    return x;
  }
}.

module SampleState = { proc run() : state = { var y; y <$ dstate; return y; } }.

section EncUniform.
local clone DList.Program as DLA with type t <- ans, op d <- dans.

local module R5 = {
  proc run(x : state) : state = { var l; l <@ DLA.LoopSnoc.sample(12); return rounds x (map mask_of l); }
}.

local equiv enc_R5 : Net(Ideal).enc ~ R5.run :
  ={x} /\ (forall c, c \in RO.m{1} => isA c \/ isB c) ==> ={res}.
proof.
proc; inline{2} DLA.LoopSnoc.sample; wp.
while (={i} /\ n{2} = 12 /\ 0 <= i{1} /\ x{1} = rounds x{2} (map mask_of l0{2}) /\
       (forall k j r, PH (k, j, r) \in RO.m{1} => Ridx.val j < i{1})).
- seq 2 0 : (={i} /\ n{2} = 12 /\ 0 <= i{1} < 12 /\ x{1} = rounds x{2} (map mask_of l0{2}) /\
             (forall k j r, PH (k, j, r) \in RO.m{1} => Ridx.val j < i{1})).
  + by inline *; auto => />; smt(mem_set dans_ll).
  inline *; rcondt{1} ^if; 1: by auto => />; smt(rdK).
  auto => /> &1 &2 ge0i hi1 hinv r _; split; 1: smt().
  split; 1: by rewrite get_set_sameE /rounds map_cat foldl_cat.
  by move=> k j r'; rewrite mem_set /=; smt(rdK).
by auto => /> &1 hf k j r /hf.
qed.

local equiv masks_R5 : Masks.run ~ R5.run : ={x} ==> ={res}.
proof.
proc; inline{2} DLA.LoopSnoc.sample; wp.
while (={i} /\ n{2} = 12 /\ x{1} = rounds x{2} (map mask_of l0{2})).
- by auto => /> &2 _ r _; rewrite /rounds map_cat foldl_cat.
by auto.
qed.

local lemma R5_uniform &m (x y : state) : Pr[R5.run(x) @ &m : res = y] = mu1 dstate y.
proof.
have -> : Pr[R5.run(x) @ &m : res = y] = Pr[DLA.Sample.sample(12) @ &m : rounds x (map mask_of res) = y].
- byequiv => //; proc *; inline R5.run; wp.
  by symmetry; call DLA.Sample_LoopSnoc_eq; auto.
byphoare (_ : arg = 12 ==> _) => //; proc; rnd; skip => />.
rewrite -(dlist_rounds x 12) // dmap1E -dans_mask dlist_dmap dmapE.
by congr; apply fun_ext => l; rewrite /(\o) /pred1 eq_sym.
qed.

(* The fresh masks make the output uniform and independent of the input. *)
lemma masks_uniform : equiv [Masks.run ~ SampleState.run : true ==> ={res}].
proof.
bypr (res{1}) (res{2}) => // &1 &2 a.
have -> : Pr[Masks.run(x{1}) @ &1 : res = a] = Pr[R5.run(x{1}) @ &1 : res = a] by byequiv masks_R5.
rewrite R5_uniform; byphoare => //; proc; rnd; auto => />; rewrite /pred1 eq_sym.
qed.

lemma enc_uniform &m (p : pw) (x y : state) :
  (forall c, c \in RO.m{m} => isA c \/ isB c) =>
  Pr[Net(Ideal).enc(p, x) @ &m : res = y] = mu1 dstate y.
proof. by move=> hf; rewrite -(R5_uniform &m x y); byequiv enc_R5. qed.
end section EncUniform.

lemma enc_uniform_ph (p0 : pw) (x0 y0 : state) :
  phoare [Net(Ideal).enc : arg = (p0, x0) /\ (forall c, c \in RO.m => isA c \/ isB c) ==> res = y0]
  = (mu1 dstate y0).
proof.
bypr => &m; split; 1: exact ge0_mu.
move=> [ha hf]; have [hp hx] : p{m} = p0 /\ x{m} = x0 by move: ha; rewrite /=.
by rewrite hp hx; exact (enc_uniform &m p0 x0 y0 hf).
qed.

end Feistel.
