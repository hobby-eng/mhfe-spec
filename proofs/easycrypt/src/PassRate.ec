(* The share p_U of the 24-word values whose seed passes the wallet check, over the random
   functions S and T: E|p_U - 2^-16| <= 2^-136 - 2^-154 (DESIGN-NOTES A.6, "The number of trials"). *)
require import AllCore List Distr DBool DProd FMap IntDiv StdBigop StdOrder Xreal RealSeries Finite.
require import Suite3 Chain Collision Passphrase Generation Selection.
import W128 StdBigop.Bigreal.BRA RealOrder.

(* ---- All states, and p_U as a sum ------------------------------------------------------------ *)
op st_enum : state list = allpairs (fun (a b : W128.word) => (a, b)) W128.words W128.words.

lemma st_enum_uniq : uniq st_enum.
proof. by apply allpairs_uniq; [exact W128.enum_uniq | exact W128.enum_uniq | smt()]. qed.

lemma st_enumP (x : state) : x \in st_enum.
proof. by case: x => a b; rewrite /st_enum allpairsP; exists (a, b); rewrite !W128.enumP. qed.

lemma size_st_enum : size st_enum = 2 ^ 256.
proof.
rewrite /st_enum size_allpairs; have := W128.word_card; rewrite /W128.card => ->.
by rewrite -exprD_nneg.
qed.

op p16 : real = inv (2%r ^ 16).

(* The first 16 bits of T at a seed are zero. *)
op ind (fT : seed -> W16.word * W240.word) (s : seed) : real = b2r ((fT s).`1 = zero16).

(* |U| - 2^240, as a sum over the states. *)
op dev (fS : state * pp -> seed) (fT : seed -> W16.word * W240.word) (q : pp) : real =
  big predT (fun e => ind fT (fS (e, q)) - p16) st_enum.

lemma mu_dstate (P : state -> bool) : mu dstate P = big P (fun _ => inv (2%r ^ 256)) st_enum.
proof.
rewrite -(mu_eq _ (mem (filter P st_enum))) => [x | ]; 1: by rewrite mem_filter st_enumP.
rewrite mu_mem_uniq 1:filter_uniq 1:st_enum_uniq big_filter.
by apply eq_bigr => x _ /=; rewrite dstate1_256.
qed.

lemma pU_dev fS fT q : mu dstate (pass fS fT q) - p16 = dev fS fT q / 2%r ^ 256.
proof.
have h : big (pass fS fT q) (fun (_ : state) => inv (2%r ^ 256)) st_enum =
         big predT (fun (e : state) => ind fT (fS (e, q))) st_enum * inv (2%r ^ 256).
- rewrite big_mkcond mulr_suml; apply eq_bigr => e _ /=.
  by rewrite /ind /pass; case: ((fT (fS (e, q))).`1 = zero16).
rewrite mu_dstate h /dev big_split /= Bigreal.sumr_const count_predT size_st_enum.
rewrite RField.fromintXn // /p16; field; smt(RealOrder.expr_gt0).
qed.

(* ---- Expectations over finite supports ------------------------------------------------------- *)
lemma exp_b2r ['a] (d : 'a distr) (P : 'a -> bool) : E d (fun x => b2r (P x)) = mu d P.
proof. by rewrite /E muE; apply eq_sum => x /=; case: (P x). qed.

lemma exp_big ['a 'b] (d : 'a distr) (s : 'b list) (F : 'b -> 'a -> real) :
  is_finite (support d) =>
  E d (fun x => big predT (fun b => F b x) s) = big predT (fun b => E d (F b)) s.
proof.
move=> hfin; elim: s => [|b s ih].
- rewrite big_nil (_ : (fun (x : 'a) => big predT (fun b => F b x) []) = fun _ => 0%r).
  + by apply fun_ext => x; rewrite big_nil.
  by rewrite expC.
rewrite big_cons /predT /= -ih -(expD d (F b) (fun x => big predT (fun b => F b x) s)).
- exact hasE_finite.
- exact hasE_finite.
by apply eq_exp => x /=; rewrite big_cons.
qed.

(* ---- Over T, at fixed seeds ------------------------------------------------------------------- *)
op dfT = RTE.MUniFinFun.dfun (fun (_ : seed) => dct).

lemma dfT_fin : is_finite (support dfT).
proof.
apply/uniform_finite/RTE.MUniFinFun.dfun_uni => x /=.
by apply dprod_uni; [exact W16.DWord.dunifin_uni | exact W240.DWord.dunifin_uni].
qed.

lemma dct16 : mu dct (fun (c : W16.word * W240.word) => c.`1 = zero16) = p16.
proof.
rewrite (mu_eq _ _ (fun (c : W16.word * W240.word) => pred1 zero16 c.`1 /\ predT c.`2)) 1:/#.
rewrite /dct (dprodE (pred1 zero16) predT) W240.DWord.dunifin_ll /= W16.DWord.dunifin1E W16.word_card /p16.
by rewrite RField.fromintXn // RField.div1r.
qed.

lemma ET_ind s : E dfT (fun fT => ind fT s) = p16.
proof.
rewrite /ind exp_b2r (mu_eq _ _ (fun (f : seed -> W16.word * W240.word) =>
  forall x, (fun x (c : W16.word * W240.word) => x = s => c.`1 = zero16) x (f x))) 1:/#.
rewrite /dfT RTE.MUniFinFun.dfunE (Bigreal.BRM.bigD1 _ _ s) ?(SeedT.enumP, SeedT.enum_uniq) /=.
rewrite (mu_eq _ _ (fun (c : W16.word * W240.word) => c.`1 = zero16)) 1:/# dct16.
rewrite (Bigreal.BRM.eq_bigr _ _ (fun _ => 1%r)) => [x @/predC1 hx /= |].
- by rewrite (mu_eq _ _ predT) 1:/# dct_ll.
by rewrite Bigreal.BRM.big1_eq.
qed.

lemma ET_ind2 s s' : s <> s' => E dfT (fun fT => ind fT s * ind fT s') = p16 * p16.
proof.
move=> hne.
rewrite (_ : (fun fT => ind fT s * ind fT s') =
             fun (fT : seed -> W16.word * W240.word) => b2r ((fT s).`1 = zero16 /\ (fT s').`1 = zero16)).
- by apply fun_ext => f; rewrite /ind; case: ((f s).`1 = zero16); case: ((f s').`1 = zero16).
rewrite exp_b2r (mu_eq _ _ (fun (f : seed -> W16.word * W240.word) =>
  forall x, (fun x (c : W16.word * W240.word) => (x = s \/ x = s') => c.`1 = zero16) x (f x))) 1:/#.
rewrite /dfT RTE.MUniFinFun.dfunE (Bigreal.BRM.bigD1 _ _ s) ?(SeedT.enumP, SeedT.enum_uniq) /=.
rewrite (Bigreal.BRM.bigD1_cond _ _ _ s') ?(SeedT.enumP, SeedT.enum_uniq) 1:/# /=.
rewrite dct16.
rewrite (Bigreal.BRM.eq_bigr _ _ (fun _ => 1%r)) => [x @/predI @/predC1 hx /= |].
- by rewrite (mu_eq _ _ predT) 1:/# dct_ll.
by rewrite Bigreal.BRM.big1_eq.
qed.

lemma hasT (f : (seed -> W16.word * W240.word) -> real) : hasE dfT f.
proof. exact (hasE_finite _ _ dfT_fin). qed.

lemma dfT_ll : is_lossless dfT.
proof. by apply RTE.MUniFinFun.dfun_ll => x /=; exact dct_ll. qed.

lemma ET_term s s' :
  E dfT (fun fT => (ind fT s - p16) * (ind fT s' - p16)) = if s = s' then p16 - p16 * p16 else 0%r.
proof.
rewrite (_ : (fun fT => (ind fT s - p16) * (ind fT s' - p16)) =
             fun (fT : seed -> W16.word * W240.word) =>
               (ind fT s * ind fT s' + (-p16) * ind fT s) + ((-p16) * ind fT s' + p16 * p16)).
- by apply fun_ext => f /=; ring.
rewrite expD 1,2:hasT expD 1,2:hasT expD 1,2:hasT !expZ expC dfT_ll ET_ind ET_ind.
case: (s = s') => [<- | hne].
- rewrite (_ : (fun fT => ind fT s * ind fT s) = fun (fT : seed -> W16.word * W240.word) => ind fT s).
  + by apply fun_ext => f; rewrite /ind; case: ((f s).`1 = zero16).
  by rewrite ET_ind; ring.
by rewrite ET_ind2 //; ring.
qed.

(* ---- E_T[dev^2] = v * coll, coll the number of colliding pairs under S ---------------------- *)
op coll (fS : state * pp -> seed) (q : pp) : real =
  big predT (fun e => big predT (fun e' => b2r (fS (e, q) = fS (e', q))) st_enum) st_enum.

lemma ET_dev2 fS q : E dfT (fun fT => dev fS fT q * dev fS fT q) = (p16 - p16 * p16) * coll fS q.
proof.
rewrite /dev /coll.
rewrite (_ : (fun fT => big predT (fun e => ind fT (fS (e, q)) - p16) st_enum *
                        big predT (fun e => ind fT (fS (e, q)) - p16) st_enum) =
             fun (fT : seed -> W16.word * W240.word) => big predT (fun e => big predT (fun e' =>
               (ind fT (fS (e, q)) - p16) * (ind fT (fS (e', q)) - p16)) st_enum) st_enum).
- by apply fun_ext => f; rewrite mulr_suml; apply eq_bigr => e _ /=; rewrite mulr_sumr.
rewrite exp_big 1:dfT_fin mulr_sumr; apply eq_bigr => e _ /=.
rewrite exp_big 1:dfT_fin mulr_sumr; apply eq_bigr => e' _ /=.
by rewrite ET_term; case: (fS (e, q) = fS (e', q)).
qed.

(* ---- Over S: two distinct points collide with probability at most 2^-512 ------------------- *)
op dfS = RSE.MUniFinFun.dfun (fun (_ : state * pp) => dseed).

lemma dfS_fin : is_finite (support dfS).
proof. by apply/uniform_finite/RSE.MUniFinFun.dfun_uni => x /=; exact W512.DWord.dunifin_uni. qed.

lemma coll_pt (x y : state * pp) : x <> y => mu dfS (fun fS => fS x = fS y) <= inv (2%r ^ 512).
proof.
move=> hne; rewrite /dfS (RSE.MUniFinFun.dfunE_dlet_fix1 _ x) /=.
apply (ler_trans (mu (dlet dseed (fun (_ : seed) => dseed)) (pred1 witness))); last first.
- by rewrite dlet_cst 1:dseed_ll dseed1.
apply mu_dlet_le => v _ /=.
rewrite (mu_eq_support _ _ (fun (f : state * pp -> seed) =>
  forall z, (fun z (w : seed) => z = y => w = v) z (f z))).
- move=> f /RSE.MUniFinFun.dfun_supp /(_ x); rewrite fupdate_eq supp_dunit => hx /=.
  by rewrite hx eq_iff; split => [-> z -> // | /(_ y) //].
rewrite RSE.MUniFinFun.dfunE (Bigreal.BRM.bigD1 _ _ y) ?(SPT.enumP, SPT.enum_uniq) /=.
rewrite fupdate_neq 1:/# (Bigreal.BRM.eq_bigr _ _ (fun _ => 1%r)) => [z @/predC1 hz /= |].
- rewrite (mu_eq _ _ predT) 1:/#; case: (z = x) => [-> | hzx].
  + by rewrite fupdate_eq; exact dunit_ll.
  by rewrite fupdate_neq 1:/#; exact dseed_ll.
by rewrite Bigreal.BRM.big1_eq /= -/(pred1 v) !dseed1.
qed.

lemma dfS_ll : is_lossless dfS.
proof. by apply RSE.MUniFinFun.dfun_ll => x /=; exact dseed_ll. qed.

lemma hasS (f : (state * pp -> seed) -> real) : hasE dfS f.
proof. exact (hasE_finite _ _ dfS_fin). qed.

lemma sum_pred1 (e : state) : big predT (fun e' => b2r (e' = e)) st_enum = 1%r.
proof.
rewrite (eq_bigr _ _ (fun e' => if pred1 e e' then 1%r else 0%r)) => [e' _ /= |].
- by [].
by rewrite -big_mkcond Bigreal.sumr_const count_uniq_mem 1:st_enum_uniq st_enumP.
qed.

lemma ES_coll q : E dfS (fun fS => coll fS q) <= 2%r ^ 256 + 1%r.
proof.
rewrite /coll exp_big 1:dfS_fin.
apply (ler_trans (big predT (fun (_ : state) => 1%r + 2%r ^ 256 * inv (2%r ^ 512)) st_enum)).
- apply Bigreal.ler_sum => e _ /=.
  rewrite exp_big 1:dfS_fin.
  apply (ler_trans (big predT (fun (e' : state) => b2r (e' = e) + inv (2%r ^ 512)) st_enum)).
  + apply Bigreal.ler_sum => e' _ /=; rewrite exp_b2r.
    case: (e' = e) => [-> | hne]; 1: smt(le1_mu e512_gt0).
    by have := coll_pt (e, q) (e', q) _; smt().
  rewrite big_split /= sum_pred1 Bigreal.sumr_const count_predT size_st_enum.
  by rewrite -(RField.fromintXn 2 256) // mulrC.
rewrite Bigreal.sumr_const count_predT size_st_enum -(RField.fromintXn 2 256) //.
have -> : 2%r ^ 512 = 2%r ^ 256 * 2%r ^ 256 by rewrite -RField.exprD_nneg.
have h : 0%r < 2%r ^ 256 by smt(RealOrder.expr_gt0).
by apply lerr_eq; field; smt().
qed.

(* |x| <= x^2 / (2t) + t/2: the square (|x| - t)^2 is not negative. *)
lemma abs_sq (x t : real) : 0%r < t => `|x| <= x * x / (2%r * t) + t / 2%r.
proof.
move=> ht.
have hsq : 0%r <= (`|x| - t) * (`|x| - t) by smt().
have h2 : 0%r <= (`|x| - t) * (`|x| - t) / (2%r * t) by apply divr_ge0 => //; smt().
have e : x * x / (2%r * t) + t / 2%r = `|x| + (`|x| - t) * (`|x| - t) / (2%r * t).
- have -> : x * x = `|x| * `|x| by smt().
  by field; smt().
by rewrite e; smt().
qed.

(* Over the random functions S and T, |p_U - 2^-16| is at most 2^-136 on average. *)
(* The same with its slack: at most 2^-136 - 2^-154. *)
lemma E_pU_tight q :
  E dfS (fun fS => E dfT (fun fT => `|mu dstate (pass fS fT q) - p16|)) <=
  inv (2%r ^ 136) - inv (2%r ^ 136) / 2%r ^ 18.
proof.
pose t := inv (2%r ^ 136); pose N := 2%r ^ 256; pose v := p16 - p16 * p16.
have ht : 0%r < t by smt(RealOrder.expr_gt0 RealOrder.invr_gt0).
have hN : 0%r < N by smt(RealOrder.expr_gt0).
have hp : 0%r < p16 by smt(RealOrder.expr_gt0 RealOrder.invr_gt0).
have hpN : p16 * N = 2%r ^ 240.
- by rewrite /p16 /N (_ : 256 = 16 + 240) // RField.exprD_nneg //; field; smt(RealOrder.expr_gt0).
have htN : t * N = 2%r ^ 120.
- by rewrite /t /N (_ : 256 = 136 + 120) // RField.exprD_nneg //; field; smt(RealOrder.expr_gt0).
have h240 : 2%r ^ 240 = 2%r ^ 120 * 2%r ^ 120 by rewrite -RField.exprD_nneg.
have h1 : 1%r <= 2%r ^ 240 by smt(RealOrder.exprn_ege1).
have hK : t * t * (N * N) = p16 * N.
- by rewrite hpN h240 -htN; ring.
have h2 : 2%r <= p16 * N.
- rewrite hpN (_ : 240 = 1 + 239) // RField.exprD_nneg // RField.expr1.
  have : 1%r <= 2%r ^ 239 by apply RealOrder.exprn_ege1.
  smt().
have h1618 : 2%r ^ 18 = 2%r * 2%r * 2%r ^ 16.
- by rewrite (_ : 18 = 1 + 1 + 16) // !RField.exprD_nneg // RField.expr1.
have hp16 : p16 * 2%r ^ 16 = 1%r by rewrite /p16; field; smt(RealOrder.expr_gt0).
have key : v * (N + 1%r) <= t * t * (N * N) - t * t * (N * N) * 2%r / 2%r ^ 18.
- rewrite hK h1618 /v.
  have -> : p16 * N * 2%r / (2%r * 2%r * 2%r ^ 16) = p16 * (p16 * N) / 2%r.
  + by rewrite /p16; field; smt(RealOrder.expr_gt0).
  have -> : (p16 - p16 * p16) * (N + 1%r) = p16 * N - p16 * (p16 * N) + p16 - p16 * p16 by ring.
  have hp0 : 0%r < p16 by smt(RealOrder.expr_gt0 RealOrder.invr_gt0).
  have hp1 : p16 <= 1%r by rewrite /p16; smt(RealOrder.exprn_ege1 RealOrder.invr_le1 RealOrder.expr_gt0).
  have : p16 * (2%r * (1%r - p16)) <= p16 * (p16 * N) by apply ler_wpmul2l; smt().
  smt().
have inner : forall fS, E dfT (fun fT => `|mu dstate (pass fS fT q) - p16|) <=
             v * coll fS q / (N * N * (2%r * t)) + t / 2%r.
- move=> fS.
  apply (ler_trans (E dfT (fun fT => inv (N * N * (2%r * t)) * (dev fS fT q * dev fS fT q) + t / 2%r))).
  + apply ler_exp; 1,2: exact hasT.
    move=> fT /=; rewrite pU_dev -/N; have := abs_sq (dev fS fT q / N) t ht.
    have -> : dev fS fT q / N * (dev fS fT q / N) / (2%r * t) =
              dev fS fT q * dev fS fT q / (N * N * (2%r * t)) by field; smt(RField.expr2).
    by [].
  rewrite expD 1,2:hasT expZ expC dfT_ll ET_dev2 -/v /=.
  by [].
apply (ler_trans (E dfS (fun fS => v / (N * N * (2%r * t)) * coll fS q + t / 2%r))).
- apply ler_exp; 1,2: exact hasS.
  by move=> fS /=; have := inner fS; smt().
rewrite expD 1,2:hasS expZ expC dfS_ll /=.
have hc := ES_coll q; rewrite -/N in hc.
have h16 : p16 * 2%r ^ 16 = 1%r by rewrite /p16; field; smt(RealOrder.expr_gt0).
have hp1 : p16 <= 1%r by smt(RealOrder.exprn_ege1).
have hv : 0%r <= v.
- by rewrite (_ : v = p16 * (1%r - p16)) 1:/v 1:#ring; apply mulr_ge0; smt().
have hd : 0%r <= inv (N * N * (2%r * t)) by apply invr_ge0; smt().
have e1 : v * E dfS (fun (x : state * pp -> seed) => coll x q) / (N * N * (2%r * t)) <=
          v * (N + 1%r) / (N * N * (2%r * t)).
- by apply ler_wpmul2r => //; apply ler_wpmul2l.
have e2 : v * (N + 1%r) / (N * N * (2%r * t)) <=
          (t * t * (N * N) - t * t * (N * N) * 2%r / 2%r ^ 18) / (N * N * (2%r * t)).
- by apply ler_wpmul2r.
have hden : 2%r * t * N ^ 2 <> 0%r.
- by rewrite RField.expr2; apply RealOrder.gtr_eqF; apply mulr_gt0; [smt() | apply mulr_gt0].
have e3 : (t * t * (N * N) - t * t * (N * N) * 2%r / 2%r ^ 18) / (N * N * (2%r * t)) =
          t / 2%r - t / 2%r ^ 18 by field; smt(RealOrder.expr_gt0).
smt().
qed.

lemma E_pU q :
  E dfS (fun fS => E dfT (fun fT => `|mu dstate (pass fS fT q) - p16|)) <= inv (2%r ^ 136).
proof.
have h : 0%r <= inv (2%r ^ 136) / 2%r ^ 18 by apply divr_ge0; smt(RealOrder.expr_gt0 RealOrder.invr_gt0).
by apply (ler_trans _ _ _ (E_pU_tight q)); rewrite ler_subl_addr ler_addl.
qed.
