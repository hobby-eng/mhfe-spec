(* Instances of the abstract theories. Every axiom of OneContainer.Source and Deniability.Denial is
   realized by concrete bit strings, so none of their results is vacuous, at every source length the
   text names: Source for 12-, 15-, 18-, 21- and 24-word sources, Denial for suite 3 at the same five
   lengths and for suite 4 at 12, 15, 18 and 21 words. Passwords stay those of Suite3: a finite type
   with a distribution. *)
require import AllCore List Distr DProd DBool.
require (*--*) BitWord.
require import Suite3.
require OneContainer Deniability.

(* ---- One container: 12-word sources, E is the left half and the verifier the right half ------ *)
clone OneContainer.Source as Src12 with
  type ent <- W128.word, type ver <- W128.word, type rest <- W128.word,
  op ENT <- 128, op r <- 128,
  op dent <- W128.DWord.dunifin, op dver <- W128.DWord.dunifin, op drest <- W128.DWord.dunifin,
  op pack <- (fun (e v : W128.word) => (e, v)), op unpack <- (fun (x : state) => x),
  op lead <- (fun (e : W128.word) => e),
  type data <- W128.word, op lambda <- 128, op ddata <- W128.DWord.dunifin,
  type phrase <- W128.word * (W128.word * W128.word),
  op phr <- (fun (e : W128.word) (v : W128.word * W128.word) => (e, v)),
  op ent_of <- (fun (f : W128.word * (W128.word * W128.word)) => f.`1)
proof *.
realize ENT_r by done.
realize ENT_range by done.
realize dent_ll by exact W128.DWord.dunifin_ll.
realize dent1 by exact dhalf1.
realize dver_ll by exact W128.DWord.dunifin_ll.
realize dver1 by exact dhalf1.
realize drest_ll by exact W128.DWord.dunifin_ll.
realize drest_funi by exact W128.DWord.dunifin_funi.
realize unpack_pack by done.
realize pack_unpack by case.
realize lead_pack by done.
realize ddata_ll by exact W128.DWord.dunifin_ll.
realize ddata1 by exact dhalf1.
realize ent_of_phr by done.

(* ---- One container: 24-word sources, no verifier ------------------------------------------- *)
clone OneContainer.Source as Src24 with
  type ent <- state, type ver <- unit, type rest <- W256.word,
  op ENT <- 256, op r <- 0,
  op dent <- dstate, op dver <- dunit tt, op drest <- W256.DWord.dunifin,
  op pack <- (fun (e : state) (v : unit) => e), op unpack <- (fun (x : state) => (x, tt)),
  op lead <- (fun (e : state) => e.`1),
  type data <- W128.word, op lambda <- 128, op ddata <- W128.DWord.dunifin,
  type phrase <- state * (unit * W256.word),
  op phr <- (fun (e : state) (v : unit * W256.word) => (e, v)),
  op ent_of <- (fun (f : state * (unit * W256.word)) => f.`1)
proof *.
realize ENT_r by done.
realize ENT_range by done.
realize dent_ll by exact dstate_ll.
realize dent1 by exact dstate1_256.
realize dver_ll by exact dunit_ll.
realize dver1 by move=> v; rewrite dunit1E RField.expr0 RField.invr1; case: v.
realize drest_ll by exact W256.DWord.dunifin_ll.
realize drest_funi by exact W256.DWord.dunifin_funi.
realize unpack_pack by move=> e v; case: v.
realize pack_unpack by done.
realize lead_pack by done.
realize ddata_ll by exact W128.DWord.dunifin_ll.
realize ddata1 by exact dhalf1.
realize ent_of_phr by done.

(* A phrase with its length: a suite 3 state read at the full width, or a shorter source. *)
type 'e phrase3 = [ Full of state | Short of 'e ].

(* ---- Deniability, suite 3: 256-bit states and a 24-word source ------------------------------- *)
clone Deniability.Denial as Den3 with
  type half <- W128.word, op (+^) <- W128.(+^), op zero <- W128.zerow,
  op dhalf <- W128.DWord.dunifin,
  type salt <- W128.word, op dsalt <- W128.DWord.dunifin,
  type key <- W256.word, op dkey <- W256.DWord.dunifin,
  type pw <- pw, op dP <- dP,
  op HalfT.enum <- W128.words, op SaltT.enum <- W128.words, op KeyT.enum <- W256.words,
  op PwT.enum <- Suite3.PwT.enum,
  op W <- 256,
  type ent <- state, type ver <- unit, type rest <- W256.word,
  op ENT <- 256, op dent <- dstate, op dver <- dunit tt, op drest <- W256.DWord.dunifin,
  op pack <- (fun (e : state) (v : unit) => e),
  type phrase <- state, op ph <- (fun (x : state) => x), op phE <- (fun (e : state) => e),
  type record <- unit, op empty <- tt,
  op dU <- (fun (_ : state) => dunit tt), op dReal <- (fun (_ : state) (_ : pw) (_ _ : state) (_ : pw) (_ : state) (_ : unit) => dunit tt)
proof *.
realize xorA by exact W128.xorwA.
realize xorC by exact W128.xorwC.
realize xor0 by exact W128.xorw0.
realize xorK by exact W128.xorwK.
realize HalfT.enum_spec by exact W128.enum_spec.
realize SaltT.enum_spec by exact W128.enum_spec.
realize KeyT.enum_spec by exact W256.enum_spec.
realize PwT.enum_spec by exact Suite3.PwT.enum_spec.
realize dhalf_ll by exact W128.DWord.dunifin_ll.
realize dhalf_funi by exact W128.DWord.dunifin_funi.
realize dsalt_ll by exact W128.DWord.dunifin_ll.
realize dsalt_funi by exact W128.DWord.dunifin_funi.
realize dkey_ll by exact W256.DWord.dunifin_ll.
realize dkey_funi by exact W256.DWord.dunifin_funi.
realize dP_ll by exact dP_ll.
realize dstate1 by exact dstate1_256.
realize dkey1 by exact dkey1.
realize dent_ll by exact dstate_ll.
realize dent1 by exact dstate1_256.
realize dver_ll by exact dunit_ll.
realize drest_ll by exact W256.DWord.dunifin_ll.
realize ph_inj by move=> x y.
realize phE_inj by move=> x y.
realize dU_ll by move=> _; exact dunit_ll.
realize dReal_ll by move=> *; exact dunit_ll.

(* ---- Deniability, suite 3: a 12-word source, read as a phrase of its own length -------------- *)
clone Deniability.Denial as Den3w12 with
  type half <- W128.word, op (+^) <- W128.(+^), op zero <- W128.zerow,
  op dhalf <- W128.DWord.dunifin,
  type salt <- W128.word, op dsalt <- W128.DWord.dunifin,
  type key <- W256.word, op dkey <- W256.DWord.dunifin,
  type pw <- pw, op dP <- dP,
  op HalfT.enum <- W128.words, op SaltT.enum <- W128.words, op KeyT.enum <- W256.words,
  op PwT.enum <- Suite3.PwT.enum,
  op W <- 256,
  type ent <- W128.word, type ver <- W128.word, type rest <- W128.word,
  op ENT <- 128, op dent <- W128.DWord.dunifin, op dver <- W128.DWord.dunifin,
  op drest <- W128.DWord.dunifin,
  op pack <- (fun (e v : W128.word) => (e, v)),
  type phrase <- W128.word phrase3, op ph <- Full<:W128.word>, op phE <- Short<:W128.word>,
  type record <- unit, op empty <- tt,
  op dU <- (fun (_ : W128.word phrase3) => dunit tt),
  op dReal <- (fun (_ : W128.word) (_ : pw) (_ _ : state) (_ : pw) (_ : state) (_ : unit) => dunit tt)
proof *.
realize xorA by exact W128.xorwA.
realize xorC by exact W128.xorwC.
realize xor0 by exact W128.xorw0.
realize xorK by exact W128.xorwK.
realize HalfT.enum_spec by exact W128.enum_spec.
realize SaltT.enum_spec by exact W128.enum_spec.
realize KeyT.enum_spec by exact W256.enum_spec.
realize PwT.enum_spec by exact Suite3.PwT.enum_spec.
realize dhalf_ll by exact W128.DWord.dunifin_ll.
realize dhalf_funi by exact W128.DWord.dunifin_funi.
realize dsalt_ll by exact W128.DWord.dunifin_ll.
realize dsalt_funi by exact W128.DWord.dunifin_funi.
realize dkey_ll by exact W256.DWord.dunifin_ll.
realize dkey_funi by exact W256.DWord.dunifin_funi.
realize dP_ll by exact dP_ll.
realize dstate1 by exact dstate1_256.
realize dkey1 by exact dkey1.
realize dent_ll by exact W128.DWord.dunifin_ll.
realize dent1 by exact dhalf1.
realize dver_ll by exact W128.DWord.dunifin_ll.
realize drest_ll by exact W128.DWord.dunifin_ll.
realize ph_inj by move=> x y /=.
realize phE_inj by move=> x y /=.
realize dU_ll by move=> _; exact dunit_ll.
realize dReal_ll by move=> *; exact dunit_ll.

(* ---- Suite 3, sources of 128 + a bits for 0 < a < 128 (15, 18 and 21 words: a = 32, 64, 96) ---- *)
(* E is its first 128 bits followed by a further bits, the verifier has 128 - a bits, and
   pack(E, v) = E || v: the left half is the first 128 bits of E, the right half the rest of E
   followed by v. *)
abstract theory Short3.
op a : { int | 0 < a < 128 } as a_range.
clone BitWord as WA with op n <- a proof gt0_n by smt(a_range).
clone BitWord as WV with op n <- 128 - a proof gt0_n by smt(a_range).
clone BitWord as WR with op n <- 128 + a proof gt0_n by smt(a_range).

type ent = W128.word * WA.word.
op dent : ent distr = W128.DWord.dunifin `*` WA.DWord.dunifin.
op join (x : WA.word) (v : WV.word) : W128.word = W128.mkword (WA.ofword x ++ WV.ofword v).
op unjoin (z : W128.word) : WA.word * WV.word =
  (WA.mkword (take a (W128.ofword z)), WV.mkword (drop a (W128.ofword z))).
op pack (e : ent) (v : WV.word) : state = (e.`1, join e.`2 v).
op unpack (x : state) : ent * WV.word = ((x.`1, (unjoin x.`2).`1), (unjoin x.`2).`2).

lemma unjoinK (x : WA.word) (v : WV.word) : unjoin (join x v) = (x, v).
proof.
rewrite /unjoin /join W128.ofwordK; 1: by rewrite size_cat WA.size_word WV.size_word; smt().
by rewrite (take_size_cat a) 1:WA.size_word // (drop_size_cat a) 1:WA.size_word // WA.mkwordK WV.mkwordK.
qed.

lemma joinK (z : W128.word) : join (unjoin z).`1 (unjoin z).`2 = z.
proof.
rewrite /unjoin /join /= WA.ofwordK; 1: by rewrite size_takel // W128.size_word; smt(a_range).
rewrite WV.ofwordK; 1: by rewrite size_drop ?W128.size_word; smt(a_range).
by rewrite cat_take_drop W128.mkwordK.
qed.

lemma dent_ll : is_lossless dent.
proof. by apply/dprod_ll; split; [apply W128.DWord.dunifin_ll | apply WA.DWord.dunifin_ll]. qed.

lemma dA1 (x : WA.word) : mu1 WA.DWord.dunifin x = inv (2%r ^ a).
proof. by rewrite WA.DWord.dunifin1E WA.word_card; smt(RField.fromintXn a_range). qed.

lemma dent1 (e : ent) : mu1 dent e = inv (2%r ^ (128 + a)).
proof.
case: e => x y; rewrite /dent dprod1E dhalf1 dA1 -RField.invfM; congr.
by rewrite RField.exprD_nneg //; smt(a_range).
qed.

lemma dver1 (v : WV.word) : mu1 WV.DWord.dunifin v = inv (2%r ^ (128 - a)).
proof. by rewrite WV.DWord.dunifin1E WV.word_card; smt(RField.fromintXn a_range). qed.

clone OneContainer.Source as Src with
  type ent <- ent, type ver <- WV.word, type rest <- WR.word,
  op ENT <- 128 + a, op r <- 128 - a,
  op dent <- dent, op dver <- WV.DWord.dunifin, op drest <- WR.DWord.dunifin,
  op pack <- pack, op unpack <- unpack, op lead <- (fun (e : ent) => e.`1),
  type data <- W128.word, op lambda <- 128, op ddata <- W128.DWord.dunifin,
  type phrase <- ent * (WV.word * WR.word),
  op phr <- (fun (e : ent) (v : WV.word * WR.word) => (e, v)),
  op ent_of <- (fun (f : ent * (WV.word * WR.word)) => f.`1)
proof *.
realize ENT_r by smt().
realize ENT_range by smt(a_range).
realize dent_ll by exact dent_ll.
realize dent1 by exact dent1.
realize dver_ll by exact WV.DWord.dunifin_ll.
realize dver1 by exact dver1.
realize drest_ll by exact WR.DWord.dunifin_ll.
realize drest_funi by exact WR.DWord.dunifin_funi.
realize unpack_pack by move=> e v; rewrite /unpack /pack /= unjoinK /=; case: e.
realize pack_unpack by move=> x; rewrite /unpack /pack /= joinK; case: x.
realize lead_pack by done.
realize ddata_ll by exact W128.DWord.dunifin_ll.
realize ddata1 by exact dhalf1.
realize ent_of_phr by done.

clone Deniability.Denial as Den with
  type half <- W128.word, op (+^) <- W128.(+^), op zero <- W128.zerow,
  op dhalf <- W128.DWord.dunifin,
  type salt <- W128.word, op dsalt <- W128.DWord.dunifin,
  type key <- W256.word, op dkey <- W256.DWord.dunifin,
  type pw <- pw, op dP <- dP,
  op HalfT.enum <- W128.words, op SaltT.enum <- W128.words, op KeyT.enum <- W256.words,
  op PwT.enum <- Suite3.PwT.enum,
  op W <- 256,
  type ent <- ent, type ver <- WV.word, type rest <- WR.word,
  op ENT <- 128 + a, op dent <- dent, op dver <- WV.DWord.dunifin, op drest <- WR.DWord.dunifin,
  op pack <- pack,
  type phrase <- ent phrase3, op ph <- Full<:ent>, op phE <- Short<:ent>,
  type record <- unit, op empty <- tt,
  op dU <- (fun (_ : ent phrase3) => dunit tt),
  op dReal <- (fun (_ : ent) (_ : pw) (_ _ : state) (_ : pw) (_ : state) (_ : unit) => dunit tt)
proof *.
realize xorA by exact W128.xorwA.
realize xorC by exact W128.xorwC.
realize xor0 by exact W128.xorw0.
realize xorK by exact W128.xorwK.
realize HalfT.enum_spec by exact W128.enum_spec.
realize SaltT.enum_spec by exact W128.enum_spec.
realize KeyT.enum_spec by exact W256.enum_spec.
realize PwT.enum_spec by exact Suite3.PwT.enum_spec.
realize dhalf_ll by exact W128.DWord.dunifin_ll.
realize dhalf_funi by exact W128.DWord.dunifin_funi.
realize dsalt_ll by exact W128.DWord.dunifin_ll.
realize dsalt_funi by exact W128.DWord.dunifin_funi.
realize dkey_ll by exact W256.DWord.dunifin_ll.
realize dkey_funi by exact W256.DWord.dunifin_funi.
realize dP_ll by exact dP_ll.
realize dstate1 by exact dstate1_256.
realize dkey1 by exact dkey1.
realize dent_ll by exact dent_ll.
realize dent1 by exact dent1.
realize dver_ll by exact WV.DWord.dunifin_ll.
realize drest_ll by exact WR.DWord.dunifin_ll.
realize ph_inj by move=> x y /=.
realize phE_inj by move=> x y /=.
realize dU_ll by move=> _; exact dunit_ll.
realize dReal_ll by move=> *; exact dunit_ll.
end Short3.

clone Short3 as S3w15 with op a <- 32 proof a_range by done.
clone Short3 as S3w18 with op a <- 64 proof a_range by done.
clone Short3 as S3w21 with op a <- 96 proof a_range by done.

(* ---- Deniability, suite 4: a source of 2 hw bits, so states of two hw-bit halves ------------- *)
(* 12, 15, 18 and 21 words: hw = 64, 80, 96, 112. *)
abstract theory Suite4.
op hw : { int | 0 < hw } as gt0_hw.
clone BitWord as WH with op n <- hw proof gt0_n by exact gt0_hw.

type st = WH.word * WH.word.
op dst : st distr = WH.DWord.dunifin `*` WH.DWord.dunifin.

lemma dh1 (x : WH.word) : mu1 WH.DWord.dunifin x = inv (2%r ^ hw).
proof. by rewrite WH.DWord.dunifin1E WH.word_card; smt(RField.fromintXn gt0_hw). qed.

lemma dst1 (x : st) : mu1 dst x = inv (2%r ^ (2 * hw)).
proof.
case: x => u v; rewrite /dst dprod1E !dh1 -RField.invfM; congr.
by rewrite (_ : 2 * hw = hw + hw) 1:/# RField.exprD_nneg; smt(gt0_hw).
qed.

lemma dst_ll : is_lossless dst.
proof. by apply/dprod_ll; split; apply WH.DWord.dunifin_ll. qed.

clone Deniability.Denial as Den with
  type half <- WH.word, op (+^) <- WH.(+^), op zero <- WH.zerow,
  op dhalf <- WH.DWord.dunifin,
  type salt <- W128.word, op dsalt <- W128.DWord.dunifin,
  type key <- W256.word, op dkey <- W256.DWord.dunifin,
  type pw <- pw, op dP <- dP,
  op HalfT.enum <- WH.words, op SaltT.enum <- W128.words, op KeyT.enum <- W256.words,
  op PwT.enum <- Suite3.PwT.enum,
  op W <- 2 * hw,
  type ent <- st, type ver <- unit, type rest <- W256.word,
  op ENT <- 2 * hw, op dent <- dst, op dver <- dunit tt, op drest <- W256.DWord.dunifin,
  op pack <- (fun (e : st) (v : unit) => e),
  type phrase <- st, op ph <- (fun (x : st) => x), op phE <- (fun (e : st) => e),
  type record <- unit, op empty <- tt,
  op dU <- (fun (_ : st) => dunit tt),
  op dReal <- (fun (_ : st) (_ : pw) (_ _ : st) (_ : pw) (_ : st) (_ : unit) => dunit tt)
proof *.
realize xorA by exact WH.xorwA.
realize xorC by exact WH.xorwC.
realize xor0 by exact WH.xorw0.
realize xorK by exact WH.xorwK.
realize HalfT.enum_spec by exact WH.enum_spec.
realize SaltT.enum_spec by exact W128.enum_spec.
realize KeyT.enum_spec by exact W256.enum_spec.
realize PwT.enum_spec by exact Suite3.PwT.enum_spec.
realize dhalf_ll by exact WH.DWord.dunifin_ll.
realize dhalf_funi by exact WH.DWord.dunifin_funi.
realize dsalt_ll by exact W128.DWord.dunifin_ll.
realize dsalt_funi by exact W128.DWord.dunifin_funi.
realize dkey_ll by exact W256.DWord.dunifin_ll.
realize dkey_funi by exact W256.DWord.dunifin_funi.
realize dP_ll by exact dP_ll.
realize dstate1 by exact dst1.
realize dkey1 by exact dkey1.
realize dent_ll by exact dst_ll.
realize dent1 by exact dst1.
realize dver_ll by exact dunit_ll.
realize drest_ll by exact W256.DWord.dunifin_ll.
realize ph_inj by move=> x y.
realize phE_inj by move=> x y.
realize dU_ll by move=> _; exact dunit_ll.
realize dReal_ll by move=> *; exact dunit_ll.
end Suite4.

clone Suite4 as S4w12 with op hw <- 64 proof gt0_hw by done.
clone Suite4 as S4w15 with op hw <- 80 proof gt0_hw by done.
clone Suite4 as S4w18 with op hw <- 96 proof gt0_hw by done.
clone Suite4 as S4w21 with op hw <- 112 proof gt0_hw by done.
