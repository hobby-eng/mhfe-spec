(* Suite 3: 128-bit halves and salts, 256-bit keys (DESIGN-NOTES A.1). Passwords and their
   distribution stay abstract. *)
require import AllCore Distr DProd.
require (*--*) BitWord Model.

clone BitWord as W128 with op n <- 128 proof gt0_n by done.
clone BitWord as W256 with op n <- 256 proof gt0_n by done.

clone include Model.Feistel with
  type half <- W128.word,
  op (+^) <- W128.(+^),
  op zero <- W128.zerow,
  op dhalf <- W128.DWord.dunifin,
  type salt <- W128.word,
  op dsalt <- W128.DWord.dunifin,
  type key <- W256.word,
  op dkey <- W256.DWord.dunifin,
  op HalfT.enum <- W128.words,
  op SaltT.enum <- W128.words,
  op KeyT.enum <- W256.words
proof xorA, xorC, xor0, xorK, dhalf_ll, dhalf_funi, dsalt_ll, dsalt_funi, dkey_ll, dkey_funi,
      HalfT.enum_spec, SaltT.enum_spec, KeyT.enum_spec.
realize xorA by exact W128.xorwA.
realize xorC by exact W128.xorwC.
realize xor0 by exact W128.xorw0.
realize xorK by exact W128.xorwK.
realize dhalf_ll by exact W128.DWord.dunifin_ll.
realize dhalf_funi by exact W128.DWord.dunifin_funi.
realize dsalt_ll by exact W128.DWord.dunifin_ll.
realize dsalt_funi by exact W128.DWord.dunifin_funi.
realize dkey_ll by exact W256.DWord.dunifin_ll.
realize dkey_funi by exact W256.DWord.dunifin_funi.
realize HalfT.enum_spec by exact W128.enum_spec.
realize SaltT.enum_spec by exact W128.enum_spec.
realize KeyT.enum_spec by exact W256.enum_spec.

lemma dhalf1 (x : W128.word) : mu1 W128.DWord.dunifin x = inv (2%r ^ 128).
proof. by rewrite W128.DWord.dunifin1E W128.word_card /=; smt(RField.fromintXn). qed.

lemma dkey1 (k : W256.word) : mu1 W256.DWord.dunifin k = inv (2%r ^ 256).
proof. by rewrite W256.DWord.dunifin1E W256.word_card /=; smt(RField.fromintXn). qed.

lemma dstate1_256 (x : state) : mu1 dstate x = inv (2%r ^ 256).
proof.
case: x => a b; rewrite /dstate dprod1E !dhalf1 -RField.invfM.
by congr; rewrite -RField.exprD_nneg.
qed.
