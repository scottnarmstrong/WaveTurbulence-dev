/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DecodedCouple
public import WaveTurbulence.Foundations.RegStruct.PairFunctionality
public import WaveTurbulence.Foundations.RegStruct.NormalizeCodes

/-! # Literal perfect-matching properties of decoded couple codes

All finite-list premises are produced from the definitions, independently of
source regularity or the unfinished uniqueness characterization.
-/

public section
namespace WaveTurbulence.Reg
open TTree

/-- No decoded couple code repeats a leaf pair. -/
theorem decodedPair_nodup (Q : RegCpl) : Q.raw.2.Nodup :=
  pair_list_nodup (coupleForest Q) Q.raw.2 (decodedCouple_pairs_valid Q)
    (decodedCouple_pairs_cover Q) (decodedCouple_pair_card Q)

/-- The actual raw relation assigns only one partner to each address. -/
theorem decodedPair_functional (Q : RegCpl) {x y z : Fin 2 × Path}
    (hy : (x,y) ∈ symmPairs Q.raw.2) (hz : (x,z) ∈ symmPairs Q.raw.2) : y = z :=
  pair_relation_functional (coupleForest Q) Q.raw.2 (decodedCouple_pairs_valid Q)
    (decodedCouple_pairs_cover Q) (decodedCouple_pair_card Q) hy hz

/-- No decoded raw pair is a self-pair. -/
theorem decodedPair_no_fixed (Q : RegCpl) (x : Fin 2 × Path) : (x,x) ∉ symmPairs Q.raw.2 :=
  pair_relation_no_fixed (coupleForest Q) Q.raw.2 (decodedCouple_pairs_valid Q)
    (decodedCouple_pairs_cover Q) (decodedCouple_pair_card Q) x

/-- Normalization preserves the raw list up to permutation, including multiplicity. -/
theorem normalizeCouple_pairs_perm (Q : RegCpl) : (normalizeCouple Q).raw.2.Perm Q.raw.2 := by
  apply (List.perm_ext_iff_of_nodup (decodedPair_nodup _) (decodedPair_nodup _)).mpr
  intro z
  exact mem_normalizeCouple_pairsAt Q (0,[]) (1,[]) z

end WaveTurbulence.Reg
