/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.GardenConservation
import Mathlib.Tactic

/-!
# Garden/molecule decoration correspondence with root-pair compatibility

TARGET `defdecmol` and the owner ruling F52. The source boundary vector is
computed from the missing root slots. Labels may be arbitrary real vectors;
the affine lattice restriction is preserved by both maps.
-/

public section
namespace WaveTurbulence.Mole
open TTree
variable {w : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (G : Garden w)

/-- TARGET `defdecmol`, corrected by the root-pair compatibility indicator
carried by the garden sums (F52). This is the actual incidence restriction
and its inverse, including nontrivial trees paired with trivial trees. -/
@[expose] def gardenDecorationEquiv (hP : G.IsPlain) (n : Fin w → E)
    (hn : RootPairCompatible G n) :
    {κ : GNode G.tree → E // IsDecoration G κ ∧ ∀ i, κ (GNode.root G.tree i) = n i} ≃
    {k : GardenDart G → E // (∀ x, k (G.molecule.mate x) = k x) ∧
      ∀ v, ∑ x ∈ G.molecule.dartsAt v, G.molecule.dartSign x • k x = gardenSource G hP n v} where
  toFun κ := ⟨restrictLabels G κ.1,by
    have hk := restrictLabels_mate G κ.1 κ.2.1.2
    refine ⟨hk,?_⟩
    intro v
    have he := extend_restrictLabels G hP n κ.1 κ.2.2 κ.2.1.2
    have hs := slotSum_extension G hP n (restrictLabels G κ.1) hk v
    rw [he,(slotSum_eq_zero_iff G κ.1 v).mpr (κ.2.1.1 v)] at hs
    exact sub_eq_zero.mp hs.symm⟩
  invFun k := ⟨extendLabels G hP n k.1,by
    refine ⟨⟨?_,extendLabels_paired G hP n hn k.1 k.2.1⟩,extendLabels_root G hP n k.1⟩
    intro v
    apply (slotSum_eq_zero_iff G _ v).mp
    rw [slotSum_extension G hP n k.1 k.2.1 v,k.2.2 v,sub_self]⟩
  left_inv κ := Subtype.ext (extend_restrictLabels G hP n κ.1 κ.2.2 κ.2.1.2)
  right_inv k := Subtype.ext (restrict_extendLabels G hP n k.1 k.2.1)

omit [AddCommGroup E] [Module ℝ E] in
/-- Both directions preserve any prescribed set of allowed vectors, since
extension uses only bond values and root values, without new arithmetic. -/
theorem extendLabels_mem (hP : G.IsPlain) (n : Fin w → E) (k : GardenDart G → E)
    (S : Set E) (hn : ∀ i, n i ∈ S) (hk : ∀ x, k x ∈ S) (a : GNode G.tree) :
    extendLabels G hP n k a ∈ S := by
  unfold extendLabels
  split
  · exact hn _
  · split
    · exact hk _
    · dsimp only
      split
      · exact hn _
      · exact hk _

/-- In particular the correspondence preserves the exact affine lattice
used by k-decorations of couples, for any lattice scale and base vector. -/
theorem extendLabels_mem_affineLattice {d : ℕ} (H : Garden w) (hP : H.IsPlain)
    (L : ℝ) (base : Mom d) (n : Fin w → Mom d) (k : GardenDart H → Mom d)
    (hn : ∀ i, ∃ z : Fin d → ℤ, n i = base + latticePoint L z)
    (hk : ∀ x, ∃ z : Fin d → ℤ, k x = base + latticePoint L z) (a : GNode H.tree) :
    ∃ z : Fin d → ℤ, extendLabels H hP n k a = base + latticePoint L z :=
  extendLabels_mem H hP n k {y | ∃ z : Fin d → ℤ, y = base + latticePoint L z} hn hk a

end WaveTurbulence.Mole
