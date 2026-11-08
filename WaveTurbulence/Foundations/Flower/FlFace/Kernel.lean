/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Main
public import WaveTurbulence.Frozen.Defs.KernelKgen
public import WaveTurbulence.Frozen.Defs.LayeredGardenFixPat
public import WaveTurbulence.Frozen.Defs.InstDecidableIsFlowerParent
/-! # FL-FACE: Lemma 9.1 inside the frozen `kernelKgen`, and per-tree selections

`kernelKgen_faceExpand` rewrites the time integral of every decoration term of the frozen `kernelKgen` by
`faceIntegral_expand`, with a selection `S κ` that may depend on the decoration (e.g. the selected nodes of large
`|Ω_v|`). It is stated in a context without `Classical`, as the frozen kernel is, so it also checks that the left side
of `faceIntegral_expand` is literally the frozen integrand.

`selOnePerTree_image`: a per-tree choice `v j` in tree `j` (FL-SHELL's `v ∈ Fintype.piFinset (stemSet LG)`) restricted
to any set of trees selects at most one node per tree. `fixPat_plain_eq_none` and `not_mem_flowerParentOff`: in the
flower kernels (`flowerSumP`), with plain patterns, a node that is not a flower parent is free and keeps its phase, so
the selected stem nodes (`stemSet` excludes the flower parent) satisfy `hfix` and `hoff`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace WaveTurbulence.Flower.FlFace
open Finset MeasureTheory

variable {w : ℕ}

/-- A per-tree choice, restricted to a set `J` of trees, selects at most one node per tree. -/
theorem selOnePerTree_image {T : Fin w → TTree} (v : Fin w → GBranch T) (hv : ∀ j, (v j).1.1 = j)
    (J : Finset (Fin w)) : ∀ a ∈ J.image v, ∀ b ∈ J.image v, a.1.1 = b.1.1 → a = b := by
  intro a ha b hb hab
  obtain ⟨i, -, rfl⟩ := mem_image.1 ha
  obtain ⟨j, -, rfl⟩ := mem_image.1 hb
  rw [hv i, hv j] at hab
  rw [hab]

/-- Under plain patterns only the flower parents are pinned. -/
theorem fixPat_plain_eq_none (LG : LayeredGarden w) (t s : ℝ) {v : GBranch LG.garden.tree}
    (hv : ¬ LG.garden.IsFlowerParent v) : LG.fixPat (fun _ => FixPat.plain) t s v = none := by
  simp [LayeredGarden.fixPat, hv]

/-- The removed phases of the flower kernels are at flower parents only. -/
theorem not_mem_flowerParentOff (LG : LayeredGarden w) (c : Bool)
    {inst : DecidablePred LG.garden.IsFlowerParent} {v : GBranch LG.garden.tree}
    (hv : ¬ LG.garden.IsFlowerParent v) :
    v ∉ (if c then @Finset.filter _ LG.garden.IsFlowerParent inst Finset.univ else ∅) := by
  split_ifs
  · simp [hv]
  · simp

/-- **Lemma 9.1 inside `kernelKgen`.** For a decoration-dependent selection `S κ` of free nodes, at most one per tree,
outside `off`, with nonzero frequencies at the coset decoration, each time integral of the frozen kernel is replaced
by `∏ (i ω_v)⁻¹` times the signed sum of its face integrals. -/
theorem kernelKgen_faceExpand (L γ δ : ℝ) {d : ℕ} (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (S : GenDecoration LG.garden d nroot nfl → Finset (GBranch LG.garden.tree))
    (hS : ∀ κ, ∀ a ∈ S κ, ∀ b ∈ S κ, a.1.1 = b.1.1 → a = b) (hfix : ∀ κ, ∀ v ∈ S κ, fix v = none)
    (hoff : ∀ κ, ∀ v ∈ S κ, v ∉ off)
    (hω : ∀ κ, ∀ v ∈ S κ, nodeFreq L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1) v ≠ 0) :
    kernelKgen L γ δ F LG fix off wt up k₀ nroot nfl =
      (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d nroot nfl,
          (epsDec LG.garden κ.1 : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
            ((∏ v ∈ S κ, (Complex.I * nodeFreq L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1) v)⁻¹) *
              ∑ Fc ∈ faces (S κ), faceSign (S κ) Fc *
                faceIntegral L γ δ LG up fix off (cosetDecoration LG.garden L k₀ κ.1) (S κ) Fc) *
            ∏ ℓ ∈ inputLeaves LG.garden,
              (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) := by
  unfold kernelKgen
  congr 1
  refine tsum_congr fun κ => ?_
  rw [faceIntegral_expand LG up fix (S κ) L γ δ off _ (hS κ) (hfix κ) (hoff κ) (hω κ)]

end WaveTurbulence.Flower.FlFace
