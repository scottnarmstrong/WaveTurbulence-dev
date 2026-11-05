/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.RegularAsymptotics.PhaseContinuity
public import Mathlib.Analysis.Normed.Group.FunctionSeries
/-! Continuity of the actual decoration sums from the uniform summable majorant. -/
public section
namespace WaveTurbulence.LGSpine
open MeasureTheory Finset Set

/-- Uniform convergence transfers continuity of the literal phase integrals to the kernel.
Only summability on the input cosets and the source's lone-leaf restriction are needed. -/
theorem continuous_kernelK_time {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden w) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    Continuous (fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
      kernelK L γ δ F LG x.1 x.2 k₀ nroot nfl) := by
  unfold kernelK
  apply Continuous.mul continuous_const
  apply continuous_tsum
  · intro κ
    exact (continuous_const.mul
      (continuous_phaseIntegral_no_flower L γ δ LG hflower
        (cosetDecoration LG.garden L k₀ κ.1))).mul continuous_const
  · exact summable_inputLeafMajorant L F LG k₀ nroot nfl hlone hF
  · intro κ x
    exact norm_kernel_summand_le_inputLeafMajorant L γ δ F LG x.1 x.2 k₀ κ

/-- Plain gardens have no flower-parent coordinates. -/
theorem no_flowerParent_of_plain {w : ℕ} (G : Garden w) (hG : G.IsPlain)
    (b : GBranch G.tree) : ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hfl, _⟩
  have h := hG ℓ
  rw [Garden.IsFlower, h] at hfl
  contradiction

/-- Plain gardens have no lone leaves. -/
theorem card_lone_le_one_of_plain {w : ℕ} (G : Garden w) (hG : G.IsPlain) (j : Fin w) :
    (Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsLone ℓ).card ≤ 1 := by
  have he : (Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.IsLone ℓ) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ℓ hℓ
    have hl := (mem_filter.mp hℓ).2.2
    rw [Garden.IsLone, hG ℓ] at hl
    contradiction
  rw [he, Finset.card_empty]
  exact Nat.zero_le _

/-- In particular the couple kernel has continuous two-time slices on the entire time plane. -/
theorem continuous_KQstar_time {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (LG : LayeredGarden 2) (hplain : LG.garden.IsPlain) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => KQstar L γ δ F LG (ts 0) (ts 1) k) := by
  have hc := continuous_kernelK_time L γ δ F LG k (fun _ => 0) 0
    (no_flowerParent_of_plain LG.garden hplain) (card_lone_le_one_of_plain LG.garden hplain) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) :=
    fun ts => ((fun b => if b.1.1 = 0 then ts 0 else ts 1), 0)
  have hu : Continuous u := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro b
    by_cases h : b.1.1 = 0
    · simpa only [h, ite_true] using (continuous_apply (0 : Fin 2))
    · simpa only [h, ite_false] using (continuous_apply (1 : Fin 2))
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    kernelK L γ δ F LG x.1 x.2 k (fun _ => 0) 0) ∘ u)
  exact hc.comp hu

end WaveTurbulence.LGSpine
