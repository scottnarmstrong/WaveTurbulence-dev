/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.GenMerge
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Mink

/-! # P3: finite Minkowski for `XNorm00Restr` and linearity of `lkRaw` over finite sums (V5 Step 4d part C)

`XNorm00Restr_finsum_le`: one factor `cc + 1` for a finite sum.  `lkRaw_finsum`: `lkRaw` of a finite sum of summands, each absolutely
convergent (`LkAbs`), is the sum of the `lkRaw`s, given the pointwise (on the clock domain) identity of the summands.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P3
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS4 WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory
open scoped ENNReal

/-- **Finite Minkowski** for order-zero restriction norms (one cutoff factor for the whole finite sum). -/
theorem XNorm00Restr_finsum_le {r : ℕ} {V : Type*} {ι : Type*} [Fintype ι] {θ : ℝ} (hθ : 0 ≤ θ) (q : Fin r → ℝ)
    {B : Set (Fin r → ℝ)} (hB : B ⊆ WaveTurbulence.VineEstS3.FS.cell q) {K : Set V} (hK : K.Countable)
    (f : ι → (Fin r → ℝ) → V → ℂ) (F : (Fin r → ℝ) → V → ℂ)
    (hsum : ∀ t ∈ B, ∀ v ∈ K, F t v = ∑ j, f j t v) :
    XNorm00Restr θ B K F ≤
      (WaveTurbulence.Fourier.cutoffMultiplierConstant θ (WaveTurbulence.VineEstS3.FS.cutQ q) + 1) * ∑ j, XNorm00Restr θ B K (f j) := by
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ => MeasurableSpace.measurableSet_top⟩
  have := WaveTurbulence.VineEstS3.Mink.XNorm00Restr_tsum_le (ι := ι) hθ q hB hK f F fun t ht v hv => by
    rw [hsum t ht v hv]; exact hasSum_fintype _
  simpa [tsum_fintype] using this

/-- Absolute convergence of a summand `ψ` in the local sum-integral. -/
def LkAbs {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b)
    (L : ℝ) (base : Mom d) (ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) : Prop :=
  (∀ κ : CLLocalDecoration R L base β, Integrable fun τ : CLInternalTime R => ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)) ∧
    Summable fun κ : CLLocalDecoration R L base β => ∫ τ : CLInternalTime R, ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)

/-- **Linearity of `lkRaw` over a finite sum**, given the identity of the summands for a.e. clock of every decoration. -/
theorem lkRaw_finsum {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) {ι : Type*} [Fintype ι]
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (ψ : ι → (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (t : Fin 3 → ℝ) (β : Fin 4 → Mom d)
    (hae : ∀ κ : CLLocalDecoration R L base β, ∀ᵐ τ : CLInternalTime R,
      Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) = ∑ j, ψ j (clExtendIndices R κ.1) t (clLocalClock R t τ))
    (habs : ∀ j, LkAbs R L base (ψ j) t β) :
    lkRaw R L base Ψ t β = ∑ j, lkRaw R L base (ψ j) t β := by
  unfold lkRaw
  have h1 : ∀ κ : CLLocalDecoration R L base β, ∫ τ : CLInternalTime R, Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) =
      ∑ j, ∫ τ : CLInternalTime R, ψ j (clExtendIndices R κ.1) t (clLocalClock R t τ) := fun κ => by
    rw [integral_congr_ae (hae κ), integral_finsetSum]
    exact fun j _ => (habs j).1 κ
  simp_rw [h1]
  rw [Summable.tsum_finsetSum (fun j _ => (habs j).2)]

end WaveTurbulence.VineEstS5C.P3
