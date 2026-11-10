/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsSb5
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsGlue3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase2

/-! # `UAbs` calculus (V5 Step 4d part C, 4d-B2 integration, leaf `bot`)

`uAbs_mono`, `uAbs_const_mul`, `uAbs_finsetSum`, `uAbs_transport` (along a bijection of the decorations and a measure-preserving change of the
times), `uAbs_of_summand_eq` (a summand equal to the CL local summand of a native garden has the uniform bound `baseConst`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

section Calc
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem uAbs_const_mul (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ) (c : ℂ) {C : ℝ}
    (h : UAbs R L base Ψ C) : UAbs R L base (fun x t u => c * Ψ x t u) (‖c‖ * C) := fun t β => by
  obtain ⟨h1, h2, h3⟩ := h t β
  have hfun : (fun κ : CLLocalDecoration R L base β => ∫ τ : CLInternalTime R,
      ‖c * Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)‖) =
      fun κ => ‖c‖ * ∫ τ : CLInternalTime R, ‖Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)‖ := by
    funext κ; simp_rw [norm_mul]; rw [integral_const_mul]
  refine ⟨fun κ => (h1 κ).const_mul c, ?_, ?_⟩
  · rw [hfun]; exact h2.mul_left _
  · rw [hfun, tsum_mul_left]
    exact mul_le_mul_of_nonneg_left h3 (norm_nonneg c)

theorem uAbs_finsetSum {β' : Type*} (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) (s : Finset β')
    (Ψ : β' → (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ) (C : β' → ℝ)
    (h : ∀ i ∈ s, UAbs R L base (Ψ i) (C i)) :
    UAbs R L base (fun x t u => ∑ i ∈ s, Ψ i x t u) (∑ i ∈ s, C i) := fun t β => by
  classical
  have hh := fun i (hi : i ∈ s) => h i hi t β
  have hle : ∀ κ : CLLocalDecoration R L base β, ∫ τ : CLInternalTime R,
      ‖∑ i ∈ s, Ψ i (clExtendIndices R κ.1) t (clLocalClock R t τ)‖ ≤
      ∑ i ∈ s, ∫ τ : CLInternalTime R, ‖Ψ i (clExtendIndices R κ.1) t (clLocalClock R t τ)‖ := by
    intro κ
    rw [← integral_finsetSum _ fun i hi => ((hh i hi).1 κ).norm]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun τ => norm_nonneg _)
      (integrable_finsetSum _ fun i hi => ((hh i hi).1 κ).norm) (Filter.Eventually.of_forall fun τ => ?_)
    exact norm_sum_le _ _
  have hs : Summable fun κ : CLLocalDecoration R L base β =>
      ∑ i ∈ s, ∫ τ : CLInternalTime R, ‖Ψ i (clExtendIndices R κ.1) t (clLocalClock R t τ)‖ :=
    summable_sum fun i hi => (hh i hi).2.1
  have hs0 : Summable fun κ : CLLocalDecoration R L base β =>
      ∫ τ : CLInternalTime R, ‖∑ i ∈ s, Ψ i (clExtendIndices R κ.1) t (clLocalClock R t τ)‖ :=
    Summable.of_nonneg_of_le (fun κ => integral_nonneg fun _ => norm_nonneg _) hle hs
  refine ⟨fun κ => integrable_finsetSum _ fun i hi => (hh i hi).1 κ, hs0, ?_⟩
  calc ∑' κ : CLLocalDecoration R L base β, ∫ τ : CLInternalTime R,
        ‖∑ i ∈ s, Ψ i (clExtendIndices R κ.1) t (clLocalClock R t τ)‖
      ≤ ∑' κ : CLLocalDecoration R L base β, ∑ i ∈ s, ∫ τ : CLInternalTime R,
          ‖Ψ i (clExtendIndices R κ.1) t (clLocalClock R t τ)‖ := hs0.tsum_le_tsum hle hs
    _ = ∑ i ∈ s, ∑' κ : CLLocalDecoration R L base β, ∫ τ : CLInternalTime R,
          ‖Ψ i (clExtendIndices R κ.1) t (clLocalClock R t τ)‖ := Summable.tsum_finsetSum fun i hi => (hh i hi).2.1
    _ ≤ ∑ i ∈ s, C i := Finset.sum_le_sum fun i hi => (hh i hi).2.2

end Calc

section Transport
variable {w d : ℕ} {G G' : Garden w} {U : Finset (GBranch G.tree)} {U' : Finset (GBranch G'.tree)} {a b : GBranch G.tree}
  {a' b' : GBranch G'.tree}

theorem uAbs_transport (R : CLRegionData G U a b) (R' : CLRegionData G' U' a' b') (L : ℝ) (base : Mom d)
    (E : ∀ β : Fin 4 → Mom d, CLLocalDecoration R L base β ≃ CLLocalDecoration R' L base β)
    (m : CLInternalTime R ≃ᵐ CLInternalTime R') (hm : MeasurePreserving m volume volume)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (Ψ' : (GNode G'.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G'.tree → ℝ) → ℂ) {C : ℝ}
    (hΨ : ∀ (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R),
      Ψ' (clExtendIndices R' (E β κ).1) t (clLocalClock R' t (m τ)) = Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ))
    (h : UAbs R' L base Ψ' C) : UAbs R L base Ψ C := by
  intro t β
  obtain ⟨h1, h2, h3⟩ := h t β
  obtain ⟨hI, hN, hS⟩ := tsum_integral_norm_transport (E β) m hm
    (fun (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R) => Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ))
    (fun (κ' : CLLocalDecoration R' L base β) (τ' : CLInternalTime R') => Ψ' (clExtendIndices R' κ'.1) t (clLocalClock R' t τ'))
    (fun κ τ => hΨ t β κ τ) h1
  refine ⟨hI, ?_, ?_⟩
  · have : (fun κ : CLLocalDecoration R L base β => ∫ τ : CLInternalTime R, ‖Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ)‖) =
        (fun κ' : CLLocalDecoration R' L base β => ∫ τ' : CLInternalTime R',
          ‖Ψ' (clExtendIndices R' κ'.1) t (clLocalClock R' t τ')‖) ∘ (E β) := funext fun κ => hN κ
    rw [this]
    exact ((E β).summable_iff (f := fun κ' : CLLocalDecoration R' L base β => ∫ τ' : CLInternalTime R',
      ‖Ψ' (clExtendIndices R' κ'.1) t (clLocalClock R' t τ')‖)).mpr h2
  · rw [hS]; exact h3

end Transport

section Native
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

/-- A summand equal to the CL local summand of a native garden has the uniform bound `baseConst`. -/
theorem uAbs_of_summand_eq (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (hF : HF D hG L F layer base) (hL : L ≠ 0)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → ℂ)
    (hΨ : ∀ (t : Fin 3 → ℝ) (β : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β) (τ : CLInternalTime R),
      Ψ (clExtendIndices R κ.1) t (clLocalClock R t τ) = psiNat D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) t (clLocalClock R t τ)) :
    UAbs R L base Ψ (baseConst D hG L γ δ F layer hLayer base R) := by
  have h := uAbs_psiNat (hLayer := hLayer) (γ := γ) (δ := δ) hU R hF hL
  intro t β
  obtain ⟨h1, h2, h3⟩ := h t β
  simp_rw [hΨ t β]
  exact ⟨h1, h2, h3⟩

end Native

end WaveTurbulence.VineEstS5C
