/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmCover2
public import WaveTurbulence.Foundations.FinalCount.AsmCountAlg
public import WaveTurbulence.Foundations.FinalCount.G3Adm
/-! **FINALCOUNT-ASSEMBLY, B: the quantity `Q h A = 𝔄(M_h; AdmS A)` of the cover induction** is monotone, subadditive and zero on `∅`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- `𝔄` of the state `h` over the decorations inherited from the class `A`. -/
noncomputable def QS (L γ δ C₁ : ℝ) (w : Mom d) (P : Finset V → ℝ) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) : ℝ≥0∞ :=
  h.s.M.countA L γ δ C₁ w (AdmS (fun k => k ∈ A) h.s) P

theorem QS_mono (L γ δ C₁ : ℝ) (w : Mom d) (P : Finset V → ℝ) (h : HSt V D₀) {A B : Set (D₀ → (Fin d → ℤ))}
    (hAB : A ⊆ B) : QS L γ δ C₁ w P h A ≤ QS L γ δ C₁ w P h B :=
  countA_mono_adm _ L γ δ C₁ w (fun κ ⟨k0, hk, e⟩ => ⟨k0, hAB hk, e⟩) P

theorem QS_union (L γ δ C₁ : ℝ) (w : Mom d) (P : Finset V → ℝ) (h : HSt V D₀) (A B : Set (D₀ → (Fin d → ℤ))) :
    QS L γ δ C₁ w P h (A ∪ B) ≤ QS L γ δ C₁ w P h A + QS L γ δ C₁ w P h B := by
  have := countA_union_le h.s.M L γ δ C₁ w (Finset.univ : Finset Bool)
    (Adm := AdmS (fun k => k ∈ A ∪ B) h.s) (fun b => if b then AdmS (fun k => k ∈ A) h.s else AdmS (fun k => k ∈ B) h.s)
    (fun κ ⟨k0, hk, e⟩ => by
      rcases hk with hk | hk
      · exact ⟨true, by simp, by simpa using ⟨k0, hk, e⟩⟩
      · exact ⟨false, by simp, by simpa using ⟨k0, hk, e⟩⟩) P
  simpa [QS] using this

theorem QS_empty (L γ δ C₁ : ℝ) (w : Mom d) (P : Finset V → ℝ) (h : HSt V D₀) :
    QS L γ δ C₁ w P h ∅ = 0 := by
  have := countA_union_le h.s.M L γ δ C₁ w (∅ : Finset Bool)
    (Adm := AdmS (fun k => k ∈ (∅ : Set (D₀ → (Fin d → ℤ)))) h.s) (fun _ => fun _ => True)
    (fun κ ⟨k0, hk, e⟩ => absurd hk (by simp)) P
  simpa [QS] using this

end WaveTurbulence.FinalCountAsm
