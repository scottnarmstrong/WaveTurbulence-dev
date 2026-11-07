/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm6
public import WaveTurbulence.Foundations.FinalCount.AsmProp96b
public import WaveTurbulence.Foundations.FinalCount.G3Untouched
public import WaveTurbulence.Foundations.FinalCount.G3MapDec
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 7: an untouched component of the Operation-5 molecule counts like the component of `hf`.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem op5_M_eq' (hf : HSt V D₀) (Tm : V → Prop) :
    (hf.op5 Tm).s.M = restrictP (eraseSet hf.s.M (tameSet hf Tm)) (keepM hf.s.M (tameSet hf Tm))
      (keepM_closed hf.s.M (tameSet hf Tm)) := rfl

/-- **Untouched component, count equality.** -/
theorem comp_count_eq_unt {hf : HSt V D₀} {Tm : V → Prop} {a : V} (hT : TameFree hf Tm a)
    (ha5 : a ∈ (hf.op5 Tm).s.M.atoms) (A : Set (D₀ → (Fin d → ℤ))) (L γ δ C₁ : ℝ) (P : Finset V → ℝ) :
    (compMol (restrictP (eraseSet hf.s.M (tameSet hf Tm)) (keepM hf.s.M (tameSet hf Tm))
        (keepM_closed hf.s.M (tameSet hf Tm))) a).countA L γ δ C₁ (0 : Mom d)
      (projAdm (restrictP (eraseSet hf.s.M (tameSet hf Tm)) (keepM hf.s.M (tameSet hf Tm))
        (keepM_closed hf.s.M (tameSet hf Tm)))
        (compP (restrictP (eraseSet hf.s.M (tameSet hf Tm)) (keepM hf.s.M (tameSet hf Tm))
        (keepM_closed hf.s.M (tameSet hf Tm))) a)
        (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P =
    (compMol hf.s.M a).countA L γ δ C₁ (0 : Mom d) (compAdm hf a (fun k => k ∈ A)) P := by
  symm
  exact (untouchedIso hT ha5).countA_eq L γ δ C₁ (0 : Mom d) _ _ (fun κ' => by
    constructor
    · rintro ⟨κ5, ⟨κ'', ⟨κs, ⟨k0, hk0, rfl⟩, hκ''⟩, rfl⟩, rfl⟩
      refine ⟨k0, hk0, funext fun x => ?_⟩
      have h2 := untouchedIso_down hT ha5 x
      exact (hκ'' _).trans (congrArg k0 h2)
    · rintro ⟨k0, hk0, e⟩
      refine ⟨fun y => k0 (hf.s.down y.1.1), ⟨fun x => k0 (hf.s.down x.1), ⟨k0 ∘ hf.s.down, ⟨k0, hk0, rfl⟩, fun x => rfl⟩, rfl⟩, ?_⟩
      funext x
      obtain ⟨z, rfl⟩ := (untouchedIso hT ha5).e.surjective x
      have h1 := congrFun e z
      have h2 := untouchedIso_down hT ha5 z
      simp only [compDec] at h1
      rw [h1, ← h2]
      rfl) P

end WaveTurbulence.FinalCountAsm
