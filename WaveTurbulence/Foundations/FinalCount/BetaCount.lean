/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.WorldFinalCountBetaCut
/-! `β`-cut count bound (FINALCOUNT-HALF M2d). DH23 L1784: for a `β`-cut, `k_{ℓ₁}-k_{ℓ₂}` is fixed and the
number of classes of `|k_{ℓ₁}|²-|k_{ℓ₂}|²` is `≲ n`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- The parameter triple of the cut molecule built from `(c, β)` of `M` and the grid indices `(j, e)`. -/
noncomputable def betaParams (v v₂ : V) (x₁ x₂ : D) (T : ℝ) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (j e : ℤ) : (V → Mom d) × (V → ℝ) × (D → Mom d) :=
  (fun a => if a = v₂ then -(∑ b ∈ betaSide M v v₂ x₁ x₂, c b)
      else if a = v then c v + ∑ b ∈ betaSide M v v₂ x₁ x₂, c b else c a,
   fun a => if a = v₂ then -(∑ b ∈ betaSide M v v₂ x₁ x₂, β b) + j * T
      else if a = v then β v + (∑ b ∈ betaSide M v v₂ x₁ x₂, β b) - j * T + e * T / 2 else β a,
   k0)

theorem beta_paramOK (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) (T : ℝ) (c : V → Mom d)
    (β : V → ℝ) (k0 : D → Mom d) (hP : ParamOK M c k0) (j e : ℤ) :
    ParamOK (M.cut v v₂ x₁ x₂) (betaParams M v v₂ x₁ x₂ T c β k0 j e).1
      (betaParams M v v₂ x₁ x₂ T c β k0 j e).2.2 := by
  refine ⟨fun a ha hdeg4 => ?_, hP.2⟩
  have hv₂ : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
  simp only [betaParams]
  by_cases h2 : a = v₂
  · exfalso
    have := cut_deg_v₂ M hcd
    subst h2; omega
  by_cases h1 : a = v
  · exfalso
    have := cut_deg_v M hcd
    subst h1; omega
  simp only [h1, h2, ↓reduceIte]
  have haM : a ∈ M.atoms := by
    have : a ∈ insert v₂ M.atoms := ha
    exact (Finset.mem_insert.mp this).resolve_left h2
  refine hP.1 a haM ?_
  unfold Molecule.deg at hdeg4 ⊢
  rwa [cut_dartsAt_other M hcd h1 h2] at hdeg4

end WaveTurbulence.FinalCount
