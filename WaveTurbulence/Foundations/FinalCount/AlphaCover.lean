/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AlphaBasics
/-! The `α`-cut (FINALCOUNT-G2 step 4), part 2: covering the decorations of `M` by post classes
indexed by the gap `r = k_{ℓ₁} - k_{ℓ₂}` and the energy windows (DH23 L1784, the `α`-cut count
`(RL)^d (1 + δ R L^{2γ})`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem latticePoint_sub (L : ℝ) (a b : Fin d → ℤ) :
    latticePoint L (a - b) = latticePoint L a - latticePoint L b := by
  ext j
  simp [latticePoint, sub_div]

/-- The parameter triple of the cut molecule for the grid indices `(n, j, e)`. -/
noncomputable def alphaParams (v v₂ : V) (L τ : ℝ) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (n : Fin d → ℤ) (j e : ℤ) : (V → Mom d) × (V → ℝ) × (D → Mom d) :=
  (fun a => if a = v₂ then c v + latticePoint L n else if a = v then -(latticePoint L n) else c a,
   fun a => if a = v₂ then β v - j * τ + e * τ else if a = v then j * τ else β a,
   k0)

theorem alpha_paramOK (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4) (L τ : ℝ) (c : V → Mom d)
    (β : V → ℝ) (k0 : D → Mom d) (hP : ParamOK M c k0) (n : Fin d → ℤ) (j e : ℤ) :
    ParamOK (M.cut v v₂ x₁ x₂) (alphaParams v v₂ L τ c β k0 n j e).1
      (alphaParams v v₂ L τ c β k0 n j e).2.2 := by
  refine ⟨fun a ha hdeg4 => ?_, hP.2⟩
  simp only [alphaParams]
  by_cases h2 : a = v₂
  · exfalso
    have := cut_deg_v₂ M hcd
    subst h2; omega
  by_cases h1 : a = v
  · exfalso
    have := cut_deg_v M hcd
    subst h1; omega
  simp only [h1, h2, ↓reduceIte]
  have haM : a ∈ M.atoms := (Finset.mem_insert.mp ha).resolve_left h2
  refine hP.1 a haM ?_
  unfold Molecule.deg at hdeg4 ⊢
  rwa [cut_dartsAt_other M hcd h1 h2] at hdeg4

end WaveTurbulence.FinalCount
