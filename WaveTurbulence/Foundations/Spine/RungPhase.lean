/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderFactor
public import WaveTurbulence.Foundations.Spine.ChainBound
/-! # The rung phases as `rungPh` times a unimodular constant (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums Finset

variable {w d : ℕ} {G : Garden w}

/-- The additive linear phase of rung `i`: `p ↦ c ⟨φ(τ₃ - τ₂)(p), φ q⟩`. -/
noncomputable def lamHom (L c : ℝ) {n : ℕ} (S : ChainSigns n) (i : Fin n) (q : Fin d → ℤ) :
    Pt d →+ ℝ where
  toFun p := c * inner ℝ (latticePoint L ((tauHom S i 3 - tauHom S i 2 : Pt d →+ (Fin d → ℤ)) p)) (latticePoint L q)
  map_zero' := by simp [latticePoint_zero']
  map_add' p p' := by
    simp only [map_add, latticePoint_add', inner_add_left, mul_add]

lemma phase_alg (c fu fv tu tv b m Qn s : ℝ) :
    Complex.exp (((Real.pi * ((c * (-(2 * b)) + fu) * tu) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((Real.pi * ((c * (2 * b + 2 * m + s * Qn) + fv) * tv) : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((Real.pi * ((c * s * Qn + fv) * tv + fu * tu) : ℝ) : ℂ) * Complex.I) *
      e (c * (tv - tu) * b + tv * (c * m)) := by
  rw [← Complex.exp_add]
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

include C in
lemma rung_phase_eq (L δ γ fu fv tu tv : ℝ) (κ : GardenDart G → (Fin d → ℤ)) (i : Fin n) :
    Complex.exp (((Real.pi * ((δ * L ^ (2 * γ) * C.rungAU L κ i + fu) * tu) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((Real.pi * ((δ * L ^ (2 * γ) * C.rungAV L κ i + fv) * tv) : ℝ) : ℂ) * Complex.I) =
    Complex.exp (((Real.pi * ((δ * L ^ (2 * γ) * ((C.signs.sg i 2 : ℝ) + (C.signs.sg i 3 : ℝ)) *
        ‖latticePoint L (C.signs.qrel (C.chainOf κ) i)‖ ^ 2 + fv) * tv + fu * tu) : ℝ) : ℂ) * Complex.I) *
      rungPh L (δ * L ^ (2 * γ)) (lamHom L (δ * L ^ (2 * γ)) C.signs i (C.signs.qrel (C.chainOf κ) i))
        (tv, tu) (C.signs.pairs (C.chainOf κ) i) := by
  unfold rungAU rungAV rungPh
  have := phase_alg (δ * L ^ (2 * γ)) fu fv tu tv
    (inner ℝ (latticePoint L (C.signs.pairs (C.chainOf κ) i).1)
        (latticePoint L (C.signs.pairs (C.chainOf κ) i).2))
    (inner ℝ (latticePoint L (C.signs.tau (C.signs.pairs (C.chainOf κ)) i 3 -
          C.signs.tau (C.signs.pairs (C.chainOf κ)) i 2))
        (latticePoint L (C.signs.qrel (C.chainOf κ) i)))
    (‖latticePoint L (C.signs.qrel (C.chainOf κ) i)‖ ^ 2) ((C.signs.sg i 2 : ℝ) + (C.signs.sg i 3 : ℝ))
  convert this using 3
  simp only [bil, lamHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, AddMonoidHom.sub_apply]
  congr 2

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
