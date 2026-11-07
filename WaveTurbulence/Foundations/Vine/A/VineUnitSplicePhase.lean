/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceGenDecoration
/-! Actual resonances and phase products transport through the selected
simultaneous-splice node and branch maps. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- Every actual branch resonance is invariant under the full node correspondence. -/
theorem unitSplice_omegaNode {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → Mom d)
    (b : GBranch (stSt G σ).G.tree) :
    omegaNode (stSt G σ).G (κ ∘ unitSpliceNodeEquiv Z σ hsel) b =
      omegaNode (stSt Z.target (transportPrescription Z.iso σ)).G κ ((unitSpliceMolIso Z σ hsel).e b) := by
  unfold omegaNode resFactor
  dsimp only [Function.comp_apply]
  rw [unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_branch]
  exact congrArg (fun r => r - ‖κ ((unitSpliceMolIso Z σ hsel).e b).toNode‖ ^ 2)
    (signed_ternary_sum_perm (unitSpliceChildEquiv Z σ hsel b) (unitSpliceChildSlot_middle Z σ hsel b)
      (fun i => ‖κ (((unitSpliceMolIso Z σ hsel).e b).child i)‖ ^ 2))

/-- The full original signed phase product agrees after actual coordinate transport. -/
theorem unitSplice_phaseProd {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (L γ δ : ℝ)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → Mom d)
    (t : GBranch (stSt Z.target (transportPrescription Z.iso σ)).G.tree → ℝ) :
    phaseProd L γ δ (stSt G σ).G (κ ∘ unitSpliceNodeEquiv Z σ hsel) (t ∘ (unitSpliceMolIso Z σ hsel).e) =
      phaseProd L γ δ (stSt Z.target (transportPrescription Z.iso σ)).G κ t := by
  unfold phaseProd
  trans ∏ b : GBranch (stSt G σ).G.tree,
    Complex.exp ((Real.pi * (((stSt Z.target (transportPrescription Z.iso σ)).G.sign
      ((unitSpliceMolIso Z σ hsel).e b).toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode (stSt Z.target (transportPrescription Z.iso σ)).G κ ((unitSpliceMolIso Z σ hsel).e b) *
          t ((unitSpliceMolIso Z σ hsel).e b) : ℝ) * Complex.I)
  · apply Finset.prod_congr rfl
    intro b _
    rw [unitSplice_omegaNode, unitSpliceMolIso_branch_sign]
    rfl
  · exact (unitSpliceMolIso Z σ hsel).e.prod_comp
      (fun b : GBranch (stSt Z.target (transportPrescription Z.iso σ)).G.tree =>
        Complex.exp ((Real.pi * (((stSt Z.target (transportPrescription Z.iso σ)).G.sign b.toNode : ℤˣ) : ℤ) *
          δ * L ^ (2 * γ) * omegaNode (stSt Z.target (transportPrescription Z.iso σ)).G κ b * t b : ℝ) * Complex.I))

end WaveTurbulence.VineA
