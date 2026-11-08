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

/-- B1b-2 (Mk-general form of `unitSplice_omegaNode`). -/
theorem unitSplice_omegaNodeMk {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → Mom d)
    (b : GBranch (stSt G σ Mk).G.tree) :
    omegaNode (stSt G σ Mk).G (κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) b =
      omegaNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G κ ((unitSpliceMolIsoMk Z σ hT hsel).e b) := by
  unfold omegaNode resFactor
  dsimp only [Function.comp_apply]
  rw [unitSpliceNodeEquiv_childMk, unitSpliceNodeEquiv_childMk, unitSpliceNodeEquiv_childMk, unitSpliceNodeEquiv_branchMk]
  exact congrArg (fun r => r - ‖κ ((unitSpliceMolIsoMk Z σ hT hsel).e b).toNode‖ ^ 2)
    (signed_ternary_sum_perm (unitSpliceChildEquivMk Z σ hT hsel b) (unitSpliceChildSlot_middleMk Z σ hT hsel b)
      (fun i => ‖κ (((unitSpliceMolIsoMk Z σ hT hsel).e b).child i)‖ ^ 2))

/-- Every actual branch resonance is invariant under the full node correspondence. -/
theorem unitSplice_omegaNode {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → Mom d)
    (b : GBranch (stSt G σ).G.tree) :
    omegaNode (stSt G σ).G (κ ∘ unitSpliceNodeEquiv Z σ hsel) b =
      omegaNode (stSt Z.target (transportPrescription Z.iso σ)).G κ ((unitSpliceMolIso Z σ hsel).e b) :=
  unitSplice_omegaNodeMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel κ b

/-- B1b-2 (Mk-general form of `unitSplice_phaseProd`). -/
theorem unitSplice_phaseProdMk {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (L γ δ : ℝ)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → Mom d)
    (t : GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → ℝ) :
    phaseProd L γ δ (stSt G σ Mk).G (κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) (t ∘ (unitSpliceMolIsoMk Z σ hT hsel).e) =
      phaseProd L γ δ (stSt Z.target (transportPrescription Z.iso σ) Mk').G κ t := by
  unfold phaseProd
  trans ∏ b : GBranch (stSt G σ Mk).G.tree,
    Complex.exp ((Real.pi * (((stSt Z.target (transportPrescription Z.iso σ) Mk').G.sign
      ((unitSpliceMolIsoMk Z σ hT hsel).e b).toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G κ ((unitSpliceMolIsoMk Z σ hT hsel).e b) *
          t ((unitSpliceMolIsoMk Z σ hT hsel).e b) : ℝ) * Complex.I)
  · apply Finset.prod_congr rfl
    intro b _
    rw [unitSplice_omegaNodeMk, unitSpliceMolIso_branch_signMk]
    rfl
  · exact (unitSpliceMolIsoMk Z σ hT hsel).e.prod_comp
      (fun b : GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree =>
        Complex.exp ((Real.pi * (((stSt Z.target (transportPrescription Z.iso σ) Mk').G.sign b.toNode : ℤˣ) : ℤ) *
          δ * L ^ (2 * γ) * omegaNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G κ b * t b : ℝ) * Complex.I))

/-- The full original signed phase product agrees after actual coordinate transport. -/
theorem unitSplice_phaseProd {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (L γ δ : ℝ)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → Mom d)
    (t : GBranch (stSt Z.target (transportPrescription Z.iso σ)).G.tree → ℝ) :
    phaseProd L γ δ (stSt G σ).G (κ ∘ unitSpliceNodeEquiv Z σ hsel) (t ∘ (unitSpliceMolIso Z σ hsel).e) =
      phaseProd L γ δ (stSt Z.target (transportPrescription Z.iso σ)).G κ t :=
  unitSplice_phaseProdMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel L γ δ κ t

end WaveTurbulence.VineA
