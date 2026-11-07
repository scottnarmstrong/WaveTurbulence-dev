/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSurvivingDarts
/-! The actual selected-splice dart map preserves PC/LP tags and agrees
with the full node map on the exact bond-momentum arguments of the kernel. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Mole WaveTurbulence.LGSpine
variable {w d : ℕ} {G : Garden w}

/-- The actual full leaf map preserves LP typing in both directions. -/
theorem unitSpliceLP_profile_iff (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    ((stSt Z.target (transportPrescription Z.iso σ)).G.mark (unitSpliceLeafEquiv Z σ hsel q) = none ∧
      (unitSpliceLeafEquiv Z σ hsel q).1.2 ≠ [] ∧
      ((stSt Z.target (transportPrescription Z.iso σ)).G.pair (unitSpliceLeafEquiv Z σ hsel q)).1.2 ≠ []) ↔
    ((stSt G σ).G.mark q = none ∧ q.1.2 ≠ [] ∧ ((stSt G σ).G.pair q).1.2 ≠ []) := by
  have hm := Iff.of_eq (congrArg (fun x : Option MarkTag => x = none) (unitSpliceLeafEquiv_mark Z σ hsel q))
  have hr := not_congr (unitSpliceLeafEquiv_root Z σ hsel q)
  have hp := (Iff.of_eq (congrArg (fun l : GLeaf (stSt Z.target (transportPrescription Z.iso σ)).G.tree => l.1.2 ≠ [])
    (unitSpliceLeafEquiv_pair Z σ hsel q).symm)).trans
      (not_congr (unitSpliceLeafEquiv_root Z σ hsel ((stSt G σ).G.pair q)))
  exact and_congr hm (and_congr hr hp)

/-- The actual LP-leaf carrier correspondence. -/
noncomputable def unitSpliceLPLeafEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    GardenLPLeaf (stSt G σ).G ≃ GardenLPLeaf (stSt Z.target (transportPrescription Z.iso σ)).G :=
  (unitSpliceLeafEquiv Z σ hsel).subtypeEquiv (fun q => (unitSpliceLP_profile_iff Z σ hsel q).symm)

/-- The actual nonroot-branch carrier correspondence. -/
noncomputable def unitSplicePCEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    {c : GBranch (stSt G σ).G.tree // c.1.2 ≠ []} ≃
      {c : GBranch (stSt Z.target (transportPrescription Z.iso σ)).G.tree // c.1.2 ≠ []} :=
  (unitSpliceMolIso Z σ hsel).e.subtypeEquiv
    (fun c => (not_congr (unitSpliceMolIso_branch_root Z σ hsel c)).symm)

/-- Actual surviving PC darts retain their side and follow the actual branch map. -/
theorem unitSpliceMolIso_pc (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (c : {c : GBranch (stSt G σ).G.tree // c.1.2 ≠ []}) (side : Bool) :
    (unitSpliceMolIso Z σ hsel).d (.inl (c, side)) = .inl (unitSplicePCEquiv Z σ hsel c, side) := by
  apply (stSt Z.target (transportPrescription Z.iso σ)).M.od_inj
  have he : naiveDartEquiv G Z.P (.inl (spliceOldPC (stSt G σ) c, side)) =
      .inl (spliceOldPC (stSt Z.target (transportPrescription Z.iso σ)) (unitSplicePCEquiv Z σ hsel c), side) := by
    apply congrArg (fun b => Sum.inl (b, side))
    apply Subtype.ext
    exact (unitSpliceMolIso_branch_names Z σ hsel c.1).symm
  exact (unitSpliceMolIso_surviving_dart_names Z σ hsel (.inl (c, side))).trans
    ((congrArg (naiveDartEquiv G Z.P) ((spliceFoldDartTrace (unitBlocks G σ)).pc c side)).trans
      (he.trans ((spliceFoldDartTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).pc _ side).symm))

/-- Actual surviving LP darts follow the full actual leaf map. -/
theorem unitSpliceMolIso_lp (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GardenLPLeaf (stSt G σ).G) :
    (unitSpliceMolIso Z σ hsel).d (.inr q) = .inr (unitSpliceLPLeafEquiv Z σ hsel q) := by
  apply (stSt Z.target (transportPrescription Z.iso σ)).M.od_inj
  have he : naiveDartEquiv G Z.P (.inr ((spliceFoldLeafTrace (unitBlocks G σ)).lp q)) =
      .inr ((spliceFoldLeafTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).lp
        (unitSpliceLPLeafEquiv Z σ hsel q)) := by
    apply congrArg Sum.inr
    apply Subtype.ext
    exact (unitSpliceLeafEquiv_names Z σ hsel q.1).symm
  exact (unitSpliceMolIso_surviving_dart_names Z σ hsel (.inr q)).trans
    ((congrArg (naiveDartEquiv G Z.P) ((spliceFoldDartTrace (unitBlocks G σ)).lp q)).trans
      (he.trans ((spliceFoldDartTrace (unitBlocks Z.target (transportPrescription Z.iso σ))).lp _).symm))

/-- Exact bond-momentum arguments commute with the actual full node and dart maps. -/
theorem unitSplice_bondIndex (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (z : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ))
    (x : GardenDart (stSt G σ).G) :
    bondIndex (stSt G σ).G (z ∘ unitSpliceNodeEquiv Z σ hsel) x =
      bondIndex (stSt Z.target (transportPrescription Z.iso σ)).G z ((unitSpliceMolIso Z σ hsel).d x) := by
  cases x with
  | inl c =>
    obtain ⟨c, side⟩ := c
    rw [unitSpliceMolIso_pc]
    exact congrArg z (unitSpliceNodeEquiv_branch Z σ hsel c.1)
  | inr q =>
    rw [unitSpliceMolIso_lp]
    exact congrArg z (unitSpliceNodeEquiv_leaf Z σ hsel q.1)

end WaveTurbulence.VineA
