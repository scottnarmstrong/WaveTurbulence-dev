/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDecoration
/-! Actual general decorations, including root values and marked flower
values, correspond bijectively across selected simultaneous splices. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `unitSpliceNodeEquiv_root_node`). -/
theorem unitSpliceNodeEquiv_root_nodeMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (j : Fin w) :
    unitSpliceNodeEquivMk Z σ hT hsel (GNode.root (stSt G σ Mk).G.tree j) =
      GNode.root (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree j := by
  apply Subtype.ext
  exact Prod.ext (unitSpliceNodeEquiv_indexMk Z σ hT hsel _)
    ((unitSpliceNodeEquiv_rootMk Z σ hT hsel _).mpr rfl)

/-- The complete node map fixes each external root's tree index and empty path. -/
theorem unitSpliceNodeEquiv_root_node (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (j : Fin w) :
    unitSpliceNodeEquiv Z σ hsel (GNode.root (stSt G σ).G.tree j) =
      GNode.root (stSt Z.target (transportPrescription Z.iso σ)).G.tree j :=
  unitSpliceNodeEquiv_root_nodeMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel j

/-- B1b-2 (Mk-general form of `unitSpliceLeafEquiv_flower_iff`). -/
theorem unitSpliceLeafEquiv_flower_iffMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (q : GLeaf (stSt G σ Mk).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').G.IsFlower (unitSpliceLeafEquivMk Z σ hT hsel q) ↔
      (stSt G σ Mk).G.IsFlower q := by
  change _ = some MarkTag.equal ↔ _ = some MarkTag.equal
  rw [unitSpliceLeafEquiv_markMk]

/-- The actual full leaf map preserves the source marked-flower predicate. -/
theorem unitSpliceLeafEquiv_flower_iff (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.IsFlower (unitSpliceLeafEquiv Z σ hsel q) ↔
      (stSt G σ).G.IsFlower q := unitSpliceLeafEquiv_flower_iffMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel q

/-- B1b-2 (Mk-general form of `unitSplice_decoration_constraints_iff`). -/
theorem unitSplice_decoration_constraints_iffMk {V : Type*} [AddCommGroup V]
    (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → V)
    (roots : Fin w → V) (flower : V) :
    (IsDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G κ ∧
      (∀ j, κ (GNode.root (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree j) = roots j) ∧
      ∀ q, (stSt Z.target (transportPrescription Z.iso σ) Mk').G.IsFlower q → κ q.toNode = flower) ↔
    (IsDecoration (stSt G σ Mk).G (κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) ∧
      (∀ j, (κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) (GNode.root (stSt G σ Mk).G.tree j) = roots j) ∧
      ∀ q, (stSt G σ Mk).G.IsFlower q → (κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) q.toNode = flower) := by
  constructor
  · rintro ⟨hd, hr, hf⟩
    refine ⟨(unitSplice_isDecoration_iffMk Z σ hT hsel κ).mp hd, ?_, ?_⟩
    · intro j
      exact (congrArg κ (unitSpliceNodeEquiv_root_nodeMk Z σ hT hsel j)).trans (hr j)
    · intro q hq
      exact (congrArg κ (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).trans
        (hf _ ((unitSpliceLeafEquiv_flower_iffMk Z σ hT hsel q).mpr hq))
  · rintro ⟨hd, hr, hf⟩
    refine ⟨(unitSplice_isDecoration_iffMk Z σ hT hsel κ).mpr hd, ?_, ?_⟩
    · intro j
      exact (congrArg κ (unitSpliceNodeEquiv_root_nodeMk Z σ hT hsel j)).symm.trans (hr j)
    · intro q' hq'
      obtain ⟨q, rfl⟩ := (unitSpliceLeafEquivMk Z σ hT hsel).surjective q'
      exact (congrArg κ (unitSpliceNodeEquiv_leafMk Z σ hT hsel q)).symm.trans
        (hf q ((unitSpliceLeafEquiv_flower_iffMk Z σ hT hsel q).mp hq'))

/-- The full decoration, root and flower constraints transport together. -/
theorem unitSplice_decoration_constraints_iff {V : Type*} [AddCommGroup V]
    (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → V)
    (roots : Fin w → V) (flower : V) :
    (IsDecoration (stSt Z.target (transportPrescription Z.iso σ)).G κ ∧
      (∀ j, κ (GNode.root (stSt Z.target (transportPrescription Z.iso σ)).G.tree j) = roots j) ∧
      ∀ q, (stSt Z.target (transportPrescription Z.iso σ)).G.IsFlower q → κ q.toNode = flower) ↔
    (IsDecoration (stSt G σ).G (κ ∘ unitSpliceNodeEquiv Z σ hsel) ∧
      (∀ j, (κ ∘ unitSpliceNodeEquiv Z σ hsel) (GNode.root (stSt G σ).G.tree j) = roots j) ∧
      ∀ q, (stSt G σ).G.IsFlower q → (κ ∘ unitSpliceNodeEquiv Z σ hsel) q.toNode = flower) :=
  unitSplice_decoration_constraints_iffMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel κ roots flower

/-- B1b-2 (Mk-general form of `unitSpliceGenDecorationEquiv`). -/
noncomputable def unitSpliceGenDecorationEquivMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (d : ℕ)
    (roots : Fin w → (Fin d → ℤ)) (flower : Fin d → ℤ) :
    GenDecoration (stSt G σ Mk).G d roots flower ≃
      GenDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G d roots flower := by
  let E := unitSpliceNodeEquivMk Z σ hT hsel
  let e := Equiv.arrowCongr E (Equiv.refl (Fin d → ℤ))
  refine e.subtypeEquiv (fun κ => ?_)
  have h := unitSplice_decoration_constraints_iffMk Z σ hT hsel (e κ) roots flower
  have he : (e κ) ∘ E = κ := by
    funext n
    change κ (E.symm (E n)) = κ n
    exact congrArg κ (E.symm_apply_apply n)
  rw [he] at h
  exact h.symm

/-- The exact general integer-decoration carrier of the kernel is bijective. -/
noncomputable def unitSpliceGenDecorationEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (d : ℕ)
    (roots : Fin w → (Fin d → ℤ)) (flower : Fin d → ℤ) :
    GenDecoration (stSt G σ).G d roots flower ≃
      GenDecoration (stSt Z.target (transportPrescription Z.iso σ)).G d roots flower :=
  unitSpliceGenDecorationEquivMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel d roots flower

end WaveTurbulence.VineA
