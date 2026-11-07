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

/-- The complete node map fixes each external root's tree index and empty path. -/
theorem unitSpliceNodeEquiv_root_node (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (j : Fin w) :
    unitSpliceNodeEquiv Z σ hsel (GNode.root (stSt G σ).G.tree j) =
      GNode.root (stSt Z.target (transportPrescription Z.iso σ)).G.tree j := by
  apply Subtype.ext
  exact Prod.ext (unitSpliceNodeEquiv_index Z σ hsel _)
    ((unitSpliceNodeEquiv_root Z σ hsel _).mpr rfl)

/-- The actual full leaf map preserves the source marked-flower predicate. -/
theorem unitSpliceLeafEquiv_flower_iff (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (q : GLeaf (stSt G σ).G.tree) :
    (stSt Z.target (transportPrescription Z.iso σ)).G.IsFlower (unitSpliceLeafEquiv Z σ hsel q) ↔
      (stSt G σ).G.IsFlower q := by
  change _ = some MarkTag.equal ↔ _ = some MarkTag.equal
  rw [unitSpliceLeafEquiv_mark]

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
      ∀ q, (stSt G σ).G.IsFlower q → (κ ∘ unitSpliceNodeEquiv Z σ hsel) q.toNode = flower) := by
  constructor
  · rintro ⟨hd, hr, hf⟩
    refine ⟨(unitSplice_isDecoration_iff Z σ hsel κ).mp hd, ?_, ?_⟩
    · intro j
      exact (congrArg κ (unitSpliceNodeEquiv_root_node Z σ hsel j)).trans (hr j)
    · intro q hq
      exact (congrArg κ (unitSpliceNodeEquiv_leaf Z σ hsel q)).trans
        (hf _ ((unitSpliceLeafEquiv_flower_iff Z σ hsel q).mpr hq))
  · rintro ⟨hd, hr, hf⟩
    refine ⟨(unitSplice_isDecoration_iff Z σ hsel κ).mpr hd, ?_, ?_⟩
    · intro j
      exact (congrArg κ (unitSpliceNodeEquiv_root_node Z σ hsel j)).symm.trans (hr j)
    · intro q' hq'
      obtain ⟨q, rfl⟩ := (unitSpliceLeafEquiv Z σ hsel).surjective q'
      exact (congrArg κ (unitSpliceNodeEquiv_leaf Z σ hsel q)).symm.trans
        (hf q ((unitSpliceLeafEquiv_flower_iff Z σ hsel q).mp hq'))

/-- The exact general integer-decoration carrier of the kernel is bijective. -/
noncomputable def unitSpliceGenDecorationEquiv (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (d : ℕ)
    (roots : Fin w → (Fin d → ℤ)) (flower : Fin d → ℤ) :
    GenDecoration (stSt G σ).G d roots flower ≃
      GenDecoration (stSt Z.target (transportPrescription Z.iso σ)).G d roots flower := by
  let E := unitSpliceNodeEquiv Z σ hsel
  let e := Equiv.arrowCongr E (Equiv.refl (Fin d → ℤ))
  refine e.subtypeEquiv (fun κ => ?_)
  have h := unitSplice_decoration_constraints_iff Z σ hsel (e κ) roots flower
  have he : (e κ) ∘ E = κ := by
    funext n
    change κ (E.symm (E n)) = κ n
    exact congrArg κ (E.symm_apply_apply n)
  rw [he] at h
  exact h.symm

end WaveTurbulence.VineA
