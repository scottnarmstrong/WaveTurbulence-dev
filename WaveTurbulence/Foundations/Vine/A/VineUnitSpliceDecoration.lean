/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceChildren
/-! Actual integer or vector decorations transport through the full
selected-splice node equivalence, including paired boundary leaves. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- A permutation fixing the middle slot preserves the signed ternary sum. -/
theorem signed_ternary_sum_perm {V : Type*} [AddCommGroup V] (e : Fin 3 ≃ Fin 3)
    (he : e 1 = 1) (f : Fin 3 → V) :
    f (e 0) - f (e 1) + f (e 2) = f 0 - f 1 + f 2 := by
  have h0 : e 0 ≠ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (e.injective (h.trans he.symm))
  have h2 : e 2 ≠ 1 := fun h => (by decide : (2 : Fin 3) ≠ 1) (e.injective (h.trans he.symm))
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h := e.sum_comp (fun i => if i = 1 then -f i else f i)
  simp only [Fin.sum_univ_three, he, h0, h2, h01, h21, ↓reduceIte] at h
  simpa only [sub_eq_add_neg, he] using h

/-- The actual decoration constraints are preserved in both directions. -/
theorem unitSplice_isDecoration_iff {V : Type*} [AddCommGroup V]
    (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → V) :
    IsDecoration (stSt Z.target (transportPrescription Z.iso σ)).G κ ↔
      IsDecoration (stSt G σ).G (κ ∘ unitSpliceNodeEquiv Z σ hsel) := by
  let F := unitSpliceMolIso Z σ hsel
  let E := unitSpliceLeafEquiv Z σ hsel
  have hsum (b : GBranch (stSt G σ).G.tree) :=
    signed_ternary_sum_perm (unitSpliceChildEquiv Z σ hsel b) (unitSpliceChildSlot_middle Z σ hsel b)
      (fun i => κ ((F.e b).child i))
  constructor
  · rintro ⟨hb, hl⟩
    constructor
    · intro b
      change κ (unitSpliceNodeEquiv Z σ hsel b.toNode) =
        κ (unitSpliceNodeEquiv Z σ hsel (b.child 0)) - κ (unitSpliceNodeEquiv Z σ hsel (b.child 1)) +
          κ (unitSpliceNodeEquiv Z σ hsel (b.child 2))
      rw [unitSpliceNodeEquiv_branch, unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_child]
      exact (hb (F.e b)).trans (hsum b).symm
    · intro q
      change κ (unitSpliceNodeEquiv Z σ hsel q.toNode) = κ (unitSpliceNodeEquiv Z σ hsel ((stSt G σ).G.pair q).toNode)
      rw [unitSpliceNodeEquiv_leaf, unitSpliceNodeEquiv_leaf, unitSpliceLeafEquiv_pair]
      exact hl (E q)
  · rintro ⟨hb, hl⟩
    constructor
    · intro b'
      obtain ⟨b, rfl⟩ := F.e.surjective b'
      have h := hb b
      change κ (unitSpliceNodeEquiv Z σ hsel b.toNode) =
        κ (unitSpliceNodeEquiv Z σ hsel (b.child 0)) - κ (unitSpliceNodeEquiv Z σ hsel (b.child 1)) +
          κ (unitSpliceNodeEquiv Z σ hsel (b.child 2)) at h
      rw [unitSpliceNodeEquiv_branch, unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_child] at h
      exact h.trans (hsum b)
    · intro q'
      obtain ⟨q, rfl⟩ := E.surjective q'
      have h := hl q
      change κ (unitSpliceNodeEquiv Z σ hsel q.toNode) = κ (unitSpliceNodeEquiv Z σ hsel ((stSt G σ).G.pair q).toNode) at h
      rw [unitSpliceNodeEquiv_leaf, unitSpliceNodeEquiv_leaf, unitSpliceLeafEquiv_pair] at h
      exact h

end WaveTurbulence.VineA
