/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.MarkedGardenGraft
public import WaveTurbulence.Foundations.XChain.GraftBranchConsistency
/-! Exact decoration constraints for arbitrary marked garden grafts. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem markedGardenGraft_pair_lower {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (ℓ : GLeaf (low B).tree) :
    (markedGardenGraft sig top P low hsig).pair (lowerLeafEmbedding top P low B ℓ) =
      lowerLeafEmbedding top P low B ((low B).pair ℓ) := by
  have he := congrArg (fun z : Σ B : P.parts, GLeaf (low B).tree =>
    (gardenLeafEquiv top P low).symm (blockPair low z))
    ((gardenLeafEquiv top P low).apply_symm_apply ⟨B, ℓ⟩)
  exact he

theorem markedGardenGraft_mark_lower {w : ℕ} (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (B : P.parts) (ℓ : GLeaf (low B).tree) :
    (markedGardenGraft sig top P low hsig).mark (lowerLeafEmbedding top P low B ℓ) =
      (low B).mark ℓ := by
  exact congrArg (fun z : Σ B : P.parts, GLeaf (low B).tree => (low z.1).mark z.2)
    ((gardenLeafEquiv top P low).apply_symm_apply ⟨B, ℓ⟩)

theorem pairing_consistent_graft_iff {V : Type*} [AddCommGroup V] {w : ℕ}
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (κ : GNode (graftForest top (blockGraftTrees top P low)) → V) :
    (∀ ℓ, κ ℓ.toNode = κ ((markedGardenGraft sig top P low hsig).pair ℓ).toNode) ↔
    ∀ B (ℓ : GLeaf (low B).tree),
      κ (lowerNodeEmbedding top P low B ℓ.toNode) =
        κ (lowerNodeEmbedding top P low B ((low B).pair ℓ).toNode) := by
  have hleft (B : P.parts) (ℓ : GLeaf (low B).tree) :=
    congrArg κ (gardenLeaf_toNode_lower top P low B ℓ)
  have hright (B : P.parts) (ℓ : GLeaf (low B).tree) :=
    (congrArg (fun l => κ l.toNode) (markedGardenGraft_pair_lower sig top P low hsig B ℓ)).trans
      (hleft B ((low B).pair ℓ))
  constructor
  · intro h B ℓ
    exact (hleft B ℓ).symm.trans ((h _).trans (hright B ℓ))
  · intro h ℓ
    obtain ⟨⟨B, l⟩, rfl⟩ := (gardenLeafEquiv top P low).symm.surjective ℓ
    exact (hleft B l).trans ((h B l).trans (hright B l).symm)

theorem isDecoration_markedGardenGraft_iff {V : Type*} [AddCommGroup V] {w : ℕ}
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (κ : GNode (graftForest top (blockGraftTrees top P low)) → V) :
    IsDecoration (markedGardenGraft sig top P low hsig) κ ↔
      IsBranchConsistent (fun a => κ (topNodeEmbedding top P low a)) ∧
      ∀ B, IsDecoration (low B) (fun a => κ (lowerNodeEmbedding top P low B a)) := by
  constructor
  · rintro ⟨hb, hp⟩
    obtain ⟨ht, hl⟩ := (isBranchConsistent_graft_iff top P low κ).mp hb
    have hp' := (pairing_consistent_graft_iff sig top P low hsig κ).mp hp
    exact ⟨ht, fun B => ⟨hl B, hp' B⟩⟩
  · rintro ⟨ht, hl⟩
    exact ⟨(isBranchConsistent_graft_iff top P low κ).mpr ⟨ht, fun B => (hl B).1⟩,
      (pairing_consistent_graft_iff sig top P low hsig κ).mpr (fun B => (hl B).2)⟩

end WaveTurbulence.Induct
