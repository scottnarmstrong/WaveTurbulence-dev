/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.InsertionSigns

/-! # Identifying the two exceptional leaves in the concrete unit twist

TARGET twistexplain: precisely u23 and u0 change sign as leaves.
-/

public section
namespace WaveTurbulence.Twist
open TTree
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Decompose the original actual leaves into common-forest and lower-crown pieces. -/
@[expose] noncomputable def coreLeafPiece : GLeaf G.tree ≃
    InsertionLeafPiece (commonForest G P.lower) (collapsedRoot G P.lower) (lowerCrown G P.lower) :=
  (forestLeafCast (restore_commonForest G P.lower).symm).trans
    (insertionLeafEquiv (commonForest G P.lower) (collapsedRoot G P.lower) (lowerCrown G P.lower)).symm

/-- The retained leaf as an actual local lower-crown leaf. -/
@[expose] def keptLocalLeaf : ↥(lowerCrown G P.lower).leaves := ⟨[P.keep],by
  have hs := (Comb.subtree_leaves_iff (lowerCrown_retained_leaf G P) []).mp
    (Finset.mem_singleton_self [])
  simpa only [List.append_nil] using hs⟩

/-- The two insertion holes are distinct actual common-forest leaves. -/
theorem pairedHole_ne_root : pairedHole G P ≠ collapsedRoot G P.lower := by
  intro he
  have hv := congrArg (fun l : GLeaf (commonForest G P.lower) => l.1) he
  have hn : (G.pair P.retained).toNode = P.lower.toNode := Subtype.ext hv
  exact Mole.branch_toNode_ne_leaf P.lower (G.pair P.retained) hn.symm

/-- u0 on the common outside leaf carrier. -/
@[expose] def pairedOutsideLeaf : {l : GLeaf (commonForest G P.lower) // l ≠ collapsedRoot G P.lower} :=
  ⟨pairedHole G P,pairedHole_ne_root G P⟩

/-- The retained actual leaf corresponds to the local singleton keep address. -/
theorem coreLeafPiece_retained : coreLeafPiece G P P.retained = .inr (keptLocalLeaf G P) := by
  apply (coreLeafPiece G P).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  change P.retained.1 = (P.lower.1.1,P.lower.1.2 ++ [P.keep])
  exact congrArg (fun n : GNode G.tree => n.1) P.child

/-- Its paired actual leaf corresponds to the distinguished outside leaf u0. -/
theorem coreLeafPiece_paired : coreLeafPiece G P (G.pair P.retained) = .inl (pairedOutsideLeaf G P) := by
  apply (coreLeafPiece G P).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  rfl

/-- Pair-invariant sign multiplier for the two exceptional leaves. -/
@[expose] noncomputable def coreLeafMultiplier (l : GLeaf G.tree) : ℤˣ :=
  if l = P.retained ∨ l = G.pair P.retained then -1 else 1

/-- The multiplier is constant on every actual paired pair. -/
theorem coreLeafMultiplier_pair (l : GLeaf G.tree) :
    coreLeafMultiplier G P (G.pair l) = coreLeafMultiplier G P l := by
  classical
  have h1 : G.pair l = P.retained ↔ l = G.pair P.retained := by
    constructor
    · intro he
      have hh := congrArg G.pair he
      simpa only [G.pair_pair] using hh
    · intro he
      rw [he,G.pair_pair]
  have h2 : G.pair l = G.pair P.retained ↔ l = P.retained :=
    ⟨fun he => by have hh := congrArg G.pair he; simpa only [G.pair_pair] using hh,
      fun he => congrArg G.pair he⟩
  simp only [coreLeafMultiplier,h1,h2,or_comm]

end WaveTurbulence.Twist
