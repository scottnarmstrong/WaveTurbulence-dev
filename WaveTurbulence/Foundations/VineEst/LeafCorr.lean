/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.VineEst.LeafNative

/-! # The ordinary-leaf correspondence of one LF construction (LFTWIST-LEAFMAP, step 2)

For `h : LFConstruction s ε` only the tree at `s.placement.lower` and the couple at `s.exceptional`
are replaced. A leaf of the source garden in any other native slot corresponds to the leaf with the
same relative coordinates in the image slot of the output garden. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LFTwist
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree Links
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
  (h : LFConstruction s ε)

/-- Same relative coordinates in the image slot. -/
@[expose] def LFConstruction.OrdCorr (x : GLeaf (s.data.forest s.plain)) (y : GLeaf (h.data.forest (s.chosen_plain ε))) :
    Prop :=
  (∃ q : SourcePair s.skeleton, q ≠ s.exceptional ∧ ∃ (ℓ : NativeLeaf s.data (.inl q))
      (ℓ' : NativeLeaf h.data (.inl (s.pairs ε q))), ℓ.1 = ℓ'.1 ∧
      nativeLeafAt s.data s.plain (.inl q) ℓ = x ∧
      nativeLeafAt h.data (s.chosen_plain ε) (.inl (s.pairs ε q)) ℓ' = y) ∨
  (∃ b : GBranch s.skeleton.tree, b ≠ s.placement.lower ∧ ∃ (ℓ : NativeLeaf s.data (.inr b))
      (ℓ' : NativeLeaf h.data (.inr (s.branches ε b))), ℓ.1.1 = ℓ'.1.1 ∧
      nativeLeafAt s.data s.plain (.inr b) ℓ = x ∧
      nativeLeafAt h.data (s.chosen_plain ε) (.inr (s.branches ε b)) ℓ' = y)

theorem LFConstruction.coupleTransport (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional)
    (ℓ : NativeLeaf s.data (.inl q)) :
    ∃ ℓ' : NativeLeaf h.data (.inl (s.pairs ε q)), ℓ.1 = ℓ'.1 := by
  have hm := ℓ.2
  have he := h.couple_other q hq
  refine ⟨⟨ℓ.1, ?_⟩, rfl⟩
  rw [he]
  exact hm


theorem LFConstruction.chainTransport (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower)
    (ℓ : NativeLeaf s.data (.inr b)) :
    ∃ ℓ' : NativeLeaf h.data (.inr (s.branches ε b)), ℓ.1.1 = ℓ'.1.1 := by
  have e1 := h.tree_other b hb
  have e2 := s.ordinary_branch_sign ε b hb
  obtain ⟨⟨a, ha⟩, hl⟩ := ℓ
  refine ⟨⟨⟨a, ?_⟩, ?_⟩, rfl⟩
  · rw [e1, e2]; exact ha
  · exact fun h' => hl (h'.trans (congrArg RegChain.lonePath e1))

end WaveTurbulence.LFTwist
