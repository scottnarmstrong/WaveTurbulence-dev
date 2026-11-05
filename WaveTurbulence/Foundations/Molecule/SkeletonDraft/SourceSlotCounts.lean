/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourcePairPayload
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.ReconstructionDataCount

/-! # Exact branch/pair slot counts and the uniform assignment exponent -/

public section
namespace WaveTurbulence.Reg.Skeleton

theorem sourcePair_card_twice {w : ℕ} (G : Garden w) (hG : G.IsPlain) :
    2 * Fintype.card (SourcePair G) = 2 * G.order + w := by
  classical
  let E : SourcePair G × Fin 2 ≃ GLeaf G.tree := Equiv.ofBijective
    (fun z => sourcePairLeaf G hG z.1 z.2)
    ⟨sourcePairLeaf_injective G hG,sourcePairLeaf_surjective G hG⟩
  have he := Fintype.card_congr E
  rw [Fintype.card_prod,Fintype.card_fin,Comb.card_gleaf] at he
  change Fintype.card (SourcePair G) * 2 = 2 * G.order + w at he
  omega

/-- Width 2R gives precisely order+R canonical leaf-pair replacement slots. -/
theorem sourcePair_card {R : ℕ} (G : Garden (2*R)) (hG : G.IsPlain) :
    Fintype.card (SourcePair G) = G.order + R := by
  have he := sourcePair_card_twice G hG
  omega

/-- A uniform exponential assignment count at fixed source signs, with no size-composition overcount. -/
theorem reconstructionDataCount_uniform {R : ℕ} (S : Garden (2*R)) (hS : S.IsPlain)
    (m : ℕ) (hord : S.order ≤ m) :
    Nat.card {D : ReconstructionData S // D.size ≤ m} ≤ (12^6)^(m+R) := by
  have he := reconstructionDataCount_le S m
  have hb : Fintype.card (GBranch S.tree) = S.order := Comb.card_gbranch S.tree
  rw [hb,sourcePair_card S hS] at he
  apply he.trans
  rw [← pow_mul]
  apply Nat.pow_le_pow_right (by decide : 0 < 12)
  omega

end WaveTurbulence.Reg.Skeleton
