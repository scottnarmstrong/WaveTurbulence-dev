/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PairRelations

/-! # Normalization of all regular-object structure codes (DH21 Proposition 4.10)

The intermediate code grammar permits redundant terminal type-2 constructors.
Normalization enforces the audited uniqueness side conditions, preserving all
trees, orders and leaf-pair relations. This does not assume source regularity.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

mutual
/-- Normalize every nested side couple and absorb terminal type-2 constructors. -/
def normalizeCouple : RegCpl → RegCpl
  | .triv => .triv
  | .type1 c a b d => .type1 c (normalizeCouple a) (normalizeCouple b) (normalizeCouple d)
  | .type2 p m q => attachChains (normalizeChain p) (normalizeChain m) (normalizeCouple q)

/-- Normalize the side couples in a chain without changing its spine or mini-tree codes. -/
def normalizeChain : RegChain → RegChain
  | .nil => .nil
  | .pair m r g i s =>
    .pair m (normalizeCouple r) (normalizeCouple g) (normalizeChain i) (normalizeChain s)
end

mutual
/-- Every couple code has a well-formed normalization. -/
theorem normalizeCouple_wf (Q : RegCpl) : (normalizeCouple Q).wf = true := by
  cases Q with
  | triv => rfl
  | type1 c a b d =>
    simp only [normalizeCouple, RegCpl.wf, normalizeCouple_wf a,
      normalizeCouple_wf b, normalizeCouple_wf d, Bool.and_self]
  | type2 p m q =>
    exact attachChains_wf _ _ _ (normalizeChain_wf p)
      (normalizeChain_wf m) (normalizeCouple_wf q)
termination_by structural Q

/-- Every chain code has a well-formed normalization. -/
theorem normalizeChain_wf (X : RegChain) : (normalizeChain X).wf = true := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    simp only [normalizeChain, RegChain.wf, normalizeCouple_wf r, normalizeCouple_wf g,
      normalizeChain_wf i, normalizeChain_wf s, Bool.and_self]
termination_by structural X
end

/-- Normalizing side couples leaves the source chain's lone path unchanged. -/
theorem normalizeChain_lonePath (X : RegChain) :
    (normalizeChain X).lonePath = X.lonePath := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    simp only [normalizeChain, RegChain.lonePath, normalizeChain_lonePath i, normalizeChain_lonePath s]
termination_by structural X

mutual
/-- Normalization retains every oriented couple leaf pair. -/
theorem mem_normalizeCouple_pairsAt {w : ℕ} (Q : RegCpl) (a b : Fin w × Path)
    (z : (Fin w × Path) × (Fin w × Path)) :
    z ∈ (normalizeCouple Q).pairsAt a b ↔ z ∈ Q.pairsAt a b := by
  cases Q with
  | triv => rfl
  | type1 c r g d =>
    simp only [normalizeCouple, RegCpl.pairsAt, List.mem_append,
      mem_normalizeCouple_pairsAt r, mem_normalizeCouple_pairsAt g, mem_normalizeCouple_pairsAt d]
  | type2 p m q =>
    simp only [normalizeCouple, mem_attachChains_pairsAt, normalizeChain_lonePath,
      mem_normalizeChain_pairsAt p, mem_normalizeChain_pairsAt m,
      mem_normalizeCouple_pairsAt q, RegCpl.pairsAt, List.mem_append, or_assoc]
termination_by structural Q

/-- Normalization retains every oriented chain leaf pair. -/
theorem mem_normalizeChain_pairsAt {w : ℕ} (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (z : (Fin w × Path) × (Fin w × Path)) :
    z ∈ (normalizeChain X).pairsAt ζ a ↔ z ∈ X.pairsAt ζ a := by
  cases X with
  | nil => rfl
  | pair m r g i s =>
    by_cases hr : slotSign ζ m.red.1 = 1 <;>
      by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp only [normalizeChain, RegChain.pairsAt, normalizeChain_lonePath,
        hr, hg, ite_true, ite_false, List.mem_append, mem_normalizeCouple_pairsAt r,
        mem_normalizeCouple_pairsAt g, mem_normalizeChain_pairsAt i, mem_normalizeChain_pairsAt s]
termination_by structural X
end

end WaveTurbulence.Reg
