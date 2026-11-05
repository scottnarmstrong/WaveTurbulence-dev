/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineLocalDartObjects
public import WaveTurbulence.Foundations.Molecule.VineChainCounts
import Mathlib.Tactic

/-! # Local dart identifications preserve actual chain decompositions -/

public section
namespace WaveTurbulence.Vine
variable {V D E : Type*} [DecidableEq V] [Fintype D] [Fintype E]
    {M : Molecule V D} {N : Molecule V E} {A : Finset V}
namespace LocalDartEmbedding
variable (F : LocalDartEmbedding M N A)

include F in
/-- Every identified actual chain is also a chain in the original molecule. -/
theorem chain_to {S : Finset V} {a b : V} {n : ℕ} (h : Chain N S a b n) :
    S ⊆ A → Chain M S a b n := by
  induction h with
  | single h =>
    intro hSA
    obtain ⟨X,hX⟩ := h
    exact Chain.single ⟨X,(F.isVine_iff X _ hSA _ _).mp hX⟩
  | @append S T a b c n hS hT hi hne ih =>
    intro hUA
    obtain ⟨X,hX⟩ := hT
    exact Chain.append (ih (Finset.subset_union_left.trans hUA))
      ⟨X,(F.isVine_iff X _ (Finset.subset_union_right.trans hUA) _ _).mp hX⟩ hi hne

include F in
/-- Every original chain lifts through an identification of all its internal darts. -/
theorem chain_of {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) :
    S ⊆ A → Chain N S a b n := by
  induction h with
  | single h =>
    intro hSA
    obtain ⟨X,hX⟩ := h
    exact Chain.single ⟨X,(F.isVine_iff X _ hSA _ _).mpr hX⟩
  | @append S T a b c n hS hT hi hne ih =>
    intro hUA
    obtain ⟨X,hX⟩ := hT
    exact Chain.append (ih (Finset.subset_union_left.trans hUA))
      ⟨X,(F.isVine_iff X _ (Finset.subset_union_right.trans hUA) _ _).mpr hX⟩ hi hne

include F in
/-- Both source chain existence and the exact number of ingredients are preserved. -/
theorem chain_iff (S : Finset V) (hSA : S ⊆ A) (a b : V) (n : ℕ) :
    Chain N S a b n ↔ Chain M S a b n :=
  ⟨fun h => F.chain_to h hSA,fun h => F.chain_of h hSA⟩

include F in
/-- The source VC predicate, including the actual block premise, is preserved. -/
theorem isVC_iff (S : Finset V) (hSA : S ⊆ A) (a b : V) : IsVC N S a b ↔ IsVC M S a b := by
  simp only [IsVC,F.isBlock_iff S hSA a b,F.chain_iff S hSA a b]

include F in
/-- A chain of doubled bonds is preserved in the original molecule. -/
theorem doubleChain_to {S : Finset V} {a b : V} {n : ℕ} (h : DoubleChain N S a b n) :
    S ⊆ A → DoubleChain M S a b n := by
  induction h with
  | single h => intro hSA; exact DoubleChain.single ((F.isVine_iff .I _ hSA _ _).mp h)
  | @append S T a b c n hS hT hi hne ih =>
    intro hUA
    exact DoubleChain.append (ih (Finset.subset_union_left.trans hUA))
      ((F.isVine_iff .I _ (Finset.subset_union_right.trans hUA) _ _).mp hT) hi hne

include F in
/-- Every original double chain lifts to the identified local graph. -/
theorem doubleChain_of {S : Finset V} {a b : V} {n : ℕ} (h : DoubleChain M S a b n) :
    S ⊆ A → DoubleChain N S a b n := by
  induction h with
  | single h => intro hSA; exact DoubleChain.single ((F.isVine_iff .I _ hSA _ _).mpr h)
  | @append S T a b c n hS hT hi hne ih =>
    intro hUA
    exact DoubleChain.append (ih (Finset.subset_union_left.trans hUA))
      ((F.isVine_iff .I _ (Finset.subset_union_right.trans hUA) _ _).mpr hT) hi hne

end LocalDartEmbedding
end WaveTurbulence.Vine
