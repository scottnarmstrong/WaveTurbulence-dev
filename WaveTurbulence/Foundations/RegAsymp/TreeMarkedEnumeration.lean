/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.CoefficientEnumeration

/-! # Marked finite link enumeration for the tree coefficient expansion

DH23 Proposition 6.1, tree case: an arbitrary injective enumeration of the actual chosen
addresses identifies the active source variables without changing any SRep bound.
-/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR
open scoped Classical

/-- The actual marked indices of a selected source address set. -/
@[expose] def treeMarkedIndices {V : Type} [DecidableEq V] {n : ℕ}
    (g : Fin n → V) (Z : Finset V) : Finset (Fin n) :=
  Finset.univ.filter fun j => g j ∈ Z

/-- The remaining indices enumerate exactly the remaining source addresses. -/
theorem range_treeUnmarked {V : Type} [DecidableEq V] {n : ℕ}
    (g : Fin n → V) (S Z : Finset V) (hr : Set.range g = (S : Set V)) :
    Set.range (fun j : {j : Fin n // j ∉ treeMarkedIndices g Z} => g j) =
      (S \ Z : Finset V) := by
  ext v
  constructor
  · rintro ⟨j, rfl⟩
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact (Set.ext_iff.mp hr _).mp ⟨j.val, rfl⟩
    · simpa only [treeMarkedIndices, Finset.mem_filter, Finset.mem_univ, true_and] using j.property
  · intro hv
    obtain ⟨hs, hz⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨j, hj⟩ := (Set.ext_iff.mp hr v).mpr hs
    refine ⟨⟨j, ?_⟩, hj⟩
    simpa only [treeMarkedIndices, Finset.mem_filter, Finset.mem_univ, true_and, hj] using hz

/-- Products over marked actual indices are exactly products over marked source addresses. -/
theorem prod_treeMarked {V : Type} {M : Type*} [DecidableEq V] [CommMonoid M] {n : ℕ}
    (g : Fin n → V) (hg : Function.Injective g) (S Z : Finset V)
    (hr : Set.range g = (S : Set V)) (hZ : Z ⊆ S) (f : V → M) :
    (∏ j ∈ treeMarkedIndices g Z, f (g j)) = ∏ z ∈ Z, f z := by
  apply Finset.prod_bij (fun j _ => g j)
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro i _ j _ hij
    exact hg hij
  · intro z hz
    obtain ⟨j, hj⟩ := (Set.ext_iff.mp hr z).mpr (hZ hz)
    refine ⟨j, ?_, hj⟩
    simp only [treeMarkedIndices, Finset.mem_filter, Finset.mem_univ, true_and, hj, hz]
  · intro j _
    rfl

/-- Actual source coefficient variables can be the unmarked tree links, with unchanged constants. -/
theorem treeCoefficient_on_unmarked {V : Type} [DecidableEq V] {n : ℕ}
    {θ a b A N : ℝ} {S Z : Finset V} {F : (V → ℝ) → ℝ → ℝ → ℂ}
    (hF : MCRep θ a b A N (S \ Z : Finset V) F)
    (g : Fin n → V) (hg : Function.Injective g) (hr : Set.range g = (S : Set V)) :
    ∃ C : ({j : Fin n // j ∉ treeMarkedIndices g Z} → ℝ) → ℝ × ℝ → ℂ,
      SRep θ a b A N C ∧
      ∀ α t s, t ∈ Set.Icc (0 : ℝ) 1 → s ∈ Set.Icc (0 : ℝ) 1 →
        F α t s = ∫ lam, C (fun j => α (g j)) lam * e2 lam t s := by
  exact mcRep_on_enumeration hF _ (fun i j h => Subtype.ext (hg h))
    (range_treeUnmarked g S Z hr)

end WaveTurbulence.RegAsymp
