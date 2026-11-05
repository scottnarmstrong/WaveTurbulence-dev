/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineMaskIdentity
public import WaveTurbulence.Foundations.Molecule.VineBranchingEnds
import Mathlib.Tactic

/-! # Actual branching neighbors certified by finite template subsets -/

public section
namespace WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D]

/-- Exact finite template neighbors transfer to distinct actual subgroup
neighbors. The hypothesis is a local edge certificate on the finite label set. -/
theorem VineRealization.branching_of_image {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    {A : Finset V} (hAS : A ⊆ S) (W : Finset ℕ) (hW : W=A.image R.f)
    (hbranch : ∀ i ∈ W,∃ j ∈ W,∃ k ∈ W,
      EdgeAdj (X.expand R.k).bonds i j ∧ EdgeAdj (X.expand R.k).bonds i k ∧ j ≠ k)
    {v : V} (hv : v ∈ A) :
    ∃ u w,(Mole.induced M A).Adj v u ∧ (Mole.induced M A).Adj v w ∧ u ≠ w := by
  have hfv : R.f v ∈ W := hW.symm ▸ mem_image_of_mem R.f hv
  obtain ⟨j,hj,k,hk,hej,hek,hne⟩ := hbranch _ hfv
  rw [hW] at hj hk
  obtain ⟨u,hu,huLabel⟩ := mem_image.mp hj
  obtain ⟨w,hw,hwLabel⟩ := mem_image.mp hk
  refine ⟨u,w,R.subgroup_adj_of_edge hAS hv hu ?_,
    R.subgroup_adj_of_edge hAS hv hw ?_,?_⟩
  · simpa only [huLabel] using hej
  · simpa only [hwLabel] using hek
  · intro he
    exact hne (huLabel.symm.trans ((congrArg R.f he).trans hwLabel))

/-- The exceptional five-atom proper block in core VII has at least two
distinct neighbors at every atom, certified directly by its literal edges. -/
theorem coreVII_five_branching :
    ∀ i ∈ ({4,5,6,7,8} : Finset ℕ),∃ j ∈ ({4,5,6,7,8} : Finset ℕ),
      ∃ k ∈ ({4,5,6,7,8} : Finset ℕ),
        EdgeAdj VineType.VII.template.bonds i j ∧
        EdgeAdj VineType.VII.template.bonds i k ∧ j ≠ k := by decide

/-- The five-atom proper side block of unexpanded core VII is not a VC. -/
theorem coreVII_five_not_isVC [DecidableEq D] {M : Molecule V D}
    {S : Finset V} {a b : V} (R : VineRealization M .VII S a b)
    (hk : R.k=List.replicate VineType.VII.template.slots.length 0)
    {A : Finset V} {x y : V} (hAS : A ⊆ S)
    (himage : A.image R.f=({4,5,6,7,8} : Finset ℕ)) : ¬IsVC M A x y := by
  intro hVC
  have hcard : A.card=5 := by
    have he := congrArg Finset.card himage
    rw [card_image_of_injOn (fun _ hx _ hy he => R.injOn (hAS hx) (hAS hy) he)] at he
    exact he
  have hbranch : ∀ v ∈ A,∃ u w,(Mole.induced M A).Adj v u ∧
      (Mole.induced M A).Adj v w ∧ u ≠ w := by
    intro v hv
    apply R.branching_of_image hAS _ himage.symm _ hv
    simpa only [hk,expand_zero_rungs] using coreVII_five_branching
  exact not_isVC_five_of_branching M hcard
    (hbranch x hVC.1.2.1) (hbranch y hVC.1.2.2.1) hVC

end WaveTurbulence.Vine
