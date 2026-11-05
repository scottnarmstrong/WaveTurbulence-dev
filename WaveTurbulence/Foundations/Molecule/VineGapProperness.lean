/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
public import WaveTurbulence.Foundations.Molecule.VineLatticeGaps
import Mathlib.Tactic

/-! # SG subsets cannot equal an LG or ZG outer block -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The gap kind of a decorated block is independent of the order and
choice of its specified joints. -/
theorem same_block_gapKind_eq (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b x y : V} (hB : M.IsBlock S a b) (hC : M.IsBlock S x y)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r)
    (hr' : M.IsBlockGap L w κ S x r') :
    Molecule.gapKind L γ η r=Molecule.gapKind L γ η r' := by
  have hx := block_degree_two_joint M hB hC.2.1 (Mole.block_joint_degrees M hC).1
  rcases hx with rfl | rfl
  · have he := blockGap_unique M hB hr hr'
    rw [he]
  · exact gapKind_eq_of_norm_eq L γ η (block_gap_norm_eq M hM hB L w c κ hκ hc hr hr')

/-- TARGET subsetvc: different gap kinds force a nested SG block to be a
proper subset of an LG or ZG outer block. -/
theorem SG_block_ne_outer (M : Molecule V D) (hM : M.IsMolecule)
    {A S : Finset V} {a b x y : V} (hB : M.IsBlock S a b) (hC : M.IsBlock A x y)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ S a r)
    (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) : A ≠ S := by
  intro he
  subst A
  have hk := same_block_gapKind_eq M hM hB hC L γ η w c κ hκ hc hr hr'
  rw [hsmall] at hk
  rcases houter with h | h <;> rw [h] at hk <;> cases hk

end WaveTurbulence.Vine
