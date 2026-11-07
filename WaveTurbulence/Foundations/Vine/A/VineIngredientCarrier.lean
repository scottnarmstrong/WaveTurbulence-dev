/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitIngredients
public import WaveTurbulence.Foundations.Molecule.VineLowDegreeJoints
/-! The actual ChainIngredient carrier of the chosen units is exactly the
atom-set carrier of V0(sigma). This strengthens the earlier unit-cover result. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Vine
variable {w : ℕ} {G : Garden w}

/-- A chain on an actual block uses exactly that block's two unordered joints. -/
theorem chain_block_joints {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V} {a b x y : V} {n : ℕ}
    (hB : M.IsBlock S a b) (hc : Chain M S x y n) : ({x, y} : Finset V) = {a, b} := by
  have hd := Mole.block_joint_degrees M hB
  exact joints_eq_of_two_low_degrees M (subset_refl _) hB.2.1 hB.2.2.1
    hB.2.2.2.1 (chain_joints_ne hc) (by omega) (by omega) (chain_interior_degree M hM hc)

/-- The chosen units' actual ingredient carrier equals the selected source carrier. -/
theorem mem_unitIngredients_iff {σ : Prescription G} {T : Finset (GBranch G.tree)} :
    T ∈ unitIngredients G σ ↔ ∃ c ∈ vinesV0 G σ, c.atoms = T := by
  have hM := Mole.garden_isMolecule G
  constructor
  · rintro ⟨u, hu, x, y, n, p, q, hi⟩
    obtain ⟨L, hs, hsel⟩ := unitBlocks_selected_spine hu
    have hj := chain_block_joints hM u.isBlock (chainIngredient_spec hi).1
    have hB := Mole.block_transport_joints G.molecule hj u.isBlock
    obtain ⟨r, s, hm | hm⟩ := isIngredient_vc hM u.isBlock hs (Or.inl ⟨x, y, n, p, q, hB, hi⟩)
    · exact hsel (T, r, s) hm
    · exact hsel (T, s, r) hm
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨_, u, hu, hcu⟩ := (vinesV0_iff_unit_cover G σ c).mp hc
    obtain ⟨L, hs, hsel⟩ := unitBlocks_selected_spine hu
    obtain ⟨T, p, q, hm, hsub⟩ := hs.vine_in_member hM u.isBlock c.isVine.choose_spec hcu
    obtain ⟨d, hd, hdat⟩ := hsel (T, p, q) hm
    have he : c = d := by
      by_contra hne
      have hcd : c.atoms ⊆ d.atoms := hdat.symm ▸ hsub
      have h := vinesV_separated hc.1 hd.1 hne c.upper c.upper_mem (hcd c.upper_mem)
        c.lower c.lower_mem (hcd c.lower_mem)
      exact c.isVine.choose_spec.1.2.2.2.1 h
    have hat : c.atoms = T := he ▸ hdat
    refine ⟨u, hu, u.upper, u.lower, L.length, p, q, ?_⟩
    rw [hat]
    exact hs.ingredient_of_mem hm

end WaveTurbulence.VineA
