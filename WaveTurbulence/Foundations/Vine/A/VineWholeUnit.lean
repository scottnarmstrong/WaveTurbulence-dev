/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineChainNoCN
public import WaveTurbulence.Foundations.Vine.A.VineUnitChain
/-! A whole-group unit has a nonroot VC group. Soundness at the upper
joint excludes the top-ingredient omission in a root VC. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- Every CL ingredient containing the upper joint of a CL chain is its top ingredient. -/
theorem containing_upper_top {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hs : Spine G.molecule L S a b) (hB : G.molecule.IsBlock S a b)
    (hCL : CLParentPattern G S a b) {c : CLVine G}
    (hi : IsIngredient G.molecule S c.atoms) (ha : a ∈ c.atoms) : IsTopIngredient S c := by
  have hM := garden_isMolecule G
  have hn := spine_noCN hs hB (Or.inl hCL)
  have hcl : ∀ T p q, (T, p, q) ∈ L → CLParentPattern G T p q ∨ CLParentPattern G T q p := by
    intro T p q hm
    rcases vine_cl_or_cn (hs.mem_vine hm).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn _ hm h).elim
  obtain ⟨h1, _, h3⟩ := hs.cl_aligned hM hcl hB hCL.1
  have joints (d : CLVine G) (hd : IsIngredient G.molecule S d.atoms) :
      ∃ q, (d.atoms, d.upper, q) ∈ L := by
    obtain ⟨p, q, hm | hm⟩ := isIngredient_vc hM hB hs hd
    · have hp := (h1 _ _ _ hm).1
      have e : d.upper = p := clvine_upper_eq (c' := ⟨d.atoms, p, q, (hs.mem_vine hm).1, hp.1, hp.2⟩) rfl
      exact ⟨q, e.symm ▸ hm⟩
    · have hp := (h1 _ _ _ hm).1
      have e : d.upper = q := clvine_upper_eq (c' := ⟨d.atoms, q, p, (hs.mem_vine hm).1, hp.1, hp.2⟩) rfl
      exact ⟨p, e.symm ▸ hm⟩
  obtain ⟨q, hm⟩ := joints c hi
  have hu : c.upper = a := (h1 _ _ _ hm).2.2 ha
  intro c' hi' hne
  obtain ⟨q', hm'⟩ := joints c' hi'
  have hdesc := (h1 _ _ _ hm').2.1
  have hne' : a ≠ c'.upper := by
    intro he
    have hm0 : (c.atoms, a, q) ∈ L := hu ▸ hm
    have hm1 : (c'.atoms, a, q') ∈ L := he.symm ▸ hm'
    exact hne (h3 _ _ _ _ hm1 hm0)
  rw [hu]
  exact ⟨hne', hdesc⟩

/-- An actual whole-group unit is not a root VC. -/
theorem whole_unit_nonroot {S : Finset (GBranch G.tree)} (U : GroupUnits G S)
    (hS : S ∈ maximalGroups G.molecule) (hskip : U.skip = none)
    {u : CLBlock G} (hu : u ∈ U.units) : ¬ IsRootVC G S := by
  have hat := U.noskip_units hskip u hu
  obtain ⟨a, b, hvc⟩ := U.whole_vc hskip (fun he => by rw [he] at hu; exact List.not_mem_nil hu)
  obtain ⟨n, hn⟩ := hvc.2
  have hBu : G.molecule.IsBlock S u.upper u.lower := hat ▸ u.isBlock
  have hCu : CLParentPattern G S u.upper u.lower := hat ▸ u.cl
  have hc : ∃ c ∈ vinesV G, IsIngredient G.molecule S c.atoms ∧ u.upper ∈ c.atoms := by
    obtain ⟨cs, hcs, hf⟩ := U.sound u hu
    obtain ⟨T, hT, hm⟩ := (hf u.upper).mp u.isBlock.2.1
    obtain ⟨c, hcv, he, hi⟩ := hcs T hT
    exact ⟨c, hcv, he.symm ▸ hi, he.symm ▸ hm⟩
  obtain ⟨Lu, hsu⟩ := Spine.of_chain (chain_rejoint_exists hvc.1 ⟨n, hn.toVine⟩ hBu).choose_spec
  obtain ⟨c, hcv, hci, hau⟩ := hc
  have htop := containing_upper_top hsu hBu hCu hci hau
  intro hroot
  obtain ⟨S', hS', hi', hcond⟩ := hcv
  have heS := group_eq_of_ingredient (garden_isMolecule G) hS' hS hi' hci
  subst S'
  rcases hcond with ⟨_, _, _, hnot⟩ | ⟨_, hcn | hnot⟩
  · exact hnot hroot
  · obtain ⟨T, hTi, x, y, hv, hpx, hpy⟩ := hcn
    obtain ⟨p, q, hm | hm⟩ := isIngredient_vc (garden_isMolecule G) hBu hsu hTi
    all_goals
      have hj := Vine.block_joints_unique G.molecule hv.choose_spec.1 (hsu.mem_vine hm).1.choose_spec.1
      apply (spine_noCN hsu hBu (Or.inl hCu) _ hm)
      rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hpx, hpy⟩
      · exact ⟨hpy, hpx⟩
  · exact hnot htop

end WaveTurbulence.VineA
