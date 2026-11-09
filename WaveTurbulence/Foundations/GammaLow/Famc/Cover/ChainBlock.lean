/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.ChainFacts
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Spine.SourceVineSigma
/-! # Block prefixes of `𝒱_γ` chains; chains with a joint bond (packet L5c)

Main's `Molecule/VineChainBlock.lean` (`chain_atoms_subset`, `chain_endpoint_lower`, `chain_interior_degree`,
`chain_prefix_isBlock`) and `Spine/SourceDiamondVine.lean` (`chain_single_of_joint_bond`), sha256 in
`COPIED-SHA256SUMS`, ported from `Vine.Chain` to L6's `Src.Chain γ` (each ingredient is only used through its being a
connected block). `isSomeVine_sigma_le_one` replaces main's `isVine_bondsBetween` / `vine_typeIV_of_joint_bond`:
a member of `𝒱_γ` other than a vine (I) has at most one bond between its joints ((II): none; T-vines: `σ < 2` is part
of the D11 closure; drawn types: main's count). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.Vine (oriented_degree_mono connected_degree_two_no_loop degIn_add_le_union degIn_mono
  group_filtered_card_union_le outIn_le_outdeg inIn_le_indeg induced_path_mono)

variable {γv : ℝ} {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Every chain atom belongs to the molecule's declared atom set. -/
theorem chain_atoms_subset {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain γv M S a b n) : S ⊆ M.atoms := by
  induction h with
  | single h => exact (isBlock_of_isSomeVine h).1
  | append _ hT _ _ ih => exact union_subset ih (isBlock_of_isSomeVine hT).1

/-- Both endpoints of a chain retain at least one incidence in each direction. -/
theorem chain_endpoint_lower {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Chain γv M S a b n) :
    1 ≤ M.outIn S a ∧ 1 ≤ M.inIn S a ∧ 1 ≤ M.outIn S b ∧ 1 ≤ M.inIn S b := by
  induction h with
  | single h =>
    obtain ⟨_hS, _ha, _hb, _hne, hoa, hia, hob, hib, _hint⟩ := isBlock_of_isSomeVine h
    omega
  | @append S T a b c n _hS hT _hi _hne ih =>
    obtain ⟨_hT, _hb, _hc, _hbc, _hob, _hib, hoc, hic, _hint⟩ := isBlock_of_isSomeVine hT
    have hl := oriented_degree_mono (M := M) (show S ⊆ S ∪ T from subset_union_left) a
    have hr := oriented_degree_mono (M := M) (show T ⊆ S ∪ T from subset_union_right) c
    omega

/-- Every interior chain atom already uses all four ambient incidences. -/
theorem chain_interior_degree (M : Molecule V D) (hM : M.IsMolecule)
    {S : Finset V} {a b : V} {n : ℕ} (h : Chain γv M S a b n) :
    ∀ v ∈ S, v ≠ a → v ≠ b → M.degIn S v = 4 := by
  induction h with
  | single h => exact (isBlock_of_isSomeVine h).2.2.2.2.2.2.2.2.1
  | @append S T a b c n hS hT hi _hne ih =>
    have hX := isBlock_of_isSomeVine hT
    have hloop := connected_degree_two_no_loop M (isSomeVine_connected hT)
      hX.2.1 hX.2.2.1 hX.2.2.2.1 (Mole.block_joint_degrees M hX).1
    intro v hv hva hvc
    have hvM : v ∈ M.atoms := (union_subset (chain_atoms_subset hS) hX.1) hv
    have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvM)
    by_cases hvb : v = b
    · subst v
      have hlo := chain_endpoint_lower hS
      have hsum := Mole.outIn_add_inIn M S b
      have hTdeg := (Mole.block_joint_degrees M hX).1
      have hle := degIn_add_le_union M hi hloop b
      omega
    · rcases mem_union.mp hv with hv | hv
      · have hd := ih v hv hva hvb
        have hle := degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
        omega
      · have hd := hX.2.2.2.2.2.2.2.2.1 v hv hvb hvc
        have hle := degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
        omega

/-- In an actual block, removing its terminal `𝒱_γ` ingredient leaves an actual prefix block. -/
theorem chain_prefix_isBlock (M : Molecule V D) (hM : M.IsMolecule)
    {S T : Finset V} {a b c : V} {n : ℕ} (hS : Chain γv M S a b n)
    (hT : IsSomeVine γv M T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock S a b := by
  have hTB := isBlock_of_isSomeVine hT
  have hmem := chain_joints_mem hS
  have hlo := chain_endpoint_lower hS
  have hla := oriented_degree_mono M (show S ⊆ S ∪ T from subset_union_left) a
  have hloop := connected_degree_two_no_loop M (isSomeVine_connected hT)
    hTB.2.1 hTB.2.2.1 hTB.2.2.2.1 (Mole.block_joint_degrees M hTB).1
  have hob := group_filtered_card_union_le M hi hloop b (fun d => M.out d = true)
  have hib := group_filtered_card_union_le M hi hloop b (fun d => M.out d = false)
  change M.outIn S b + M.outIn T b ≤ M.outIn (S ∪ T) b at hob
  change M.inIn S b + M.inIn T b ≤ M.inIn (S ∪ T) b at hib
  have hbo := (outIn_le_outdeg M (S ∪ T) b).trans (hM.1 b (hTB.1 hTB.2.1)).1
  have hbi := (inIn_le_indeg M (S ∪ T) b).trans (hM.1 b (hTB.1 hTB.2.1)).2
  obtain ⟨_hTU, _ha, _hc, _hac, hoa, hia, _hoc, _hic, _hint⟩ := hU
  obtain ⟨_hT, _hb, _hc, _hbc, hot, hit, _hot', _hit', _hint'⟩ := hTB
  refine ⟨chain_atoms_subset hS, hmem.1, hmem.2, chain_joints_ne hS,
    by omega, by omega, by omega, by omega, chain_interior_degree M hM hS, ?_⟩
  intro u hu v hv
  have hmono : (Mole.induced M S).Adj ≤
      fun x y => ∃ z, M.InGroup S z ∧ M.atom z = x ∧ M.atom (M.mate z) = y := by
    intro x y hxy
    obtain ⟨z, hx, hy⟩ := hxy
    exact ⟨z.1, z.2, hx, hy⟩
  exact Relation.EqvGen.mono hmono u v (chain_connected hS u hu v hv)

/-- A chain which is an ordinary block and whose group has a joint-to-joint bond has a single ingredient
(main's `chain_single_of_joint_bond`). -/
theorem chain_single_of_joint_bond {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V}
    {a b : V} {n : ℕ} (hch : Chain γv M S a b n) (hB : M.IsBlock S a b) {z : D}
    (hza : M.atom z = a) (hzb : M.atom (M.mate z) = b) (hz : M.InGroup S z) :
    IsSomeVine γv M S a b := by
  cases hch with
  | single h => exact h
  | @append S' T _ b' _ m hS hT hi hne =>
    have hX := isBlock_of_isSomeVine hT
    exfalso
    have hP := chain_prefix_isBlock M hM hS hT hi hB
    have hbS : b ∉ S' := by
      intro hb
      have : b ∈ S' ∩ T := mem_inter.mpr ⟨hb, hX.2.2.1⟩
      rw [hi] at this
      exact hX.2.2.2.1 (mem_singleton.mp this).symm
    have h1 := (Mole.block_joint_degrees M hP).1
    have h2 := (Mole.block_joint_degrees M hB).1
    have hlt : M.degIn S' a < M.degIn (S' ∪ T) a := by
      unfold Molecule.degIn
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨z, ?_, ?_⟩
        · simp [Molecule.dartsAt, hza, hz]
        · simp only [mem_filter]
          rintro ⟨_, _, h⟩
          exact hbS (hzb ▸ h)
      · intro x hx
        simp only [mem_filter] at hx ⊢
        exact ⟨hx.1, mem_union_left _ hx.2.1, mem_union_left _ hx.2.2⟩
    omega

/-- A dart from `a` to `b` gives a bond between `a` and `b`. -/
theorem bondsBetween_pos_of_dart {M : Molecule V D} {a b : V} {z : D} (hza : M.atom z = a)
    (hzb : M.atom (M.mate z) = b) : 0 < M.bondsBetween a b := by
  unfold Molecule.bondsBetween Molecule.bonds
  apply Finset.card_pos.mpr
  by_cases hz : M.out z = true
  · exact ⟨z, by simp [hz, Molecule.ends, hza, hzb]⟩
  · refine ⟨M.mate z, ?_⟩
    have : M.out (M.mate z) = true := by
      rw [M.out_mate]; simpa using hz
    simp [this, Molecule.ends, M.mate_mate, hza, hzb, Sym2.eq_swap]

/-- A member of `𝒱_γ` which is not a vine (I) has at most one bond between its joints. -/
theorem isSomeVine_sigma_le_one {M : Molecule V D} {S : Finset V} {a b : V} (h : IsSomeVine γv M S a b)
    (hI : ¬ M.IsVine .I S a b) : M.sigma a b ≤ 1 := by
  rcases h with ⟨_, h | h | h⟩ | ⟨_, X, h⟩
  · exact absurd h hI
  · have hb := LGSpine.isVine_bondsBetween h
    unfold Molecule.sigma
    rw [hb]
    norm_num
  · obtain ⟨-, -, G, G', hcl, -, -⟩ := h
    have := hcl.1
    omega
  · have hb := LGSpine.isVine_bondsBetween h
    unfold Molecule.sigma
    rw [hb]
    cases X <;> simp_all

end WaveTurbulence.GammaLow.Famc
