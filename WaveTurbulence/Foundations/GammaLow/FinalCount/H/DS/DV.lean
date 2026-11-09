/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.DS.Member
public import WaveTurbulence.Foundations.Molecule.VineDegreeUnionIntersection
public import WaveTurbulence.Foundations.Molecule.VineFullInteriorSelection
public import WaveTurbulence.Foundations.Molecule.VineTwoJointSeparator
public import WaveTurbulence.Foundations.Molecule.VineJointFlows
public import WaveTurbulence.Foundations.Molecule.MoleculeBasic
public import WaveTurbulence.Foundations.Spine.SourceThreeBlockExclusion
/-! # H-DS: the double vine DV′ of the low family (packet L6-HDS; hand-written)

Main's DV is two vines (V) with the same joints (TARGET `vinechainlem` L1930); D11 replaces it by `DV′`
(`Molecule.IsDVPrime`, `Src.IsDV`): two members of `𝒱_γ` with `σ = 1` sharing exactly their joints. In the low family a
member with `σ = 1` is a T-vine (`isTVine_of_sigma_one`). Main's DV lemmas use of a vine (V) only: its block, its joint
pair degree `degIn {a, b} a = 1`, and its interior connectivity. Here:
* `pair_degree_one`: a block with `σ(a, b) = 1` has `degIn {a, b} a = degIn {a, b} b = 1` (the identity
  `degIn {a, b} a = 2·mult(a, a) + σ(a, b)`, `degIn_pair`);
* `tvine_interior_connected`: N2 Thm 1.15 (F1) (`Src.DSInputs.subObjects`);
* `dv_degree_profile`, `block_in_DV_both_joints_eq_branchL`, `DV_missing_joint_side_blocks`: main's DV arguments with these
  inputs. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.DS
open Finset WaveTurbulence.Vine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S T A U : Finset V}
  {a b x y : V}

/-- The path form of group connectivity gives main's induced form. -/
theorem vine_groupConnected_of (h : M.GroupConnected S) : Vine.GroupConnected M S := by
  intro u hu v hv
  apply Relation.EqvGen.mono _ u v (h u hu v hv)
  intro p q hpq
  obtain ⟨z, hz, hzp, hzq⟩ := hpq
  exact ⟨⟨z, hz⟩, hzp, hzq⟩

/-- `degIn {a, b} a = 2·mult(a, a) + σ(a, b)`. -/
theorem degIn_pair (hab : a ≠ b) :
    M.degIn {a, b} a = 2 * (TVine.Core.groupGraph M {a, b}).mult s(a, a) + M.sigma a b := by
  rw [TVine.Core.degIn_eq M (mem_insert_self a {b}),
    TVine.Core.sigma_eq M (mem_insert_self a {b}) (mem_insert_of_mem (mem_singleton_self b))]
  unfold TVine.Core.deg
  change ∑ w ∈ ({a, b} : Finset V), _ + _ = _
  rw [sum_pair hab]
  ring

/-- A block with `σ(a, b) = 1` has joint pair degrees `1`. -/
theorem pair_degree_one (hS : M.IsBlock S a b) (hσ : M.sigma a b = 1) :
    M.degIn {a, b} a = 1 ∧ M.degIn {a, b} b = 1 := by
  have hab : a ≠ b := hS.2.2.2.1
  have hsub : ({a, b} : Finset V) ⊆ S := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hS.2.1
    · exact hS.2.2.1
  have hd := Mole.block_joint_degrees M hS
  have h1 := degIn_mono M hsub a
  have h2 := degIn_mono M hsub b
  have ea := degIn_pair (M := M) hab
  have eb := degIn_pair (M := M) hab.symm
  have hσ' : M.sigma b a = 1 := by
    unfold Molecule.sigma Molecule.bondsBetween
    rw [Sym2.eq_swap]; exact hσ
  rw [pair_comm b a] at eb
  constructor <;> omega

/-- N2 Thm 1.15 (F1): the interior of a T-vine is connected. -/
theorem tvine_interior_connected (h : M.IsTVine S a b) :
    Vine.GroupConnected M (S \ {a, b}) := by
  have hF1 := ((Src.DSInputs.subObjects (V := V) (D := D)) M S a b h).1
  have he : S \ {a, b} = (S.erase a).erase b := by
    ext v
    simp only [mem_sdiff, mem_insert, mem_singleton, mem_erase]
    tauto
  rw [he]
  exact vine_groupConnected_of hF1

/-- The degree profile of a DV′: joints of degree `3`, other atoms of degree `4` (main's `isDV_degree_profile`). -/
theorem dv_degree_profile (hM : M.IsMolecule) (hσ : M.sigma a b = 1) (hS : M.IsBlock S a b)
    (hT : M.IsBlock T a b) (hi : S ∩ T = {a, b}) :
    M.degIn (S ∪ T) a = 3 ∧ M.degIn (S ∪ T) b = 3 ∧ ∀ v ∈ S ∪ T, v ≠ a → v ≠ b → M.degIn (S ∪ T) v = 4 := by
  have hs := Mole.block_joint_degrees M hS
  have ht := Mole.block_joint_degrees M hT
  have hp := pair_degree_one hS hσ
  have hda := degIn_union_inter M S T a hS.2.1 hT.2.1
  have hdb := degIn_union_inter M S T b hS.2.2.1 hT.2.2.1
  rw [hi, hp.1, hs.1, ht.1] at hda
  rw [hi, hp.2, hs.2, ht.2] at hdb
  refine ⟨by omega, by omega, ?_⟩
  intro v hv hva hvb
  have hvm : v ∈ M.atoms := (union_subset hS.1 hT.1) hv
  have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvm)
  rcases mem_union.mp hv with hv | hv
  · have hd := hS.2.2.2.2.2.2.2.2.1 v hv hva hvb
    have hle := degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
    omega
  · have hd := hT.2.2.2.2.2.2.2.2.1 v hv hva hvb
    have hle := degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
    omega

/-- The two branches of a DV′ of the low family are T-vines. -/
theorem dv_branches (hU : Src.IsDV Src.γL M U a b) :
    ∃ S T, M.sigma a b = 1 ∧ M.IsTVine S a b ∧ M.IsTVine T a b ∧ S ∩ T = {a, b} ∧ U = S ∪ T := by
  obtain ⟨hσ, S, T, hS, hT, hi, rfl⟩ := hU
  exact ⟨S, T, hσ, isTVine_of_sigma_one hS hσ, isTVine_of_sigma_one hT hσ, hi, rfl⟩

/-- Primitive two-joint separator localization in the two branches of a DV (main's `DV_missing_joint_side`, block
branches). -/
theorem DV_missing_joint_side_blocks (hM : M.IsMolecule) (hS : M.IsBlock S a b) (hT : M.IsBlock T a b)
    (hAU : A ⊆ S ∪ T) (hmiss : ¬(a ∈ A ∧ b ∈ A))
    (hconn : ∀ z, z = a ∨ z = b → Vine.GroupConnected M (A.erase z)) : A ⊆ S ∨ A ⊆ T := by
  by_cases hb : b ∈ A
  · have ha : a ∉ A := fun ha => hmiss ⟨ha, hb⟩
    exact two_groups_missing_right_joint_side M hM S T A b a hS.2.2.1 hT.2.2.1
      hS.2.2.2.1.symm hT.1
      (fun v hv hvb hva => hT.2.2.2.2.2.2.2.2.1 v hv hva hvb) hAU ha (hconn b (Or.inr rfl))
  · exact two_groups_missing_right_joint_side M hM S T A a b hS.2.1 hT.2.1
      hS.2.2.2.1 hT.1 hT.2.2.2.2.2.2.2.2.1 hAU hb (hconn a (Or.inl rfl))

/-- A block contained in a DV′ of the low family and containing both joints is one of its two branches (main's
`block_in_DV_both_joints_eq_branch`; the branches are T-vines with `σ = 1`). -/
theorem block_in_DV_both_joints_eq_branchL (hM : M.IsMolecule) (hσ : M.sigma a b = 1)
    (hS : M.IsTVine S a b) (hT : M.IsTVine T a b) (hi : S ∩ T = {a, b}) (hA : M.IsBlock A x y)
    (hAU : A ⊆ S ∪ T) (ha : a ∈ A) (hb : b ∈ A) : A = S ∨ A = T := by
  have hdU := dv_degree_profile hM hσ hS.1 hT.1 hi
  have hj := joints_eq_of_two_low_degrees M hAU ha hb hS.1.2.2.2.1 hA.2.2.2.1
    hdU.1.le hdU.2.1.le hA.2.2.2.2.2.2.2.2.1
  have hda : M.degIn A a = 2 := by
    have ham : a ∈ ({x, y} : Finset V) := by rw [hj]; exact mem_insert_self _ _
    rcases mem_insert.mp ham with hax | hay
    · exact hax.symm ▸ (Mole.block_joint_degrees M hA).1
    · exact (mem_singleton.mp hay).symm ▸ (Mole.block_joint_degrees M hA).2
  have hfull (v : V) (hv : v ∈ A) (hvj : v ∉ ({a, b} : Finset V)) : M.degIn A v = 4 := by
    have hvxy : v ∉ ({x, y} : Finset V) := by rw [hj]; exact hvj
    have hne : v ≠ x ∧ v ≠ y := by simpa only [mem_insert, mem_singleton, not_or] using hvxy
    exact hA.2.2.2.2.2.2.2.2.1 v hv hne.1 hne.2
  have lower (B : Finset V) (hB : M.IsTVine B a b) : ({a, b} : Finset V) ⊆ B := by
    intro v hv
    rcases mem_insert.mp hv with hva | hvb
    · exact hva.symm ▸ hB.1.2.1
    · exact (mem_singleton.mp hvb).symm ▸ hB.1.2.2.1
  have fills (B : Finset V) (hB : M.IsTVine B a b) (u : V) (huA : u ∈ A) (huI : u ∈ B \ {a, b}) : B ⊆ A :=
    full_interior_selection M hM hA.1 ha hb (tvine_interior_connected hB)
      (fun v hv hvI => hfull v hv (mem_sdiff.mp hvI).2) huA huI
  have hn : ¬A ⊆ ({a, b} : Finset V) := by
    intro hsub
    have hpairSub : ({a, b} : Finset V) ⊆ A := by
      intro v hv
      rcases mem_insert.mp hv with hva | hvb
      · exact hva.symm ▸ ha
      · exact (mem_singleton.mp hvb).symm ▸ hb
    have heq := Subset.antisymm hsub hpairSub
    have hp := (pair_degree_one hS.1 hσ).1
    rw [heq, hp] at hda
    omega
  obtain ⟨u, huA, huj⟩ := Finset.not_subset.mp hn
  obtain ⟨B, C, hB, hC, hUeq, hBA, hchoice⟩ : ∃ B C, M.IsTVine B a b ∧ M.IsTVine C a b ∧
      S ∪ T = B ∪ C ∧ B ⊆ A ∧ (B = S ∨ B = T) := by
    rcases mem_union.mp (hAU huA) with huS | huT
    · exact ⟨S, T, hS, hT, rfl, fills S hS u huA (mem_sdiff.mpr ⟨huS, huj⟩), Or.inl rfl⟩
    · exact ⟨T, S, hT, hS, union_comm S T, fills T hT u huA (mem_sdiff.mpr ⟨huT, huj⟩), Or.inr rfl⟩
  have hAB : A ⊆ B := by
    intro v hvA
    by_contra hvB
    have hvC : v ∈ C := (mem_union.mp (hUeq ▸ hAU hvA)).resolve_left hvB
    have hvj : v ∉ ({a, b} : Finset V) := fun hh => hvB (lower B hB hh)
    have hCA := fills C hC v hvA (mem_sdiff.mpr ⟨hvC, hvj⟩)
    have hUA : S ∪ T ⊆ A := by rw [hUeq]; exact union_subset hBA hCA
    have heq := Subset.antisymm hAU hUA
    rw [heq, hdU.1] at hda
    omega
  have heq := Subset.antisymm hAB hBA
  subst A
  exact hchoice

/-- A dart joining `a` to `b` gives a bond between them. -/
theorem bondsBetween_pos_of_dart {z : D} (hza : M.atom z = a) (hzb : M.atom (M.mate z) = b) :
    0 < M.bondsBetween a b := by
  unfold Molecule.bondsBetween Molecule.bonds
  apply Finset.card_pos.mpr
  by_cases hz : M.out z = true
  · exact ⟨z, by simp [hz, Molecule.ends, hza, hzb]⟩
  · refine ⟨M.mate z, ?_⟩
    have : M.out (M.mate z) = true := by
      rw [M.out_mate]; simpa using hz
    simp [this, Molecule.ends, M.mate_mate, hza, hzb, Sym2.eq_swap]

/-- A vine of `𝒱_enl` whose joints are joined by a bond is a double bond (I), or a T-vine with `σ = 1` ((II) has
`σ = 0`; main's `vine_typeIV_of_joint_bond`: (I) or (V)). -/
theorem vineEnl_joint_bond_cases {z : D} (hX : M.IsVineEnl S a b) (hza : M.atom z = a)
    (hzb : M.atom (M.mate z) = b) : M.IsVine .I S a b ∨ (M.IsTVine S a b ∧ M.sigma a b = 1) := by
  have hpos := bondsBetween_pos_of_dart hza hzb
  rcases hX with h | h | h
  · exact Or.inl h
  · have h0 : M.bondsBetween a b = 0 := LGSpine.isVine_bondsBetween h
    omega
  · have hle := isTVine_sigma_le h
    unfold Molecule.sigma at hle ⊢
    exact Or.inr ⟨h, by omega⟩

/-- **Partner uniqueness for DV′ branches** (main's `source_doubleVine_partner_unique`): if `S, T` and `S, U` are DV′ pairs
with joints `a, b` (`σ = 1`, `T` a T-vine), then `T = U` (three blocks with the same joints would saturate a
component, main's `no_three_joint_blocks`). -/
theorem dv_partner_unique [Src.DSInputs V D] (hM : M.IsMolecule) (hσ : M.sigma a b = 1) (hS : M.IsBlock S a b)
    (hT : M.IsTVine T a b) (hU : M.IsBlock U a b) (hST : S ∩ T = {a, b}) (hSU : S ∩ U = {a, b}) : T = U := by
  by_cases hTU : T ⊆ U
  · exact nested_blocks_both_joints_eq M hT.1 hU (vine_groupConnected_of hU.2.2.2.2.2.2.2.2.2) hTU hT.1.2.1
      hT.1.2.2.1
  · have hInt := Mole.block_same_joints_intersection M hM hT.1 hU hTU (tvine_interior_connected hT)
    have hp := pair_degree_one hS hσ
    exact (LGSpine.no_three_joint_blocks M hM hS hT.1 hU hST hSU hInt (by
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · exact hp.1
      · exact (mem_singleton.mp hv).symm ▸ hp.2)).elim

/-- Partner uniqueness for DV′ branches does not depend on the ordering of the joints. -/
theorem dv_partner_unique_unordered [Src.DSInputs V D] (hM : M.IsMolecule) {c e : V} (hσ : M.sigma a b = 1)
    (hS : M.IsBlock S a b) (hT : M.IsTVine T a b) (hS' : M.IsBlock S c e) (hU : M.IsBlock U c e)
    (hST : S ∩ T = {a, b}) (hSU : S ∩ U = {c, e}) : T = U := by
  have hj := block_joints_unique M hS hS'
  have hce : c ≠ e := hS'.2.2.2.1
  have hc : c ∈ ({a, b} : Finset V) := by rw [hj]; simp
  have he : e ∈ ({a, b} : Finset V) := by rw [hj]; simp
  simp only [mem_insert, mem_singleton] at hc he
  rcases hc with rfl | rfl <;> rcases he with rfl | rfl
  · exact absurd rfl hce
  · exact dv_partner_unique hM hσ hS hT hU hST hSU
  · exact dv_partner_unique hM hσ hS hT (Mole.block_swap_joints M hU) hST (by rw [pair_comm]; exact hSU)
  · exact absurd rfl hce

end WaveTurbulence.GammaLow.FinalCount.H.DS
