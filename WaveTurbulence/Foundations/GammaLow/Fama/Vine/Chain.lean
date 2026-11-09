/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.Molecule.VineSeparatorLocalization
public import WaveTurbulence.Foundations.Molecule.MoleculeHyperBlocks
import Mathlib.Tactic
/-! # Vine chains over `𝒱_γ` (packet L5a, item C)

Copies (by source, sha256 in `COPIED-SHA256SUMS`) of main's chain lemmas over L6's `𝒱_γ` chains `Src.Chain γ`:
`Molecule/VineObjects` (hyper-blocks), `Molecule/VineChainConnected`, `Molecule/VineChainCounts`,
`Molecule/VineChainEnds`, `Molecule/VineChainBlock`, `Molecule/VineSeparatorLocalization`,
`Molecule/VineEraseChainIngredient`, `Molecule/VineChainIngredients` (`vine_in_chain_ingredient`),
`Molecule/VineSmallVC`, `Molecule/VineHyperAdjointVC`, `Spine/SourceObjectUnion`, `Spine/SourceChainSwap`.
The only per-vine facts used are those of `Vine.Facts` (block, connectivity, erase-connectivity (named input
`TVineF1Input` for T-vines), small members are (I)). Family-free lemmas (degrees, separators, `Vine.DoubleChain`) are
main's, by import. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open Finset WaveTurbulence.GammaLow.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

section Basic
variable {γ : ℝ} {M : Molecule V D}

theorem isSomeVine_ends {S : Finset V} {a b : V} (h : Src.IsSomeVine γ M S a b) : a ∈ S ∧ b ∈ S ∧ a ≠ b :=
  ⟨(Src.isBlock_of_isSomeVine h).2.1, (Src.isBlock_of_isSomeVine h).2.2.1, (Src.isBlock_of_isSomeVine h).2.2.2.1⟩

theorem chain_ends {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : a ∈ S ∧ b ∈ S ∧ a ≠ b := by
  induction h with
  | single h => exact isSomeVine_ends h
  | append _ hT _ hac ih => exact ⟨mem_union_left _ ih.1, mem_union_right _ (isSomeVine_ends hT).2.1, hac⟩

theorem chain_joints_mem {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : a ∈ S ∧ b ∈ S :=
  ⟨(chain_ends h).1, (chain_ends h).2.1⟩

theorem chain_joints_ne {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : a ≠ b :=
  (chain_ends h).2.2

/-- Hyper-vines are actual hyper-blocks. -/
theorem isHV_isHyperBlock {S : Finset V} {a b : V} (h : Src.IsHV γ M S a b) : Mole.IsHyperBlock M S a b := by
  obtain ⟨e, he, hv⟩ := h
  exact ⟨e, he, Src.isBlock_of_isSomeVine hv⟩

/-- Hyper-vine-chains are actual hyper-blocks. -/
theorem isHVC_isHyperBlock {S : Finset V} {a b : V} (h : Src.IsHVC γ M S a b) : Mole.IsHyperBlock M S a b := by
  obtain ⟨e, he, hB, _⟩ := h
  exact ⟨e, he, hB⟩

/-- Actual ordered concatenation preserves connectivity. -/
theorem chain_connected {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : Vine.GroupConnected M S := by
  induction h with
  | single h => exact isSomeVine_connected h
  | append hS hT _ _ ih =>
    exact Vine.groupConnected_union M ih (isSomeVine_connected hT) (chain_joints_mem hS).2 (isSomeVine_ends hT).1

/-- TARGET defvine: every VC is connected. -/
theorem isVC_connected {S : Finset V} {a b : V} (h : Src.IsVC γ M S a b) : Vine.GroupConnected M S := by
  obtain ⟨_hB, n, hn⟩ := h
  exact chain_connected hn

theorem isSomeVine_card_ge_two {S : Finset V} {a b : V} (h : Src.IsSomeVine γ M S a b) : 2 ≤ S.card := by
  have hp : ({a, b} : Finset V) ⊆ S := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact (isSomeVine_ends h).1
    · rw [mem_singleton.mp hv]; exact (isSomeVine_ends h).2.1
  have hh := card_le_card hp
  rwa [card_pair (isSomeVine_ends h).2.2] at hh

/-- A chain of `n` vine ingredients has at least `n + 1` atoms. -/
theorem chain_card_ge {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : n + 1 ≤ S.card := by
  induction h with
  | single h => exact isSomeVine_card_ge_two h
  | @append S T a b c n hS hT hi _hne ih =>
    have htwo := isSomeVine_card_ge_two hT
    have hc := card_union_add_card_inter S T
    rw [hi, card_singleton] at hc
    omega

/-- Every small chain consists only of double-bond ingredients (main's `Vine.DoubleChain`). -/
theorem chain_doubleChain_of_card_lt_four {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n)
    (hc : S.card < 4) : Vine.DoubleChain M S a b n := by
  induction h with
  | single h => exact Vine.DoubleChain.single (isSomeVine_typeI_of_card_lt_four h hc)
  | @append S T a b c n hS hT hi hne ih =>
    have hcS : S.card < 4 := (card_le_card (subset_union_left : S ⊆ S ∪ T)).trans_lt hc
    have hcT : T.card < 4 := (card_le_card (subset_union_right : T ⊆ S ∪ T)).trans_lt hc
    exact Vine.DoubleChain.append (ih hcS) (isSomeVine_typeI_of_card_lt_four hT hcT) hi hne

/-- A VC on at most three atoms is one or two double-bond ingredients. -/
theorem isVC_doubleChain_of_card_le_three {A : Finset V} {x y : V} (hVC : Src.IsVC γ M A x y) (hc : A.card ≤ 3) :
    Vine.DoubleChain M A x y 1 ∨ Vine.DoubleChain M A x y 2 := by
  obtain ⟨_hB, n, hC⟩ := hVC
  have hp := chain_pos hC
  have hD := chain_doubleChain_of_card_lt_four hC (by omega)
  have hcount := Vine.doubleChain_card hD
  have hn : n = 1 ∨ n = 2 := by have := chain_card_ge hC; omega
  rcases hn with rfl | rfl
  · exact Or.inl hD
  · exact Or.inr hD

theorem chain_one_isSomeVine {S : Finset V} {a b : V} (h : Src.Chain γ M S a b 1) : Src.IsSomeVine γ M S a b := by
  cases h with
  | single h => exact h
  | append hS _ _ _ => exact absurd (chain_pos hS) (by omega)

/-- TARGET defvine: an HV or HVC is exactly an object with a designated joint bond whose deletion is a VC. -/
theorem hyperLike_iff_adjoint_VC {A : Finset V} {x y : V} :
    (Src.IsHV γ M A x y ∨ Src.IsHVC γ M A x y) ↔
      ∃ e : D, M.ends e = s(x, y) ∧ Src.IsVC γ (Molecule.eraseBond M e) A x y := by
  constructor
  · rintro (h | h)
    · obtain ⟨e, he, hV⟩ := h
      exact ⟨e, he, isVC_of_isSomeVine hV⟩
    · obtain ⟨e, he, hB, n, _hn, hC⟩ := h
      exact ⟨e, he, hB, n, hC⟩
  · rintro ⟨e, he, hB, n, hC⟩
    by_cases hn : n = 1
    · subst n
      exact Or.inl ⟨e, he, chain_one_isSomeVine hC⟩
    · have hpos := chain_pos hC
      exact Or.inr ⟨e, he, hB, n, by omega, hC⟩

/-- The adjoint of a three-atom HV/HVC is two concatenated double bonds. -/
theorem hyperLike_three_atom_adjoint {A : Finset V} {x y : V} (h : Src.IsHV γ M A x y ∨ Src.IsHVC γ M A x y)
    (hcard : A.card = 3) : ∃ e : D, M.ends e = s(x, y) ∧ Vine.DoubleChain (Molecule.eraseBond M e) A x y 2 := by
  obtain ⟨e, he, hVC⟩ := hyperLike_iff_adjoint_VC.mp h
  rcases isVC_doubleChain_of_card_le_three hVC (by omega) with h1 | h2
  · have hc := Vine.doubleChain_card h1
    omega
  · exact ⟨e, he, h2⟩

/-- Concatenation of chains sharing exactly the joining joint. -/
theorem chain_append_chain {S T : Finset V} {a b c : V} {n m : ℕ}
    (hS : Src.Chain γ M S a b n) (hT : Src.Chain γ M T b c m) (hST : S ∩ T = {b}) :
    Src.Chain γ M (S ∪ T) a c (n + m) := by
  induction hT generalizing S n with
  | @single T0 b0 c0 hv =>
    refine Src.Chain.append hS hv hST ?_
    intro hac
    have hcS : c0 ∈ S := hac ▸ (chain_ends hS).1
    have : c0 ∈ S ∩ T0 := mem_inter.mpr ⟨hcS, (isSomeVine_ends hv).2.1⟩
    rw [hST] at this
    exact (isSomeVine_ends hv).2.2 (mem_singleton.mp this).symm
  | @append T1 T2 b0 p c0 k hT1 hv hT12 hbc ih =>
    have hbS := (chain_ends hS).2.1
    have hb1 := (chain_ends hT1).1
    have hsub1 : S ∩ T1 ⊆ S ∩ (T1 ∪ T2) := inter_subset_inter_left subset_union_left
    have hsub2 : S ∩ T2 ⊆ S ∩ (T1 ∪ T2) := inter_subset_inter_left subset_union_right
    rw [hST] at hsub1 hsub2
    have hS1 : S ∩ T1 = {b0} :=
      Subset.antisymm hsub1 (singleton_subset_iff.mpr (mem_inter.mpr ⟨hbS, hb1⟩))
    have hS2 : S ∩ T2 ⊆ {p} := by
      intro x hx
      have hxb : x = b0 := mem_singleton.mp (hsub2 hx)
      have hxT2 := (mem_inter.mp hx).2
      have : x ∈ T1 ∩ T2 := mem_inter.mpr ⟨hxb ▸ hb1, hxT2⟩
      rw [hT12] at this
      exact this
    have h1 := ih hS hS1
    have hne : a ≠ c0 := by
      intro hac
      have hcS : c0 ∈ S := hac ▸ (chain_ends hS).1
      have : c0 ∈ S ∩ (T1 ∪ T2) := mem_inter.mpr ⟨hcS, mem_union_right _ (isSomeVine_ends hv).2.1⟩
      rw [hST] at this
      exact hbc (mem_singleton.mp this).symm
    have h2 := Src.Chain.append h1 hv (by
      rw [union_inter_distrib_right, hT12]
      exact Subset.antisymm (union_subset hS2 (Subset.refl _)) (subset_union_right)) hne
    rw [union_assoc] at h2
    exact h2

theorem chain_swap {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) : Src.Chain γ M S b a n := by
  induction h with
  | single h => exact Src.Chain.single (isSomeVine_swap h)
  | @append S T a b c n hS hT hi hne ih =>
    have h1 : Src.Chain γ M T c b 1 := Src.Chain.single (isSomeVine_swap hT)
    have h2 := chain_append_chain h1 ih (by rw [Finset.inter_comm]; exact hi)
    rw [Finset.union_comm] at h2
    rwa [Nat.add_comm] at h2

end Basic

/-! ## Chains inside blocks (main `Molecule/VineChainEnds`, `VineChainBlock`) -/

section Blocks
variable {γ : ℝ}

theorem chain_atoms_subset {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    S ⊆ M.atoms := by
  induction h with
  | single h => exact (Src.isBlock_of_isSomeVine h).1
  | append _ hT _ _ ih => exact union_subset ih (Src.isBlock_of_isSomeVine hT).1

theorem chain_endpoint_lower {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain γ M S a b n) :
    1 ≤ M.outIn S a ∧ 1 ≤ M.inIn S a ∧ 1 ≤ M.outIn S b ∧ 1 ≤ M.inIn S b := by
  induction h with
  | single h =>
    obtain ⟨_hS, _ha, _hb, _hne, hoa, hia, hob, hib, _hint⟩ := Src.isBlock_of_isSomeVine h
    omega
  | @append S T a b c n _hS hT _hi _hne ih =>
    obtain ⟨_hT, _hb, _hc, _hbc, _hob, _hib, hoc, hic, _hint⟩ := Src.isBlock_of_isSomeVine hT
    have hl := Vine.oriented_degree_mono (M := M) (show S ⊆ S ∪ T from subset_union_left) a
    have hr := Vine.oriented_degree_mono (M := M) (show T ⊆ S ∪ T from subset_union_right) c
    omega

theorem chain_interior_degree (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain γ M S a b n) : ∀ v ∈ S, v ≠ a → v ≠ b → M.degIn S v = 4 := by
  induction h with
  | single h => exact (Src.isBlock_of_isSomeVine h).2.2.2.2.2.2.2.2.1
  | @append S T a b c n hS hT hi _hne ih =>
    have hX := Src.isBlock_of_isSomeVine hT
    have hloop := Vine.connected_degree_two_no_loop M (isSomeVine_connected hT)
      hX.2.1 hX.2.2.1 hX.2.2.2.1 (Mole.block_joint_degrees M hX).1
    intro v hv hva hvc
    have hvM : v ∈ M.atoms := (union_subset (chain_atoms_subset hS) hX.1) hv
    have hbound := (Mole.degIn_le_deg M (S ∪ T) v).trans (Mole.deg_le_four M hM hvM)
    by_cases hvb : v = b
    · subst v
      have hlo := chain_endpoint_lower hS
      have hsum := Mole.outIn_add_inIn M S b
      have hTdeg := (Mole.block_joint_degrees M hX).1
      have hle := Vine.degIn_add_le_union M hi hloop b
      omega
    · rcases mem_union.mp hv with hv | hv
      · have hd := ih v hv hva hvb
        have hle := Vine.degIn_mono M (show S ⊆ S ∪ T from subset_union_left) v
        omega
      · have hd := hX.2.2.2.2.2.2.2.2.1 v hv hvb hvc
        have hle := Vine.degIn_mono M (show T ⊆ S ∪ T from subset_union_right) v
        omega

/-- In an actual block, removing its terminal vine ingredient leaves an actual prefix block. -/
theorem chain_prefix_isBlock (M : Molecule V D) (hM : M.IsMolecule) {S T : Finset V} {a b c : V} {n : ℕ}
    (hS : Src.Chain γ M S a b n) (hT : Src.IsSomeVine γ M T b c) (hi : S ∩ T = {b})
    (hU : M.IsBlock (S ∪ T) a c) : M.IsBlock S a b := by
  have hX := Src.isBlock_of_isSomeVine hT
  have hmem := chain_joints_mem hS
  have hlo := chain_endpoint_lower hS
  have hla := Vine.oriented_degree_mono M (show S ⊆ S ∪ T from subset_union_left) a
  have hloop := Vine.connected_degree_two_no_loop M (isSomeVine_connected hT)
    hX.2.1 hX.2.2.1 hX.2.2.2.1 (Mole.block_joint_degrees M hX).1
  have hob := Vine.group_filtered_card_union_le M hi hloop b (fun d => M.out d = true)
  have hib := Vine.group_filtered_card_union_le M hi hloop b (fun d => M.out d = false)
  change M.outIn S b + M.outIn T b ≤ M.outIn (S ∪ T) b at hob
  change M.inIn S b + M.inIn T b ≤ M.inIn (S ∪ T) b at hib
  have hbo := (Vine.outIn_le_outdeg M (S ∪ T) b).trans (hM.1 b (hX.1 hX.2.1)).1
  have hbi := (Vine.inIn_le_indeg M (S ∪ T) b).trans (hM.1 b (hX.1 hX.2.1)).2
  obtain ⟨_hTU, _ha, _hc, _hac, hoa, hia, _hoc, _hic, _hint⟩ := hU
  obtain ⟨_hT, _hb, _hc, _hbc, hot, hit, _hot', _hit', _hint'⟩ := hX
  refine ⟨chain_atoms_subset hS, hmem.1, hmem.2, chain_joints_ne hS,
    by omega, by omega, by omega, by omega, chain_interior_degree M hM hS, ?_⟩
  intro u hu v hv
  have hmono : (Mole.induced M S).Adj ≤
      fun x y => ∃ z, M.InGroup S z ∧ M.atom z = x ∧ M.atom (M.mate z) = y := by
    intro x y hxy
    obtain ⟨z, hx, hy⟩ := hxy
    exact ⟨z.1, z.2, hx, hy⟩
  exact Relation.EqvGen.mono hmono u v (chain_connected hS u hu v hv)

/-- A connected-after-any-erasure set inside a chain block lies in a single ingredient (main's
`Vine.erase_connected_in_chain_ingredient`). -/
theorem erase_connected_in_chain_ingredient (M : Molecule V D) (hM : M.IsMolecule) {A U : Finset V} {a b : V}
    {n : ℕ} (hconn : ∀ z, Vine.GroupConnected M (A.erase z)) (h : Src.Chain γ M U a b n) :
    M.IsBlock U a b → A ⊆ U → ∃ T p q, ChainIngredientG γ M U a b n T p q ∧ A ⊆ T := by
  induction h with
  | single h =>
    intro _hU hAU
    exact ⟨_, _, _, ChainIngredientG.single h, hAU⟩
  | @append S T a b c n hS hT hi hne ih =>
    intro hU hAU
    have hX := Src.isBlock_of_isSomeVine hT
    have hside := Vine.connected_erase_subset_side M S T A b (chain_joints_mem hS).2 hX.2.1 hAU
      (fun v hv hvb u hu huv => Vine.terminal_block_adj_mem M hM hX hU Finset.subset_union_right hv hvb hu huv)
      (hconn b)
    rcases hside with hAS | hAT
    · obtain ⟨B, p, q, hB, hAB⟩ := ih (chain_prefix_isBlock M hM hS hT hi hU) hAS
      exact ⟨B, p, q, ChainIngredientG.append_left hB hT hi hne, hAB⟩
    · exact ⟨T, b, c, ChainIngredientG.append_last hS hT hi hne, hAT⟩

/-- TARGET subsetvc's chain step: a member of `𝒱_γ` inside a chain block lies in a single ingredient. -/
theorem vine_in_chain_ingredient [Fact TVineF1Input] {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (hM : M.IsMolecule) {A U : Finset V} {x y a b : V} {n : ℕ}
    (hA : Src.IsSomeVine γ M A x y) (h : Src.Chain γ M U a b n) :
    M.IsBlock U a b → A ⊆ U → ∃ T p q, ChainIngredientG γ M U a b n T p q ∧ A ⊆ T :=
  erase_connected_in_chain_ingredient M hM (isSomeVine_erase_connected hA) h

/-- A member of `𝒱_γ` inside a block split at the initial joint of a terminal block lies on one side. -/
theorem vine_in_terminal_split [Fact TVineF1Input] {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) (hM : M.IsMolecule) {S T A : Finset V} {a b c x y : V}
    (hT : M.IsBlock T b c) (hU : M.IsBlock (S ∪ T) a c) (hbS : b ∈ S)
    (hA : Src.IsSomeVine γ M A x y) (hAU : A ⊆ S ∪ T) : A ⊆ S ∨ A ⊆ T :=
  Vine.connected_erase_subset_side M S T A b hbS hT.2.1 hAU
    (fun v hv hvb u hu huv => Vine.terminal_block_adj_mem M hM hT hU subset_union_right hv hvb hu huv)
    (isSomeVine_erase_connected hA b)

end Blocks

end WaveTurbulence.GammaLow.Fama
