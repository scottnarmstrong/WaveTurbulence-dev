/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.TVine.Struct.SubObjBridge
public import WaveTurbulence.Foundations.Molecule.VineVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineBlockSeparator
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
public import WaveTurbulence.Foundations.Molecule.VineSeparatorLocalization
public import WaveTurbulence.Foundations.Molecule.VineChainCounts
import Mathlib.Tactic
/-! # H-RS base: facts about the low family `Src.IsSomeVine Src.γL` used by the H-RS layer (L6-HRS, hand-written)

Main's proofs in `Subpro*` / `RedSplice*` use, about a single vine `M.IsVine X T b c` of a chain, its block part, its
connectivity, and that it has **no cut atom** (`Vine.isVine_erase_connected`). In the low family a member is a vine
(I), (II) or a T-vine (`Src.IsSomeVine.cases`):
* `vconnected`: a member is connected (induced form `Vine.GroupConnected`, main's `Vine.isVine_connected`);
* `tvine_erase_connected` / `isSomeVine_erase_connected`: removing any one atom keeps a member connected. For an
  interior atom of a T-vine this is N2 Thm 1.15 (F1)(ii) = N3 Lemma 4.1, **proved** (L3's `TVine.Struct.f1_mol`,
  from L1's `noCutVertex_holds`); for a joint, `S ∖ {j₁, j₂}` is connected ((F1)(i), `f1_mol`) and the other joint
  has a bond into the interior (its two group bonds cannot both go to the first joint since `σ < 2`);
* `isSomeVine_typeI_of_card_lt_four`: a member with fewer than four atoms is a double bond (I) (main's
  `Vine.isVine_typeI_of_card_lt_four`; a T-vine has at least five atoms, `tvine_card_ge_five`);
* `vine_in_terminal_split`: main's `Vine.vine_in_terminal_split` for a family member;
Imports only main, L3/L1 (proved T-vine structure) and `H.Api` (no H-MS module), so any layer can import it.
`RS/Facts.lean` adds the chain lemma. No named input is used. `vineConn_of_molConn`, `joint_interior_neighbor` and the size lemmas follow L5a's `Fama/Vine/Facts.lean`
(sha256 in `H/RS/COPIED-SHA256SUMS`), with the joint lemma stated for a block with `σ < 2`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H.RS
open Finset WaveTurbulence

universe u v

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Connectivity through the bonds of `S` gives connectivity of the induced group (main's `Vine.GroupConnected`). -/
theorem vineConn_of_molConn {M : Molecule V D} {S : Finset V} (h : M.GroupConnected S) :
    Vine.GroupConnected M S := by
  intro p hp q hq
  have key : ∀ p q, Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧
      M.atom (M.mate x) = b) p q → p = q ∨ (p ∈ S ∧ q ∈ S ∧ (Mole.induced M S).SameComponent p q) := by
    intro p q h
    induction h with
    | rel a b hab =>
      obtain ⟨x, hx, rfl, rfl⟩ := hab
      exact Or.inr ⟨hx.1, hx.2, Relation.EqvGen.rel _ _
        ((Mole.induced_adj_iff M S _ _).mpr ⟨⟨x, rfl, rfl⟩, hx.1, hx.2⟩)⟩
    | refl a => exact Or.inl rfl
    | symm a b _ ih =>
      rcases ih with rfl | ⟨h1, h2, h3⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨h2, h1, Relation.EqvGen.symm _ _ h3⟩
    | trans a b c _ _ ih1 ih2 =>
      rcases ih1 with rfl | ⟨h1, h2, h3⟩
      · exact ih2
      · rcases ih2 with rfl | ⟨h4, h5, h6⟩
        · exact Or.inr ⟨h1, h2, h3⟩
        · exact Or.inr ⟨h1, h5, Relation.EqvGen.trans _ _ _ h3 h6⟩
  rcases key p q (h p hp q hq) with rfl | ⟨_, _, h⟩
  · exact Relation.EqvGen.refl _
  · exact h

/-- A block is connected (induced form). -/
theorem block_vineConn {M : Molecule V D} {S : Finset V} {a b : V} (hB : M.IsBlock S a b) :
    Vine.GroupConnected M S :=
  vineConn_of_molConn hB.2.2.2.2.2.2.2.2.2

/-- A family member is connected (induced form; main's `Vine.isVine_connected`). -/
theorem vconnected {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V} (h : Src.IsSomeVine γ M S a b) :
    Vine.GroupConnected M S :=
  block_vineConn h.block

/-- In a block whose joints share fewer than two bonds, the first joint has a bond to an interior atom (its two group
incidences are not a loop, and at most one goes to the second joint). -/
theorem joint_interior_neighbor {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (hB : M.IsBlock S j₁ j₂)
    (hσ : M.bondsBetween j₁ j₂ < 2) : ∃ z ∈ S, z ≠ j₁ ∧ z ≠ j₂ ∧ M.Adj j₁ z := by
  classical
  have hj := hB.2.1
  have hj2 := hB.2.2.1
  have hne := hB.2.2.2.1
  have hd := (Mole.block_joint_degrees M hB).1
  have hloop := Vine.connected_degree_two_no_loop M (block_vineConn hB) hj hj2 hne hd
  have hno : ∀ x, M.atom x = j₁ → M.atom (M.mate x) ≠ j₁ := fun x hx he => hloop ⟨x, hx, he⟩
  have hp := Mole.degIn_pair_eq_bondsBetween M hne hno
  have hlt : M.degIn {j₁, j₂} j₁ < M.degIn S j₁ := by omega
  have hex : ∃ x ∈ (M.dartsAt j₁).filter (M.InGroup S),
      x ∉ (M.dartsAt j₁).filter (M.InGroup {j₁, j₂}) := by
    by_contra hc
    push Not at hc
    have hcard := Finset.card_le_card (show (M.dartsAt j₁).filter (M.InGroup S) ⊆
      (M.dartsAt j₁).filter (M.InGroup {j₁, j₂}) from hc)
    change M.degIn S j₁ ≤ M.degIn {j₁, j₂} j₁ at hcard
    omega
  obtain ⟨x, hx, hxnot⟩ := hex
  obtain ⟨hxv, hxa, hxm⟩ := Finset.mem_filter.mp hx
  have hax := (Mole.mem_dartsAt M j₁ x).mp hxv
  have hnot : M.atom (M.mate x) ≠ j₁ ∧ M.atom (M.mate x) ≠ j₂ := by
    constructor <;> intro he <;> apply hxnot <;> apply Finset.mem_filter.mpr
    · exact ⟨hxv, by simp [Molecule.InGroup, hax, he]⟩
    · exact ⟨hxv, by simp [Molecule.InGroup, hax, he]⟩
  exact ⟨M.atom (M.mate x), hxm, hnot.1, hnot.2, ⟨x, hax, rfl⟩⟩

theorem bondsBetween_comm' (M : Molecule V D) (a b : V) : M.bondsBetween a b = M.bondsBetween b a := by
  change (M.bonds.filter fun x => M.ends x = s(a, b)).card = (M.bonds.filter fun x => M.ends x = s(b, a)).card
  rw [show s(a, b) = s(b, a) from Sym2.eq_swap]

/-- A T-vine stays connected after removing one of its joints. -/
theorem tvine_erase_joint_connected {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} (h : M.IsTVine S j₁ j₂)
    {j k : V} (hjk : (j = j₁ ∧ k = j₂) ∨ (j = j₂ ∧ k = j₁)) : Vine.GroupConnected M (S.erase j) := by
  have hB := h.1
  have hσ : M.bondsBetween j₁ j₂ < 2 := by
    obtain ⟨-, -, G, G', hcl, -, -⟩ := h
    exact hcl.1
  have hBk : M.IsBlock S k j ∧ M.bondsBetween k j < 2 := by
    rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨Mole.block_swap_joints M hB, by rw [bondsBetween_comm']; exact hσ⟩
    · exact ⟨hB, hσ⟩
  obtain ⟨z, hzS, hzk, hzj, hadj⟩ := joint_interior_neighbor hBk.1 hBk.2
  have hI : Vine.GroupConnected M ((S.erase k).erase j) := by
    have h1 := (TVine.Struct.f1_mol h).1
    have heq : (S.erase k).erase j = (S.erase j₁).erase j₂ := by
      rcases hjk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Finset.erase_right_comm
      · rfl
    rw [heq]; exact vineConn_of_molConn h1
  have hsub : (S.erase k).erase j ⊆ S.erase j := by
    intro w hw
    exact mem_erase.mpr ⟨(mem_erase.mp hw).1, (mem_erase.mp (mem_erase.mp hw).2).2⟩
  have hzI : z ∈ (S.erase k).erase j := mem_erase.mpr ⟨hzj, mem_erase.mpr ⟨hzk, hzS⟩⟩
  have hk : k ∈ S.erase j := mem_erase.mpr ⟨hBk.1.2.2.2.1, hBk.1.2.1⟩
  have toZ : ∀ w ∈ S.erase j, (Mole.induced M (S.erase j)).SameComponent w z := by
    intro w hw
    by_cases hwk : w = k
    · subst hwk
      exact Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M _ _ _).mpr ⟨hadj, hk, hsub hzI⟩)
    · have hwI : w ∈ (S.erase k).erase j :=
        mem_erase.mpr ⟨(mem_erase.mp hw).1, mem_erase.mpr ⟨hwk, (mem_erase.mp hw).2⟩⟩
      exact Vine.induced_path_mono M hsub (hI w hwI z hzI)
  intro p hp q hq
  exact Relation.EqvGen.trans _ _ _ (toZ p hp) (Relation.EqvGen.symm _ _ (toZ q hq))

/-- **A T-vine has no cut atom**: removing any one atom keeps it connected (N2 Thm 1.15 (F1), proved by L1/L3, plus
the joint case). -/
theorem tvine_erase_connected {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsTVine S a b) (z : V) :
    Vine.GroupConnected M (S.erase z) := by
  by_cases hz : z ∈ S
  · by_cases hza : z = a
    · exact tvine_erase_joint_connected h (Or.inl ⟨hza, rfl⟩)
    · by_cases hzb : z = b
      · exact tvine_erase_joint_connected h (Or.inr ⟨hzb, rfl⟩)
      · exact vineConn_of_molConn ((TVine.Struct.f1_mol h).2 z hz hza hzb)
  · rw [Finset.erase_eq_self.mpr hz]
    exact block_vineConn h.1

/-- **A member of the low family has no cut atom** (main's `Vine.isVine_erase_connected`). -/
theorem isSomeVine_erase_connected {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsSomeVine Src.γL M S a b) (z : V) : Vine.GroupConnected M (S.erase z) := by
  rcases h.cases with h | h | h
  · exact Vine.isVine_erase_connected h z
  · exact Vine.isVine_erase_connected h z
  · exact tvine_erase_connected h z

/-! ## Size -/

theorem y2Step_card {G G' : TVine.UMultigraph V} (h : TVine.Y2Step G G') : G'.verts.card + 2 = G.verts.card := by
  obtain ⟨a, b, c, d, hab, -, -, -, -, -, h3, -, -, -, -, hv, -⟩ := h
  have ha : a ∈ G.verts := G.supp _ (by rw [h3]; norm_num) a (Sym2.mem_mk_left a b)
  have hb : b ∈ G.verts := G.supp _ (by rw [h3]; norm_num) b (Sym2.mem_mk_right a b)
  rw [hv, card_erase_of_mem (mem_erase.mpr ⟨hab.symm, hb⟩), card_erase_of_mem ha]
  have : 2 ≤ G.verts.card := by
    have := card_le_card (show ({a, b} : Finset V) ⊆ G.verts by
      intro x hx; rcases mem_insert.mp hx with rfl | hx
      · exact ha
      · rw [mem_singleton.mp hx]; exact hb)
    rwa [card_pair hab] at this
  omega

theorem reflTransGen_y2_card {G G' : TVine.UMultigraph V} (h : Relation.ReflTransGen TVine.Y2Step G G') :
    G'.verts.card ≤ G.verts.card := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => have := y2Step_card hs; omega

/-- A T-vine has at least five atoms (its closure reduces to the doubled triangle). -/
theorem tvine_card_ge_five {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsTVine S a b) : 5 ≤ S.card := by
  obtain ⟨hB, -, G, G', ⟨-, hv, -⟩, hr, ⟨x, y, z, hxy, hxz, hyz, hG', -⟩⟩ := h
  have h3 : G'.verts.card = 3 := by
    rw [hG', card_insert_of_notMem (by simp [hxy, hxz]), card_pair hyz]
  have hle := reflTransGen_y2_card hr
  rw [hv] at hle
  have hb' : b ∈ S.erase a := mem_erase.mpr ⟨hB.2.2.2.1.symm, hB.2.2.1⟩
  rw [card_erase_of_mem hb', card_erase_of_mem hB.2.1] at hle
  omega

/-- A member of the low family with fewer than four atoms is a double bond (I) (main's
`Vine.isVine_typeI_of_card_lt_four`). -/
theorem isSomeVine_typeI_of_card_lt_four {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsSomeVine Src.γL M S a b) (hc : S.card < 4) : M.IsVine .I S a b := by
  rcases h.cases with h | h | h
  · exact h
  · exact absurd (Vine.isVine_typeI_of_card_lt_four h hc) (by decide)
  · exact absurd (tvine_card_ge_five h) (by omega)

/-- Main's `Vine.vine_in_terminal_split` for a member of the family: a member inside `S ∪ T` (`T` a terminal block from
`b`, `S ∪ T` a block) lies on one side. -/
theorem vine_in_terminal_split (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b c x y : V}
    (hT : M.IsBlock T b c) (hU : M.IsBlock (S ∪ T) a c) (hbS : b ∈ S)
    (hA : Src.IsSomeVine Src.γL M A x y) (hAU : A ⊆ S ∪ T) : A ⊆ S ∨ A ⊆ T := by
  apply Vine.connected_erase_subset_side M S T A b hbS hT.2.1 hAU
    (fun v hv hvb u hu huv => Vine.terminal_block_adj_mem M hM hT hU subset_union_right hv hvb hu huv)
  exact isSomeVine_erase_connected hA b

end WaveTurbulence.GammaLow.FinalCount.H.RS
