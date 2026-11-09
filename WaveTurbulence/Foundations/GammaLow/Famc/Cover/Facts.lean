/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.TVine.Struct.Statement
public import WaveTurbulence.Foundations.Molecule.VineVertexConnected
public import WaveTurbulence.Foundations.Molecule.VineInteriorConnected
public import WaveTurbulence.Foundations.Spine.SourceDiamondClosed
/-! # The `𝒱_γ` facts used by the counting cover (packet L5c)

Main's counting cover (`Spine/Source*`) uses a few facts about the drawn vines (I)–(VIII) beyond their being blocks
(`Molecule/Vine*`). `FamFacts γ` collects the corresponding facts for the members of `𝒱_γ` (L6's `Src.IsSomeVine γ`),
and `famFacts_of_subObjects` proves them from the named input `SubObjectsInput` (= L3's `SubObjectsStatement`, N2
Theorem 1.15 (F1)–(F6); for (I), (II) and for `γ > 1/2` main's lemmas are used). The ported proofs take
`hF : FamFacts γv` as a hypothesis.

* `erase_connected` (main `Vine.isVine_erase_connected`, interior atoms): N2 Thm 1.15 (F1), DH23 `disjointlem` (ii);
* `interior_connected` (main `Vine.isVine_interior_connected`): N2 Thm 1.15 (F1), DH23 `disjointlem` (i). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.GammaLow.FinalCount.Src

/-- **NAMED INPUT (N2 Theorem 1.15 (F1)–(F6), all sizes; owner L3).** Exactly L3's published
`TVine.Struct.SubObjectsStatement` (research-gamma-half-2/NOTES.md L375–L383 with REF2's R1 patch, N3 §2.1), at the
universe of garden molecules. -/
def SubObjectsInput : Prop := TVine.Struct.SubObjectsStatement.{0, 0}

/-- The facts about the members of `𝒱_γ` used by the counting cover (stated for molecules over `Type`). -/
structure FamFacts (γ : ℝ) : Prop where
  /-- Removing any atom keeps a member connected (main `Vine.isVine_erase_connected`). -/
  erase_connected : ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) {S : Finset V}
    {a b : V}, IsSomeVine γ M S a b → ∀ z, Vine.GroupConnected M (S.erase z)
  /-- A member minus its joints is connected (main `Vine.isVine_interior_connected`). -/
  interior_connected : ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    {S : Finset V} {a b : V}, IsSomeVine γ M S a b → Vine.GroupConnected M (S \ {a, b})

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- B2 in-group connectedness gives the induced-group connectedness of `Molecule/VineChainConnected`. -/
theorem vineGroupConnected_of_groupConnected {M : Molecule V D} {S : Finset V} (h : M.GroupConnected S) :
    Vine.GroupConnected M S := by
  intro u hu v hv
  apply Relation.EqvGen.mono _ u v (h u hu v hv)
  intro a b hab
  obtain ⟨x, hx, hxa, hxb⟩ := hab
  exact ⟨⟨x, hx⟩, hxa, hxb⟩

theorem erase_erase_eq_sdiff (S : Finset V) (a b : V) : (S.erase a).erase b = S \ {a, b} := by
  ext x
  simp only [mem_erase, mem_sdiff, mem_insert, mem_singleton]
  tauto

end

/-- A T-vine minus its first joint is connected: `S ∖ {a, b}` is connected (N2 Thm 1.15 (F1)), and the second joint
`b` has a bond to an interior atom (its two `S`-bonds cannot both go to `a`, since `σ < 2` for the D11 closure, and
a joint carries no loop). -/
theorem tvine_erase_first_connected (hSO : SubObjectsInput) {V D : Type} [DecidableEq V] [Fintype D]
    [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsTVine S a b) :
    Vine.GroupConnected M (S.erase a) := by
  classical
  obtain ⟨_, haS, hbS, hab, _, _, hob, hib, _, _⟩ := h.1
  have hI : Vine.GroupConnected M (S \ {a, b}) := by
    rw [← erase_erase_eq_sdiff]
    exact vineGroupConnected_of_groupConnected (hSO M S a b h).1
  have hσ : M.sigma a b < 2 := by
    obtain ⟨-, -, G, G', hcl, -, -⟩ := h
    exact hcl.1
  obtain ⟨x, hx⟩ : ∃ x, x ∈ (M.dartsAt b).filter (fun x => M.InGroup S x ∧ M.out x = true) := by
    apply Finset.card_pos.mp
    unfold Molecule.outIn at hob
    omega
  obtain ⟨y, hy⟩ : ∃ y, y ∈ (M.dartsAt b).filter (fun x => M.InGroup S x ∧ M.out x = false) := by
    apply Finset.card_pos.mp
    unfold Molecule.inIn at hib
    omega
  simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and] at hx hy
  have hBs := Mole.block_swap_joints M h.1
  have noloop : ∀ z, M.atom z = b → M.InGroup S z → M.atom (M.mate z) ≠ b :=
    fun z hz hg he => LGSpine.block_joint_no_loop hBs hz he hg
  have key : ∃ z, M.atom z = b ∧ M.InGroup S z ∧ M.atom (M.mate z) ≠ a ∧ M.atom (M.mate z) ≠ b := by
    by_cases hxa : M.atom (M.mate x) = a
    · by_cases hya : M.atom (M.mate y) = a
      · exfalso
        have hne : M.mate y ≠ x := fun e => hab (by rw [← hya, e, hx.1])
        have hsub : ({M.mate y, x} : Finset D) ⊆ M.bonds.filter fun z => M.ends z = s(a, b) := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
            · simp [M.out_mate, hy.2.2]
            · simp only [Molecule.ends]
              rw [hya, M.mate_mate, hy.1]
          · refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.2.2⟩, ?_⟩
            simp only [Molecule.ends]
            rw [hx.1, hxa]
            exact Sym2.eq_swap
        have h2 : 2 ≤ M.sigma a b := by
          unfold Molecule.sigma Molecule.bondsBetween
          calc 2 = ({M.mate y, x} : Finset D).card := (Finset.card_pair hne).symm
            _ ≤ _ := Finset.card_le_card hsub
        omega
      · exact ⟨y, hy.1, hy.2.1, hya, noloop y hy.1 hy.2.1⟩
    · exact ⟨x, hx.1, hx.2.1, hxa, noloop x hx.1 hx.2.1⟩
  obtain ⟨z, hzb, hzg, hza, hzb'⟩ := key
  have hwI : M.atom (M.mate z) ∈ S \ {a, b} := by
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hzg.2, hza, hzb'⟩
  have hsub : S \ {a, b} ⊆ S.erase a := fun v hv => by
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
    exact Finset.mem_erase.mpr ⟨hv.2.1, hv.1⟩
  have hbE : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hbS⟩
  have hbw : (Mole.induced M (S.erase a)).SameComponent b (M.atom (M.mate z)) :=
    Relation.EqvGen.rel _ _ ((Mole.induced_adj_iff M _ b _).mpr ⟨⟨z, hzb, rfl⟩, hbE, hsub hwI⟩)
  have reach : ∀ u ∈ S.erase a, (Mole.induced M (S.erase a)).SameComponent b u := by
    intro u hu
    by_cases hub : u = b
    · subst hub
      exact Relation.EqvGen.refl _
    · have huI : u ∈ S \ {a, b} := by
        obtain ⟨hua, huS⟩ := Finset.mem_erase.mp hu
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨huS, hua, hub⟩
      exact Relation.EqvGen.trans _ _ _ hbw (Vine.induced_path_mono M hsub (hI _ hwI u huI))
  intro u hu v hv
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (reach u hu)) (reach v hv)

/-- **The `𝒱_γ` facts from N2 Theorem 1.15 (F1)** (for (I), (II) and the drawn family: main's lemmas). -/
theorem famFacts_of_subObjects (hSO : SubObjectsInput) (γ : ℝ) : FamFacts γ where
  erase_connected := by
    intro V D _ _ _ M S a b h z
    rcases h with ⟨_, h | h | h⟩ | ⟨_, X, h⟩
    · exact Vine.isVine_erase_connected h z
    · exact Vine.isVine_erase_connected h z
    · by_cases hza : z = a
      · subst hza
        exact tvine_erase_first_connected hSO h
      by_cases hzb : z = b
      · subst hzb
        exact tvine_erase_first_connected hSO (isTVine_swap h)
      by_cases hz : z ∈ S
      · exact vineGroupConnected_of_groupConnected ((hSO M S a b h).2.1 z hz hza hzb)
      · rw [Finset.erase_eq_of_notMem hz]
        exact vineGroupConnected_of_groupConnected h.1.2.2.2.2.2.2.2.2.2
    · exact Vine.isVine_erase_connected h z
  interior_connected := by
    intro V D _ _ _ M S a b h
    rcases h with ⟨_, h | h | h⟩ | ⟨_, X, h⟩
    · exact Vine.isVine_interior_connected h
    · exact Vine.isVine_interior_connected h
    · rw [← erase_erase_eq_sdiff]
      exact vineGroupConnected_of_groupConnected (hSO M S a b h).1
    · exact Vine.isVine_interior_connected h

end WaveTurbulence.GammaLow.Famc
