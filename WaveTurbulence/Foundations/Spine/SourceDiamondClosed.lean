/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceJointPairDichotomy
/-! Same-joints overlap of two ordinary blocks whose dart pairs are disjoint at both joints
would be a saturated component, contradicting `IsMolecule` (ii). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open Finset

set_option linter.unusedSectionVars false
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A nonempty atom set in which every atom has internal degree four is impossible. -/
theorem saturated_group_false {M : Molecule V D} (hM : M.IsMolecule) {U : Finset V}
    (hUa : U ⊆ M.atoms) (hne : U.Nonempty) (hU : ∀ v ∈ U, M.degIn U v = 4) : False := by
  have hall : ∀ p ∈ U, ∀ x ∈ M.dartsAt p, M.InGroup U x := by
    intro p hp x hx
    have h4 := hU p hp
    have hle := Mole.deg_le_four M hM (hUa hp)
    have hcard : ((M.dartsAt p).filter fun x => M.InGroup U x).card = (M.dartsAt p).card := by
      have h1 : ((M.dartsAt p).filter fun x => M.InGroup U x).card = M.degIn U p := rfl
      have h2 : (M.dartsAt p).card = M.deg p := rfl
      have h3 := Mole.degIn_le_deg M U p
      omega
    exact Finset.filter_card_eq hcard x hx
  have fwd : ∀ p q, M.Adj p q → p ∈ U → q ∈ U := by
    rintro p q ⟨x, hxp, hxq⟩ hp
    have hx : x ∈ M.dartsAt p := by simp [Molecule.dartsAt, hxp]
    have := (hall p hp x hx).2
    rwa [hxq] at this
  have key : ∀ p q, Relation.EqvGen M.Adj p q → (p ∈ U ↔ q ∈ U) := by
    intro p q h
    induction h with
    | rel a b hab =>
      refine ⟨fwd a b hab, fwd b a ?_⟩
      obtain ⟨x, hxa, hxb⟩ := hab
      exact ⟨M.mate x, hxb, by rw [M.mate_mate]; exact hxa⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  obtain ⟨v, hv⟩ := hne
  obtain ⟨u, hu, hvu, hdeg⟩ := hM.2 v (hUa hv)
  have huU : u ∈ U := (key v u hvu).mp hv
  have h4 := hU u huU
  have hle := Mole.deg_le_four M hM hu
  have h3 := Mole.degIn_le_deg M U u
  omega

theorem degIn_union_ge_left {M : Molecule V D} (A B : Finset V) (v : V) :
    M.degIn A v ≤ M.degIn (A ∪ B) v := by
  apply Finset.card_le_card
  intro x hx
  simp only [mem_filter] at hx ⊢
  exact ⟨hx.1, ⟨mem_union_left _ hx.2.1, mem_union_left _ hx.2.2⟩⟩

theorem degIn_union_ge_right {M : Molecule V D} (A B : Finset V) (v : V) :
    M.degIn B v ≤ M.degIn (A ∪ B) v := by
  apply Finset.card_le_card
  intro x hx
  simp only [mem_filter] at hx ⊢
  exact ⟨hx.1, ⟨mem_union_right _ hx.2.1, mem_union_right _ hx.2.2⟩⟩

theorem degIn_union_ge_add {M : Molecule V D} (A B : Finset V) (v : V)
    (hd : ∀ x, M.atom x = v → ¬ (M.InGroup A x ∧ M.InGroup B x)) :
    M.degIn A v + M.degIn B v ≤ M.degIn (A ∪ B) v := by
  have hdis : Disjoint ((M.dartsAt v).filter fun x => M.InGroup A x)
      ((M.dartsAt v).filter fun x => M.InGroup B x) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hxA hxB
    exact hd x hxA.1 ⟨hxA.2, hxB.2⟩
  have := Finset.card_union_of_disjoint hdis
  unfold Molecule.degIn
  rw [← this]
  apply Finset.card_le_card
  intro x hx
  rcases mem_union.mp hx with hx | hx <;> simp only [mem_filter] at hx ⊢
  · exact ⟨hx.1, mem_union_left _ hx.2.1, mem_union_left _ hx.2.2⟩
  · exact ⟨hx.1, mem_union_right _ hx.2.1, mem_union_right _ hx.2.2⟩

/-- Two ordinary blocks with the same joints, meeting exactly in the joints, cannot have
disjoint dart pairs at both joints. -/
theorem diamond_disjoint_pairs_false {M : Molecule V D} (hM : M.IsMolecule) {A B : Finset V}
    {a b : V} (hA : M.IsBlock A a b) (hB : M.IsBlock B a b)
    (ha : ∀ x, M.atom x = a → ¬ (M.InGroup A x ∧ M.InGroup B x))
    (hb : ∀ x, M.atom x = b → ¬ (M.InGroup A x ∧ M.InGroup B x)) : False := by
  have hbound : ∀ v ∈ A ∪ B, M.degIn (A ∪ B) v ≤ 4 := fun v hv =>
    (Mole.degIn_le_deg M _ v).trans (Mole.deg_le_four M hM
      (by rcases mem_union.mp hv with h | h; exacts [hA.1 h, hB.1 h]))
  refine saturated_group_false (U := A ∪ B) hM (fun v hv => ?_) ⟨a, mem_union_left _ hA.2.1⟩ ?_
  · rcases mem_union.mp hv with h | h; exacts [hA.1 h, hB.1 h]
  · intro v hv
    have hv4 := hbound v hv
    by_cases hva : v = a
    · subst hva
      have := degIn_union_ge_add A B v ha
      rw [(Mole.block_joint_degrees M hA).1, (Mole.block_joint_degrees M hB).1] at this
      omega
    by_cases hvb : v = b
    · subst hvb
      have := degIn_union_ge_add A B v hb
      rw [(Mole.block_joint_degrees M hA).2, (Mole.block_joint_degrees M hB).2] at this
      omega
    rcases mem_union.mp hv with h | h
    · have := hA.2.2.2.2.2.2.2.2.1 v h hva hvb
      have := degIn_union_ge_left (M := M) A B v
      omega
    · have := hB.2.2.2.2.2.2.2.2.1 v h hva hvb
      have := degIn_union_ge_right (M := M) A B v
      omega

/-- A joint of an ordinary block carries no self-loop of the block's group. -/
theorem block_joint_no_loop {M : Molecule V D} {A : Finset V} {a b : V} (hA : M.IsBlock A a b)
    {x : D} (hxa : M.atom x = a) (hxm : M.atom (M.mate x) = a) (hxg : M.InGroup A x) : False := by
  have hmg : M.InGroup A (M.mate x) := by
    refine ⟨hxm ▸ hxg.2 |> fun h => ?_, ?_⟩
    · rw [hxm]; rw [← hxa]; exact hxg.1
    · rw [M.mate_mate, hxa]; exact hxg.2 |> fun h => by rw [← hxm]; exact h
  have hdeg := (Mole.block_joint_degrees M hA).1
  have hsub : ({x, M.mate x} : Finset D) ⊆ (M.dartsAt a).filter fun y => M.InGroup A y := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · simp [Molecule.dartsAt, hxa, hxg]
    · rw [mem_singleton.mp hy]; simp [Molecule.dartsAt, hxm, hmg]
  have hc2 : ({x, M.mate x} : Finset D).card = 2 := Finset.card_pair (M.mate_ne x).symm
  have heq : ({x, M.mate x} : Finset D) = (M.dartsAt a).filter fun y => M.InGroup A y :=
    Finset.eq_of_subset_of_card_le hsub (by
      have : ((M.dartsAt a).filter fun y => M.InGroup A y).card = 2 := hdeg
      omega)
  have hcl : ∀ y, M.InGroup A y → M.atom y = a → M.atom (M.mate y) = a := by
    intro y hy hya
    have : y ∈ (M.dartsAt a).filter fun y => M.InGroup A y := by simp [Molecule.dartsAt, hya, hy]
    rw [← heq] at this
    rcases mem_insert.mp this with rfl | h
    · exact hxm
    · rw [mem_singleton.mp h, M.mate_mate]; exact hxa
  have hconn := hA.2.2.2.2.2.2.2.2.2 a hA.2.1 b hA.2.2.1
  have key : ∀ p q, Relation.EqvGen (fun u v => ∃ y, M.InGroup A y ∧ M.atom y = u ∧
      M.atom (M.mate y) = v) p q → (p = a ↔ q = a) := by
    intro p q h
    induction h with
    | rel u v huv =>
      obtain ⟨y, hy, hyu, hyv⟩ := huv
      constructor
      · intro hu; rw [← hyv]; exact hcl y hy (hyu.trans hu)
      · intro hv
        have hmy : M.InGroup A (M.mate y) := ⟨hy.2, by rw [M.mate_mate]; exact hy.1⟩
        have := hcl (M.mate y) hmy (hyv.trans hv)
        rw [M.mate_mate] at this
        rw [← hyu]; exact this
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
  exact hA.2.2.2.1 ((key a b hconn).mp rfl).symm

theorem inGroup_mate {M : Molecule V D} {S : Finset V} {x : D} (h : M.InGroup S x) :
    M.InGroup S (M.mate x) := ⟨h.2, by rw [M.mate_mate]; exact h.1⟩

/-- Two ordinary blocks with the same joints meeting exactly in the joints, with no shared
a-b bond dart, would form a saturated component; hence they share a joint-to-joint bond. -/
theorem diamond_shared_bond {M : Molecule V D} (hM : M.IsMolecule) {A B : Finset V}
    {a b : V} (hA : M.IsBlock A a b) (hB : M.IsBlock B a b) (hAB : A ∩ B = {a, b}) :
    ∃ z, M.atom z = a ∧ M.atom (M.mate z) = b ∧ M.InGroup A z ∧ M.InGroup B z := by
  by_contra H
  push Not at H
  have hAb := Mole.block_swap_joints M hA
  have hend : ∀ x, M.InGroup A x → M.InGroup B x → M.atom (M.mate x) = a ∨ M.atom (M.mate x) = b := by
    intro x h1 h2
    have : M.atom (M.mate x) ∈ A ∩ B := mem_inter.mpr ⟨h1.2, h2.2⟩
    rw [hAB] at this
    simpa using this
  refine diamond_disjoint_pairs_false hM hA hB ?_ ?_
  · rintro x hxa ⟨h1, h2⟩
    rcases hend x h1 h2 with h | h
    · exact block_joint_no_loop hA hxa h h1
    · exact H x hxa h h1 h2
  · rintro x hxb ⟨h1, h2⟩
    rcases hend x h1 h2 with h | h
    · have hm := hend (M.mate x) (inGroup_mate h1) (inGroup_mate h2)
      rw [M.mate_mate] at hm
      exact H (M.mate x) h (by rw [M.mate_mate]; exact hxb) (inGroup_mate h1) (inGroup_mate h2)
    · exact block_joint_no_loop hAb hxb h h1

end WaveTurbulence.LGSpine
