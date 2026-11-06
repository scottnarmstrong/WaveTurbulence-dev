/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceDiamondClosed
/-! Same-joints overlap involving a hyper block: either one block is just its two joints
(nested), or the union is a saturated component. -/
public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.LGSpine
open Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- If all group darts of a block at the joint `a` end at `b`, the block is `{a, b}`. -/
theorem block_eq_pair_of_all_to_b {N : Molecule V D} {A : Finset V} {a b : V}
    (hA : N.IsBlock A a b)
    (h : ∀ x, N.atom x = a → N.InGroup A x → N.atom (N.mate x) = b) : A = {a, b} := by
  have hdeg := Mole.block_joint_degrees N hA
  -- darts at b in the group are exactly the mates of those at a
  have hsub : ((N.dartsAt a).filter fun x => N.InGroup A x).image N.mate ⊆
      (N.dartsAt b).filter fun x => N.InGroup A x := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hx ⊢
    exact ⟨h x hx.1 hx.2, inGroup_mate hx.2⟩
  have hcard : (((N.dartsAt a).filter fun x => N.InGroup A x).image N.mate).card =
      ((N.dartsAt b).filter fun x => N.InGroup A x).card := by
    rw [Finset.card_image_of_injective _ (fun x y hxy => by
      simpa only [N.mate_mate] using congrArg N.mate hxy)]
    exact hdeg.1.trans hdeg.2.symm
  have heq := Finset.eq_of_subset_of_card_le hsub hcard.ge
  have hb : ∀ y, N.atom y = b → N.InGroup A y → N.atom (N.mate y) = a := by
    intro y hy hyg
    have : y ∈ (N.dartsAt b).filter fun x => N.InGroup A x := by simp [Molecule.dartsAt, hy, hyg]
    rw [← heq] at this
    obtain ⟨x, hx, rfl⟩ := mem_image.mp this
    simp only [mem_filter, Molecule.dartsAt, mem_univ, true_and] at hx
    rw [N.mate_mate]; exact hx.1
  have key : ∀ p q, Relation.EqvGen (fun u v => ∃ y, N.InGroup A y ∧ N.atom y = u ∧
      N.atom (N.mate y) = v) p q → ((p = a ∨ p = b) ↔ (q = a ∨ q = b)) := by
    intro p q hpq
    induction hpq with
    | rel u v huv =>
      obtain ⟨y, hy, hyu, hyv⟩ := huv
      have fwd : ∀ y, N.InGroup A y → (N.atom y = a ∨ N.atom y = b) →
          (N.atom (N.mate y) = a ∨ N.atom (N.mate y) = b) := by
        intro y hy h'
        rcases h' with h' | h'
        · exact Or.inr (h y h' hy)
        · exact Or.inl (hb y h' hy)
      constructor
      · intro hu; rw [← hyv]; exact fwd y hy (hyu ▸ hu)
      · intro hv
        have := fwd (N.mate y) (inGroup_mate hy) (by rw [hyv]; exact hv)
        rw [N.mate_mate, hyu] at this; exact this
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
  apply Finset.Subset.antisymm
  · intro u hu
    have hconn := hA.2.2.2.2.2.2.2.2.2 a hA.2.1 u hu
    have := (key a u hconn).mp (Or.inl rfl)
    simpa using this
  · intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact hA.2.1
    · rw [mem_singleton.mp hu]; exact hA.2.2.1


/-- An ordinary block or a hyper block, with joints `a`, `b`. -/
@[expose] def OH (M : Molecule V D) (A : Finset V) (a b : V) : Prop :=
  M.IsBlock A a b ∨ Mole.IsHyperBlock M A a b

theorem OH.swap {M : Molecule V D} {A : Finset V} {a b : V} (h : OH M A a b) : OH M A b a := by
  rcases h with h | ⟨e, he, hB⟩
  · exact Or.inl (Mole.block_swap_joints M h)
  · exact Or.inr ⟨e, by rw [he, Sym2.eq_swap], Mole.block_swap_joints _ hB⟩

theorem OH.basic {M : Molecule V D} {A : Finset V} {a b : V} (h : OH M A a b) :
    A ⊆ M.atoms ∧ a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ M.degIn A a = M.degIn A b ∧
      (M.degIn A a = 2 ∨ M.degIn A a = 3) ∧
      ∀ v ∈ A, v ≠ a → v ≠ b → M.degIn A v = 4 := by
  rcases h with h | ⟨e, he, hB⟩
  · have hd := Mole.block_joint_degrees M h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hd.1.trans hd.2.symm, Or.inl hd.1,
      fun v hv h1 h2 => h.2.2.2.2.2.2.2.2.1 v hv h1 h2⟩
  · have hd := Mole.hyperBlock_degrees M ⟨e, he, hB⟩
    exact ⟨hB.1, hB.2.1, hB.2.2.1, hB.2.2.2.1, hd.1.trans hd.2.1.symm, Or.inr hd.1,
      fun v hv h1 h2 => hd.2.2 v hv h1 h2⟩

theorem OH.noloop {M : Molecule V D} {A : Finset V} {a b : V} (h : OH M A a b) {x : D}
    (hxa : M.atom x = a) (hxm : M.atom (M.mate x) = a) (hxg : M.InGroup A x) : False := by
  rcases h with h | ⟨e, he, hB⟩
  · exact block_joint_no_loop h hxa hxm hxg
  · have hne := hB.2.2.2.1
    have hend : (M.atom e = a ∧ M.atom (M.mate e) = b) ∨ (M.atom e = b ∧ M.atom (M.mate e) = a) := by
      have := he; unfold Molecule.ends at this; simpa using this
    have h1 : x ≠ e ∧ x ≠ M.mate e := by
      constructor
      · rintro rfl; rcases hend with ⟨_, h2⟩ | ⟨h2, _⟩
        · exact hne (hxm.symm.trans h2)
        · exact hne (hxa.symm.trans h2)
      · rintro rfl
        rw [M.mate_mate] at hxm
        rcases hend with ⟨_, h3⟩ | ⟨h2, _⟩
        · exact hne (hxa.symm.trans h3)
        · exact hne (hxm.symm.trans h2)
    exact block_joint_no_loop hB (x := ⟨x, h1⟩) hxa hxm hxg

theorem OH.eq_pair {M : Molecule V D} {A : Finset V} {a b : V} (h : OH M A a b)
    (hs : ∀ x, M.atom x = a → M.InGroup A x → M.atom (M.mate x) = b) : A = {a, b} := by
  rcases h with h | ⟨e, he, hB⟩
  · exact block_eq_pair_of_all_to_b h hs
  · exact block_eq_pair_of_all_to_b hB (fun x hx hg => hs x.1 hx hg)


theorem joint_union_deg_four {M : Molecule V D} (hM : M.IsMolecule) {A B : Finset V} {a b : V}
    (hA : OH M A a b) (hB : OH M B a b) (hAB : A ∩ B = {a, b})
    (hsum : 5 ≤ M.degIn A a + M.degIn B a) (hnA : ¬ A ⊆ B) (hnB : ¬ B ⊆ A) :
    M.degIn (A ∪ B) a = 4 := by
  obtain ⟨hAat, haA, hbA, hab, hdA, hgA, hintA⟩ := hA.basic
  obtain ⟨hBat, haB, hbB, _, hdB, hgB, hintB⟩ := hB.basic
  set GA := (M.dartsAt a).filter fun x => M.InGroup A x with hGA
  set GB := (M.dartsAt a).filter fun x => M.InGroup B x with hGB
  have hcA : GA.card = M.degIn A a := rfl
  have hcB : GB.card = M.degIn B a := rfl
  have hle4 : M.degIn (A ∪ B) a ≤ 4 :=
    (Mole.degIn_le_deg M _ a).trans (Mole.deg_le_four M hM (hAat haA))
  have hu : (GA ∪ GB).card ≤ M.degIn (A ∪ B) a := by
    apply Finset.card_le_card
    intro x hx
    rcases mem_union.mp hx with hx | hx <;> simp only [hGA, hGB, mem_filter] at hx ⊢
    · exact ⟨hx.1, mem_union_left _ hx.2.1, mem_union_left _ hx.2.2⟩
    · exact ⟨hx.1, mem_union_right _ hx.2.1, mem_union_right _ hx.2.2⟩
  have hci := Finset.card_union_add_card_inter GA GB
  -- shared darts lead to b
  have hshared : ∀ x, M.atom x = a → M.InGroup A x → M.InGroup B x → M.atom (M.mate x) = b := by
    intro x hxa h1 h2
    have : M.atom (M.mate x) ∈ A ∩ B := mem_inter.mpr ⟨h1.2, h2.2⟩
    rw [hAB] at this
    rcases mem_insert.mp this with h | h
    · exact (hA.noloop hxa h h1).elim
    · exact mem_singleton.mp h
  by_cases hs1 : GA ⊆ GB
  · exfalso
    apply hnA
    have : A = {a, b} := hA.eq_pair fun x hx hg => by
      have : x ∈ GA := by simp [hGA, Molecule.dartsAt, hx, hg]
      have := hs1 this
      simp only [hGB, mem_filter] at this
      exact hshared x hx hg this.2
    rw [this]
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact haB
    · rw [mem_singleton.mp hv]; exact hbB
  by_cases hs2 : GB ⊆ GA
  · exfalso
    apply hnB
    have : B = {a, b} := hB.eq_pair fun x hx hg => by
      have : x ∈ GB := by simp [hGB, Molecule.dartsAt, hx, hg]
      have := hs2 this
      simp only [hGA, mem_filter] at this
      exact hshared x hx this.2 hg
    rw [this]
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact haA
    · rw [mem_singleton.mp hv]; exact hbA
  have hi1 : (GA ∩ GB).card < GA.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left, fun h => hs1 ?_⟩
    rw [← h]; exact inter_subset_right
  have hi2 : (GA ∩ GB).card < GB.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_right, fun h => hs2 ?_⟩
    rw [← h]; exact inter_subset_left
  omega

theorem hyper_diamond_false {M : Molecule V D} (hM : M.IsMolecule) {A B : Finset V} {a b : V}
    (hA : OH M A a b) (hB : OH M B a b) (hAB : A ∩ B = {a, b})
    (hsum : 5 ≤ M.degIn A a + M.degIn B a) (hnA : ¬ A ⊆ B) (hnB : ¬ B ⊆ A) : False := by
  obtain ⟨hAat, haA, hbA, hab, hdA, hgA, hintA⟩ := hA.basic
  obtain ⟨hBat, haB, hbB, _, hdB, hgB, hintB⟩ := hB.basic
  have hja := joint_union_deg_four hM hA hB hAB hsum hnA hnB
  have hjb := joint_union_deg_four hM hA.swap hB.swap (by rw [hAB, Finset.pair_comm])
    (by omega) hnA hnB
  have hAU : A ∪ B ⊆ M.atoms := union_subset hAat hBat
  refine saturated_group_false hM hAU ⟨a, mem_union_left _ haA⟩ (fun v hv => ?_)
  by_cases hva : v = a
  · subst hva; exact hja
  by_cases hvb : v = b
  · subst hvb; exact hjb
  have hb4 : M.degIn (A ∪ B) v ≤ 4 :=
    (Mole.degIn_le_deg M _ v).trans (Mole.deg_le_four M hM (hAU hv))
  rcases mem_union.mp hv with h | h
  · have := hintA v h hva hvb
    have := degIn_union_ge_left (M := M) A B v
    omega
  · have := hintB v h hva hvb
    have := degIn_union_ge_right (M := M) A B v
    omega

end WaveTurbulence.LGSpine
