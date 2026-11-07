/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineLG2
/-! **FINALCOUNT-G3: `vineLG`, part 3: the unselected vine of a DV (`C2Cover`).**

Let `B` be the unselected vine of a DV `A ∪ B` (joints `a, b`), whose partner `A` is a VC member of `C₂` (hence removed by Step 1).
If `A, B` share no bond, then every atom of `A ∪ B` has degree `4` and `A ∪ B` is closed under bonds, contradicting
connectedness (`closed_deg4`).  If they share a bond `e`, then `e` is a dart of `B` at a joint of the final vine component with
ancestor group `B`, hence the image of a final dart, but `e` is a dart of the VC `A`, which Step 1 removed. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

theorem allIn_of_degIn {R : ℕ} (hS : SubHyp R M₀) {S : Finset V} {v : V} (hv : v ∈ M₀.atoms)
    (h4 : M₀.degIn S v = 4) : ∀ z, M₀.atom z = v → M₀.InGroup S z := by
  have hle : M₀.deg v ≤ 4 := deg_le_four M₀ (hS.bounds v hv)
  have hsub : (M₀.dartsAt v).filter (M₀.InGroup S) ⊆ M₀.dartsAt v := Finset.filter_subset _ _
  have hcard : (M₀.dartsAt v).card ≤ ((M₀.dartsAt v).filter (M₀.InGroup S)).card := by
    have : M₀.deg v = (M₀.dartsAt v).card := rfl
    have h' : M₀.degIn S v = ((M₀.dartsAt v).filter (M₀.InGroup S)).card := rfl
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro z hz
  have : z ∈ M₀.dartsAt v := (Mole.mem_dartsAt M₀ _ _).2 hz
  rw [← heq] at this
  exact (Finset.mem_filter.1 this).2

theorem joint_full {R : ℕ} (hS : SubHyp R M₀) {A B : Finset V} {a : V} (ha : a ∈ M₀.atoms)
    (hA : M₀.degIn A a = 2) (hB : M₀.degIn B a = 2) (hdis : ¬ ∃ z, M₀.InGroup A z ∧ M₀.InGroup B z) :
    M₀.deg a = 4 ∧ ∀ z, M₀.atom z = a → M₀.InGroup A z ∨ M₀.InGroup B z := by
  have hle : M₀.deg a ≤ 4 := deg_le_four M₀ (hS.bounds a ha)
  set FA := (M₀.dartsAt a).filter (M₀.InGroup A)
  set FB := (M₀.dartsAt a).filter (M₀.InGroup B)
  have cA : FA.card = 2 := hA
  have cB : FB.card = 2 := hB
  have hd : Disjoint FA FB := by
    rw [Finset.disjoint_left]
    intro z h1 h2
    exact hdis ⟨z, (Finset.mem_filter.1 h1).2, (Finset.mem_filter.1 h2).2⟩
  have hcu : (FA ∪ FB).card = 4 := by rw [Finset.card_union_of_disjoint hd, cA, cB]
  have hsub : FA ∪ FB ⊆ M₀.dartsAt a := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdeg : M₀.deg a = (M₀.dartsAt a).card := rfl
  have hge := Finset.card_le_card hsub
  have heq : FA ∪ FB = M₀.dartsAt a := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨by omega, fun z hz => ?_⟩
  have : z ∈ M₀.dartsAt a := (Mole.mem_dartsAt M₀ _ _).2 hz
  rw [← heq, Finset.mem_union] at this
  rcases this with h | h
  · exact Or.inl (Finset.mem_filter.1 h).2
  · exact Or.inr (Finset.mem_filter.1 h).2

theorem residual_unsel {R : ℕ} (hS : SubHyp R M₀) (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc)
    (hD : DartRel M₀ hf.s) (hnl : ∀ x : hf.s.D, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x))
    (B : Finset V) (hBat : B = AncGroup hf a₀) (A : Finset V) (a b : V) (hVA : M₀.IsVine .V A a b)
    (hVB : M₀.IsVine .V B a b) (hAB : A ∩ B = {a, b})
    (U : Object M₀) (hUA : U.atoms = A) (hUvc : ∃ h, U.shape = VineLikeObject.vc h)
    (hrem : ∀ x : hf.s.D, ¬ U.ContainsDart (hf.s.down x)) : False := by
  have bA := hVA.1
  have bB := hVB.1
  have dA := Mole.block_joint_degrees M₀ bA
  have dB := Mole.block_joint_degrees M₀ bB
  have aA : a ∈ A := bA.2.1
  have bbA : b ∈ A := bA.2.2.1
  have aB : a ∈ B := bB.2.1
  have bbB : b ∈ B := bB.2.2.1
  have hab : a ≠ b := bA.2.2.2.1
  have aM : a ∈ M₀.atoms := bA.1 aA
  have bM : b ∈ M₀.atoms := bA.1 bbA
  by_cases hsh : ∃ z, M₀.InGroup A z ∧ M₀.InGroup B z
  · obtain ⟨z, zA, zB⟩ := hsh
    have mem : ∀ v, v ∈ A → v ∈ B → v = a ∨ v = b := fun v h1 h2 => by
      have : v ∈ A ∩ B := Finset.mem_inter.2 ⟨h1, h2⟩
      rw [hAB] at this; simpa using this
    have h1 := mem _ zA.1 zB.1
    have h2 := mem _ zA.2 zB.2
    have hnl0 := hS.noloop z
    -- an `e` at the joint `a`
    obtain ⟨e, he, heA, heB⟩ : ∃ e, M₀.atom e = a ∧ M₀.InGroup A e ∧ M₀.InGroup B e := by
      rcases h1 with h1 | h1
      · exact ⟨z, h1, zA, zB⟩
      · rcases h2 with h2 | h2
        · exact ⟨M₀.mate z, h2, ⟨zA.2, by rw [M₀.mate_mate]; exact zA.1⟩, ⟨zB.2, by rw [M₀.mate_mate]; exact zB.1⟩⟩
        · exact absurd (h1.trans h2.symm) hnl0
    obtain ⟨c, hc, hca⟩ := Finset.mem_image.1 (hBat ▸ aB : a ∈ AncGroup hf a₀)
    obtain ⟨hcm, hcc⟩ := (mem_compMol _ _).1 hc
    have hfinal : ∃ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) ∧ hf.s.down x = e := by
      have hjoint : ∀ j, j ∈ hf.s.M.atoms → hf.s.M.SameComponent a₀ j → hf.s.M.deg j = 2 → hf.anc j = a →
          ∃ x : hf.s.D, hf.s.M.SameComponent a₀ (hf.s.M.atom x) ∧ hf.s.down x = e := by
        intro j hj hcj hd haj
        obtain ⟨x, hx, hxe⟩ := group_darts_joint hA hD hnl hj hcj hd
          (by rw [haj, ← hBat]; exact dB.1.le) e (by rw [he, haj]) (by rw [← hBat]; exact heB)
        exact ⟨x, by rw [hx]; exact hcj, hxe⟩
      rcases J.comp c hcm hcc with rfl | rfl | ⟨hε, -⟩
      · exact hjoint c hcm hcc J.d1 hca
      · exact hjoint c hcm hcc J.d2 hca
      · have hac : hf.anc c = c := hA.eps c hcm hε
        obtain ⟨x, hx⟩ := hA.surj c hcm hε e (he.trans (hca.symm.trans hac))
        have hax : hf.s.M.atom x = c := hA.uniq _ (hf.s.M.atom_mem x) c hcm hε (by rw [← hA.atom x, hx]; exact he.trans (hca.symm.trans hac))
        exact ⟨x, by rw [hax]; exact hcc, hx⟩
    obtain ⟨x, -, hx⟩ := hfinal
    apply hrem x
    obtain ⟨h, hsh⟩ := hUvc
    unfold Object.ContainsDart
    rw [hsh]
    show M₀.InGroup U.atoms _
    rw [hUA, hx]; exact heA
  · -- no shared bond: `A ∪ B` is a closed set of degree-`4` atoms
    have hfa := joint_full hS aM dA.1 dB.1 hsh
    have hfb := joint_full hS bM dA.2 dB.2 hsh
    refine closed_deg4 hS (fun v => v ∈ A ∨ v ∈ B) aM (Or.inl aA) ?_ ?_
    · intro z hz
      have key : ∀ v, M₀.atom z = v → (v ∈ A ∨ v ∈ B) → M₀.atom (M₀.mate z) ∈ A ∨ M₀.atom (M₀.mate z) ∈ B := by
        intro v hzv hv
        have jc : ∀ w, w = a ∨ w = b → M₀.atom z = w → M₀.atom (M₀.mate z) ∈ A ∨ M₀.atom (M₀.mate z) ∈ B := by
          intro w hw hzw
          have := (hw.elim (fun h => h ▸ hfa) (fun h => h ▸ hfb)).2 z hzw
          rcases this with h | h
          · exact Or.inl h.2
          · exact Or.inr h.2
        by_cases hva : v = a
        · exact jc a (Or.inl rfl) (hzv.trans hva)
        by_cases hvb : v = b
        · exact jc b (Or.inr rfl) (hzv.trans hvb)
        have hvm : v ∈ M₀.atoms := hzv ▸ M₀.atom_mem z
        rcases hv with hv | hv
        · exact Or.inl (allIn_of_degIn hS hvm (bA.2.2.2.2.2.2.2.2.1 v hv hva hvb) z hzv).2
        · exact Or.inr (allIn_of_degIn hS hvm (bB.2.2.2.2.2.2.2.2.1 v hv hva hvb) z hzv).2
      exact key _ rfl hz
    · intro v hv hvS
      have hle : M₀.deg v ≤ 4 := deg_le_four M₀ (hS.bounds v hv)
      by_cases hva : v = a
      · exact hva ▸ hfa.1
      by_cases hvb : v = b
      · exact hvb ▸ hfb.1
      rcases hvS with h | h
      · have := bA.2.2.2.2.2.2.2.2.1 v h hva hvb
        have := Mole.degIn_le_deg M₀ A v
        omega
      · have := bB.2.2.2.2.2.2.2.2.1 v h hva hvb
        have := Mole.degIn_le_deg M₀ B v
        omega

end WaveTurbulence.FinalCountG3
