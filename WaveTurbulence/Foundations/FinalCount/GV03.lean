/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GV02
public import WaveTurbulence.Foundations.FinalCount.G3VineExt
/-! **G3-LOWDEG port of `G3VineExt`** (only the declarations that change: `SubHypL->SubHypL`, `HRunL->HRunL`, `InvL->InvL`, `FinalStructM->FinalStructM`, `Prop95ConclAtL->Prop95ConclAtL`; names get suffix `L`). -/
@[expose] public section
open WaveTurbulence.VineParamContract

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀}

variable {a₀ j₁ j₂ : V}

/-- The ancestor map is injective on the atoms of the component. -/
theorem FinalJoints.injOnL {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hS : SubHypL R M₀) : Set.InjOn hf.anc ↑(compMol hf.s.M a₀).atoms := by
  have hne := anc_ne_jointsL hA hD hS J.m1 J.m2 J.ne J.d1 J.d2 J.n1 J.n2 J.same J.comp'
  intro u hu v hv e
  have hu' := (mem_compMol _ _).1 hu
  have hv' := (mem_compMol _ _).1 hv
  rcases J.comp u hu'.1 hu'.2 with rfl | rfl | ⟨hu1, -⟩ <;>
    rcases J.comp v hv'.1 hv'.2 with rfl | rfl | ⟨hv1, -⟩
  · rfl
  · exact absurd e hne
  · have := hA.uniq _ hu'.1 v hv'.1 hv1 (by rw [e, hA.eps v hv'.1 hv1]); exact (J.n1 (by rw [this]; exact hv1)).elim
  · exact absurd e.symm hne
  · rfl
  · have := hA.uniq _ hu'.1 v hv'.1 hv1 (by rw [e, hA.eps v hv'.1 hv1]); exact (J.n2 (by rw [this]; exact hv1)).elim
  · have := hA.uniq _ hv'.1 u hu'.1 hu1 (by rw [← e, hA.eps u hu'.1 hu1]); exact (J.n1 (by rw [this]; exact hu1)).elim
  · have := hA.uniq _ hv'.1 u hu'.1 hu1 (by rw [← e, hA.eps u hu'.1 hu1]); exact (J.n2 (by rw [this]; exact hu1)).elim
  · rw [← hA.eps u hu'.1 hu1, ← hA.eps v hv'.1 hv1, e]

variable (hf a₀)

variable {hf a₀}

theorem IsExtra.endsL (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    {R : ℕ} (hS : SubHypL R M₀) {z : D₀} (hz : IsExtra hf a₀ M₀ z) :
    (M₀.atom z = hf.anc j₁ ∧ M₀.atom (M₀.mate z) = hf.anc j₂) ∨
      (M₀.atom z = hf.anc j₂ ∧ M₀.atom (M₀.mate z) = hf.anc j₁) := by
  have h1 := hz.atom_cases J hA
  have h2 := (hz.mate hD).atom_cases J hA
  have hnl := hS.noloop z
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hnl
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hnl

/-- At most one extra bond. -/
theorem extra_uniqueL {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hS : SubHypL R M₀) {z z' : D₀} (hz : IsExtra hf a₀ M₀ z) (hz' : IsExtra hf a₀ M₀ z')
    (hat : M₀.atom z = M₀.atom z') : z' = z := by
  by_contra hne
  -- both ends are full
  have full : ∀ {y y' : D₀} {j : V}, (j = j₁ ∨ j = j₂) → IsExtra hf a₀ M₀ y → IsExtra hf a₀ M₀ y' → y' ≠ y →
      M₀.atom y = hf.anc j → M₀.atom y' = hf.anc j →
      M₀.dartsAt (hf.anc j) = (hf.s.M.dartsAt j).image hf.s.down ∪ {y, y'} ∧ M₀.deg (hf.anc j) = 4 := by
    intro y y' j hj hy hy' hyy' ha ha'
    have hjm : j ∈ hf.s.M.atoms := by rcases hj with rfl | rfl; exact J.m1; exact J.m2
    have hjc : hf.s.M.SameComponent a₀ j := by rcases hj with rfl | rfl; exact J.c1; exact J.c2
    have hsub : (hf.s.M.dartsAt j).image hf.s.down ∪ {y, y'} ⊆ M₀.dartsAt (hf.anc j) := by
      intro w hw
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with ⟨x, hx, rfl⟩ | rfl | rfl
      · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [hA.atom, hx]
      · exact ha
      · exact ha'
    have hdis1 : ∀ w ∈ (hf.s.M.dartsAt j).image hf.s.down, w ≠ y ∧ w ≠ y' := by
      intro w hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hw
      simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hxc : hf.s.M.SameComponent a₀ (hf.s.M.atom x) := by rw [hx]; exact hjc
      exact ⟨fun e => hy.2 ⟨⟨x, hxc⟩, e⟩, fun e => hy'.2 ⟨⟨x, hxc⟩, e⟩⟩
    have hcard : ((hf.s.M.dartsAt j).image hf.s.down ∪ {y, y'}).card = 4 := by
      rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_image_of_injective _ hA.inj]
        have hd : hf.s.M.deg j = 2 := by rcases hj with rfl | rfl; exact J.d1; exact J.d2
        have : ({y, y'} : Finset D₀).card = 2 := Finset.card_pair (Ne.symm hyy')
        have h2 : (hf.s.M.dartsAt j).card = 2 := hd
        omega
      · rw [Finset.disjoint_left]
        intro w hw hw2
        simp only [Finset.mem_insert, Finset.mem_singleton] at hw2
        rcases hw2 with rfl | rfl
        · exact (hdis1 _ hw).1 rfl
        · exact (hdis1 _ hw).2 rfl
    have hle : M₀.deg (hf.anc j) ≤ 4 := deg_le_four M₀ (hS.bounds _ (hA.mem j hjm))
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      have : (M₀.dartsAt (hf.anc j)).card ≤ 4 := hle
      omega)
    have h4 : (M₀.dartsAt (hf.anc j)).card = 4 := by rw [← heq]; exact hcard
    exact ⟨heq.symm, h4⟩
  have hanc := anc_ne_jointsL hA hD hS J.m1 J.m2 J.ne J.d1 J.d2 J.n1 J.n2 J.same J.comp'
  have hmne : M₀.mate z' ≠ M₀.mate z := fun e => hne (by simpa [M₀.mate_mate] using congrArg M₀.mate e)
  have hex : ∀ j, (j = j₁ ∨ j = j₂) → ∃ y y', IsExtra hf a₀ M₀ y ∧ IsExtra hf a₀ M₀ y' ∧ y' ≠ y ∧
      M₀.atom y = hf.anc j ∧ M₀.atom y' = hf.anc j := by
    intro j hj
    have e1 := hz.endsL J hA hD hS
    have e2 := hz'.endsL J hA hD hS
    rcases e1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases e2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · rcases hj with rfl | rfl
      · exact ⟨z, z', hz, hz', hne, h1, h3⟩
      · exact ⟨_, _, hz.mate hD, hz'.mate hD, hmne, h2, h4⟩
    · exact absurd (h1.symm.trans (hat.trans h3)) hanc
    · exact absurd (h1.symm.trans (hat.trans h3)) (Ne.symm hanc)
    · rcases hj with rfl | rfl
      · exact ⟨_, _, hz.mate hD, hz'.mate hD, hmne, h2, h4⟩
      · exact ⟨z, z', hz, hz', hne, h1, h3⟩
  have hfull : ∀ j, (j = j₁ ∨ j = j₂) → ∃ y y', IsExtra hf a₀ M₀ y ∧ IsExtra hf a₀ M₀ y' ∧ y' ≠ y ∧
      M₀.dartsAt (hf.anc j) = (hf.s.M.dartsAt j).image hf.s.down ∪ {y, y'} ∧ M₀.deg (hf.anc j) = 4 := by
    intro j hj
    obtain ⟨y, y', h1, h2, h3, h4, h5⟩ := hex j hj
    exact ⟨y, y', h1, h2, h3, full hj h1 h2 h3 h4 h5⟩
  refine closed_deg4L hS (InSet hf a₀ j₁ j₂) (hA.mem j₁ J.m1) (Or.inl rfl) ?_ ?_
  · intro w hw
    rcases hw with hw | hw | ⟨c, hcm, hcc, hcε, hw⟩
    · obtain ⟨y, y', hy, hy', hyy', hfl, -⟩ := hfull j₁ (Or.inl rfl)
      have : w ∈ M₀.dartsAt (hf.anc j₁) := by simp [Molecule.dartsAt, hw]
      rw [hfl] at this
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with ⟨x, hx, rfl⟩ | rfl | rfl
      · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact InSet.mate_down J hA hD x (by rw [hx]; exact J.c1)
      · rcases hy.endsL J hA hD hS with ⟨-, h⟩ | ⟨-, h⟩
        · right; left; exact h
        · left; exact h
      · rcases hy'.endsL J hA hD hS with ⟨-, h⟩ | ⟨-, h⟩
        · right; left; exact h
        · left; exact h
    · obtain ⟨y, y', hy, hy', hyy', hfl, -⟩ := hfull j₂ (Or.inr rfl)
      have : w ∈ M₀.dartsAt (hf.anc j₂) := by simp [Molecule.dartsAt, hw]
      rw [hfl] at this
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with ⟨x, hx, rfl⟩ | rfl | rfl
      · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact InSet.mate_down J hA hD x (by rw [hx]; exact J.c2)
      · rcases hy.endsL J hA hD hS with ⟨-, h⟩ | ⟨-, h⟩
        · right; left; exact h
        · left; exact h
      · rcases hy'.endsL J hA hD hS with ⟨-, h⟩ | ⟨-, h⟩
        · right; left; exact h
        · left; exact h
    · obtain ⟨x, hx⟩ := hA.surj c hcm hcε w hw
      have hax : hf.s.M.atom x = c := hA.uniq _ (hf.s.M.atom_mem x) c hcm hcε (by rw [← hA.atom x, hx, hw])
      rw [← hx]
      exact InSet.mate_down J hA hD x (by rw [hax]; exact hcc)
  · intro b hb hbS
    rcases hbS with hb' | hb' | ⟨c, hcm, hcc, hcε, hb'⟩
    · obtain ⟨y, y', -, -, -, -, h4⟩ := hfull j₁ (Or.inl rfl); rw [hb']; exact h4
    · obtain ⟨y, y', -, -, -, -, h4⟩ := hfull j₂ (Or.inr rfl); rw [hb']; exact h4
    · rw [hb', hA.deg_eps hcm hcε]
      rcases J.comp c hcm hcc with e | e | ⟨-, h4⟩
      · exact absurd (e ▸ hcε) J.n1
      · exact absurd (e ▸ hcε) J.n2
      · exact h4

end WaveTurbulence.FinalCountG3

