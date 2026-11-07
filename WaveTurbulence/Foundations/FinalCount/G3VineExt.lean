/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineObj
/-! **FINALCOUNT-G3: identification of a final vine component, part 3**: the "extra" darts of `M_sub` in the group
`S' = anc '' (atoms of the component)` that do not come from the component.  Each extra bond joins the ancestors
`anc j₁, anc j₂` of the two joints, and at most one extra bond exists. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀}

/-- The shape of a final component that is a candidate vine: two non-`ε` joints of degree `2`, all other atoms `ε` of
degree `4`. -/
structure FinalJoints (hf : HSt V D₀) (a₀ j₁ j₂ : V) : Prop where
  m1 : j₁ ∈ hf.s.M.atoms
  m2 : j₂ ∈ hf.s.M.atoms
  ne : j₁ ≠ j₂
  c1 : hf.s.M.SameComponent a₀ j₁
  c2 : hf.s.M.SameComponent a₀ j₂
  d1 : hf.s.M.deg j₁ = 2
  d2 : hf.s.M.deg j₂ = 2
  n1 : hf.s.cls j₁ ≠ .eps
  n2 : hf.s.cls j₂ ≠ .eps
  comp : ∀ b ∈ hf.s.M.atoms, hf.s.M.SameComponent a₀ b → b = j₁ ∨ b = j₂ ∨ (hf.s.cls b = .eps ∧ hf.s.M.deg b = 4)

variable {a₀ j₁ j₂ : V}

theorem FinalJoints.comp' (J : FinalJoints hf a₀ j₁ j₂) : ∀ b ∈ hf.s.M.atoms, hf.s.M.SameComponent j₁ b →
    b = j₁ ∨ b = j₂ ∨ (hf.s.cls b = .eps ∧ hf.s.M.deg b = 4) := fun b hb h =>
  J.comp b hb (Relation.EqvGen.trans _ _ _ J.c1 h)

theorem FinalJoints.same (J : FinalJoints hf a₀ j₁ j₂) : hf.s.M.SameComponent j₁ j₂ :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ J.c1) J.c2

/-- The ancestor map is injective on the atoms of the component. -/
theorem FinalJoints.injOn {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hS : SubHyp R M₀) : Set.InjOn hf.anc ↑(compMol hf.s.M a₀).atoms := by
  have hne := anc_ne_joints hA hD hS J.m1 J.m2 J.ne J.d1 J.d2 J.n1 J.n2 J.same J.comp'
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

/-- The group of `M_sub` formed by the ancestors of the atoms of the component. -/
noncomputable def AncGroup : Finset V := (compMol hf.s.M a₀).atoms.image hf.anc

/-- A dart of the group `AncGroup` that does not come from the component. -/
def IsExtra (M₀ : Molecule V D₀) (z : D₀) : Prop :=
  M₀.InGroup (AncGroup hf a₀) z ∧ ¬ ∃ x, compEmb hf a₀ x = z

variable {hf a₀}

theorem IsExtra.mate (hD : DartRel M₀ hf.s) {z : D₀} (hz : IsExtra hf a₀ M₀ z) : IsExtra hf a₀ M₀ (M₀.mate z) := by
  refine ⟨⟨hz.1.2, by rw [M₀.mate_mate]; exact hz.1.1⟩, ?_⟩
  rintro ⟨x, hx⟩
  apply hz.2
  refine ⟨⟨hf.s.M.mate x.1, compP_closed _ _ x.1 x.2⟩, ?_⟩
  show hf.s.down (hf.s.M.mate x.1) = z
  rw [← hD.mate x.1]
  have : hf.s.down x.1 = M₀.mate z := hx
  rw [this, M₀.mate_mate]

theorem IsExtra.atom_cases (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) {z : D₀}
    (hz : IsExtra hf a₀ M₀ z) : M₀.atom z = hf.anc j₁ ∨ M₀.atom z = hf.anc j₂ := by
  obtain ⟨c, hc, hcz⟩ := Finset.mem_image.1 hz.1.1
  have hc' := (mem_compMol _ _).1 hc
  rcases J.comp c hc'.1 hc'.2 with rfl | rfl | ⟨hε, -⟩
  · left; exact hcz.symm
  · right; exact hcz.symm
  · exfalso
    have hcz' : M₀.atom z = c := by rw [← hcz, hA.eps c hc'.1 hε]
    obtain ⟨x, hx⟩ := hA.surj c hc'.1 hε z hcz'
    apply hz.2
    have hax : hf.s.M.atom x = c := hA.uniq _ (hf.s.M.atom_mem x) c hc'.1 hε (by rw [← hA.atom x, hx, hcz'])
    exact ⟨⟨x, by rw [hax]; exact hc'.2⟩, hx⟩

theorem IsExtra.ends (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    {R : ℕ} (hS : SubHyp R M₀) {z : D₀} (hz : IsExtra hf a₀ M₀ z) :
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

/-- membership in the closure candidate `{anc j₁, anc j₂} ∪ ε-atoms of the component`. -/
def InSet (hf : HSt V D₀) (a₀ j₁ j₂ : V) (b : V) : Prop :=
  b = hf.anc j₁ ∨ b = hf.anc j₂ ∨ ∃ c ∈ hf.s.M.atoms, hf.s.M.SameComponent a₀ c ∧ hf.s.cls c = .eps ∧ b = c

theorem InSet.mate_down (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (x : hf.s.D) (hx : hf.s.M.SameComponent a₀ (hf.s.M.atom x)) :
    InSet hf a₀ j₁ j₂ (M₀.atom (M₀.mate (hf.s.down x))) := by
  rw [hD.mate x, hA.atom]
  have hc : hf.s.M.SameComponent a₀ (hf.s.M.atom (hf.s.M.mate x)) :=
    Relation.EqvGen.trans _ _ _ hx (Relation.EqvGen.rel _ _ ⟨x, rfl, rfl⟩)
  rcases J.comp _ (hf.s.M.atom_mem _) hc with e | e | ⟨hε, _⟩
  · left; rw [e]
  · right; left; rw [e]
  · right; right
    exact ⟨_, hf.s.M.atom_mem _, hc, hε, hA.eps _ (hf.s.M.atom_mem _) hε⟩

/-- At most one extra bond. -/
theorem extra_unique {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hS : SubHyp R M₀) {z z' : D₀} (hz : IsExtra hf a₀ M₀ z) (hz' : IsExtra hf a₀ M₀ z')
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
  have hanc := anc_ne_joints hA hD hS J.m1 J.m2 J.ne J.d1 J.d2 J.n1 J.n2 J.same J.comp'
  have hmne : M₀.mate z' ≠ M₀.mate z := fun e => hne (by simpa [M₀.mate_mate] using congrArg M₀.mate e)
  have hex : ∀ j, (j = j₁ ∨ j = j₂) → ∃ y y', IsExtra hf a₀ M₀ y ∧ IsExtra hf a₀ M₀ y' ∧ y' ≠ y ∧
      M₀.atom y = hf.anc j ∧ M₀.atom y' = hf.anc j := by
    intro j hj
    have e1 := hz.ends J hA hD hS
    have e2 := hz'.ends J hA hD hS
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
  refine closed_deg4 hS (InSet hf a₀ j₁ j₂) (hA.mem j₁ J.m1) (Or.inl rfl) ?_ ?_
  · intro w hw
    rcases hw with hw | hw | ⟨c, hcm, hcc, hcε, hw⟩
    · obtain ⟨y, y', hy, hy', hyy', hfl, -⟩ := hfull j₁ (Or.inl rfl)
      have : w ∈ M₀.dartsAt (hf.anc j₁) := by simp [Molecule.dartsAt, hw]
      rw [hfl] at this
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with ⟨x, hx, rfl⟩ | rfl | rfl
      · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact InSet.mate_down J hA hD x (by rw [hx]; exact J.c1)
      · rcases hy.ends J hA hD hS with ⟨-, h⟩ | ⟨-, h⟩
        · right; left; exact h
        · left; exact h
      · rcases hy'.ends J hA hD hS with ⟨-, h⟩ | ⟨-, h⟩
        · right; left; exact h
        · left; exact h
    · obtain ⟨y, y', hy, hy', hyy', hfl, -⟩ := hfull j₂ (Or.inr rfl)
      have : w ∈ M₀.dartsAt (hf.anc j₂) := by simp [Molecule.dartsAt, hw]
      rw [hfl] at this
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with ⟨x, hx, rfl⟩ | rfl | rfl
      · simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact InSet.mate_down J hA hD x (by rw [hx]; exact J.c2)
      · rcases hy.ends J hA hD hS with ⟨-, h⟩ | ⟨-, h⟩
        · right; left; exact h
        · left; exact h
      · rcases hy'.ends J hA hD hS with ⟨-, h⟩ | ⟨-, h⟩
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
