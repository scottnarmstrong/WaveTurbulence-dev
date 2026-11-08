/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov2

/-! # C1b1 MK-PHASE1 (14): the survivor being removed is matched (coverage, part 3)

At a state with the bookkeeping `BookE`, a survivor `E i` that is not dartless (its earlier neighbours may be gone) is
present through the renaming `ancInv h` (`BookE.surv_match`): every group dart of `E i` is present (a killed one would
lie in the piece of `E (i-1)`, hence be a dart of `E (i-1)` with both ends in `E (i-1) ∩ E i`, a loop), and every atom
of `E i` descends from a present atom (`cov`). This is the "intact or pending re-cut joint" status without a separate
invariant: the only atom of `E i` that may be represented by a remnant is its shared joint with `E (i-1)`.

`survDesig`: the designation of the joint pairs of `E i` (C.first/second at a hinge joint `u` is the pair of the first
survivor with joint `u` (`jointPair`, 75-F1); if that survivor is `E (i-1)`, the pair of `E i` is its complement among
the four darts at `u`). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- Every atom of an object carries a dart of the object's group. -/
theorem exists_group_dart {M₀ : Molecule V D₀} (U : Object M₀) {a : V} (ha : a ∈ U.atoms) :
    ∃ z, M₀.atom z = a ∧ M₀.InGroup U.atoms z := by
  have hb := (object_oh U).basic
  have hpos : 0 < M₀.degIn U.atoms a := by
    by_cases h1 : a = U.upper
    · subst h1; rcases hb.2.2.2.2.2.1 with e | e <;> omega
    · by_cases h2 : a = U.lower
      · subst h2; rw [← hb.2.2.2.2.1]; rcases hb.2.2.2.2.2.1 with e | e <;> omega
      · rw [hb.2.2.2.2.2.2 a ha h1 h2]; omega
  obtain ⟨z, hz⟩ := Finset.card_pos.1 hpos
  rw [Finset.mem_filter] at hz
  exact ⟨z, (Mole.mem_dartsAt _ _ _).1 hz.1, hz.2⟩

/-- A dart of `M₀` that is a dart of two objects meeting in one atom is a loop: impossible. -/
theorem not_two_groups {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHypL Rn M₀) {P Q : Object M₀}
    (hcard : (P.atoms ∩ Q.atoms).card = 1) {z : D₀} (hP : M₀.InGroup P.atoms z) (hQ : M₀.InGroup Q.atoms z) : False := by
  have e := Finset.card_le_one.1 (le_of_eq hcard) _ (Finset.mem_inter.2 ⟨hP.1, hQ.1⟩) _
    (Finset.mem_inter.2 ⟨hP.2, hQ.2⟩)
  exact hS.noloop z e

section matching
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- **The group darts of a survivor still present are all present.** -/
theorem BookE.surv_lift {Rn : ℕ} (hS : SubHypL Rn M₀) {h : HSt V D₀} {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    {i : Fin m} (hi : ¬ Dartless (E i) h) :
    ∀ z : D₀, M₀.InGroup (E i).atoms z → ∃ y : h.s.D, h.s.down y = z := by
  intro z hz
  by_contra hno
  push Not at hno
  obtain ⟨p, hp, hk⟩ := B.geom.pres z hno
  obtain ⟨j, -, hpj, -, hcard⟩ := B.piece_meet hsd hchain hi hz.1 hp hk.1
  have hM₀ : M₀.IsMolecule := hS.isMolecule
  have hcd : (E j).ContainsDart z := by
    by_cases hjt : M₀.atom z = p.1.upper ∨ M₀.atom z = p.1.lower
    · have hq : p ∈ qs := by
        rcases List.mem_append.1 hp with hq | hq
        · exact hq
        · exact absurd hz.1 (Finset.disjoint_left.1 (hsd p.1 (B.hps p hq).1 i) hk.1)
      obtain ⟨-, hcd4, -⟩ := B.hqs p hq
      rw [← hpj]
      rcases hk.2 hjt with e | e | e | e <;> rw [e]
      · exact hcd4.1
      · exact hcd4.2.1
      · exact hcd4.2.2.1
      · exact hcd4.2.2.2
    · push Not at hjt
      rw [← hpj]
      exact containsDart_of_interior p.1 (fun b hb => Mole.deg_le_four M₀ hM₀ hb) (object_oh p.1).basic.2.2.2.2.2.2
        hk.1 hjt.1 hjt.2
  exact not_two_groups hS hcard (containsDart_inGroup _ hcd) hz

/-- **Every atom of a survivor still present descends from a present atom.** -/
theorem BookE.surv_cov {Rn : ℕ} (hS : SubHypL Rn M₀) {h : HSt V D₀} {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    {i : Fin m} (hi : ¬ Dartless (E i) h) {a : V} (ha : a ∈ (E i).atoms) : ∃ c ∈ h.s.M.atoms, h.anc c = a := by
  have hM₀ : M₀.IsMolecule := hS.isMolecule
  obtain ⟨z, hza, hzg⟩ := exists_group_dart (E i) ha
  obtain ⟨y, hy⟩ := B.surv_lift hS hsd hchain hi z hzg
  have hnint : ∀ p ∈ qs ++ ps, ¬ PieceInt p.1 a := by
    rintro p hp ⟨hpa, hn1, hn2⟩
    obtain ⟨j, -, hpj, -, hcard⟩ := B.piece_meet hsd hchain hi ha hp hpa
    rw [hpj] at hpa hn1 hn2
    have hcd : (E j).ContainsDart z :=
      containsDart_of_interior (E j) (fun b hb => Mole.deg_le_four M₀ hM₀ hb) (object_oh (E j)).basic.2.2.2.2.2.2
        (hza ▸ hpa) (hza ▸ hn1) (hza ▸ hn2)
    exact not_two_groups hS hcard (containsDart_inGroup _ hcd) hzg
  rcases B.geom.cov a (objectAtoms_sub (E i) ha) hnint with hc | hk
  · exact hc
  · exfalso
    obtain ⟨p, hp, hkz⟩ := hk z hza
    exact B.geom.live y p hp (hy ▸ hkz)

/-- **A survivor still present is matched through `ancInv`.** -/
theorem BookE.surv_match {Rn : ℕ} (hS : SubHypL Rn M₀) {h : HSt V D₀} {ps qs : List (Object M₀ × Quad D₀)}
    (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    {i : Fin m} (hi : ¬ Dartless (E i) h) : MatchA h (E i) (ancInv h) := by
  have hex := fun a (ha : a ∈ (E i).atoms) => B.surv_cov hS hsd hchain hi ha
  have hspec : ∀ a ∈ (E i).atoms, ancInv h a ∈ h.s.M.atoms ∧ h.anc (ancInv h a) = a := by
    intro a ha
    have hs := hex a ha
    simp only [ancInv, dite_eq_left hs]
    exact Classical.choose_spec hs
  refine ⟨fun a ha b hb e => ?_, fun a ha => (hspec a ha).1, fun a ha => (hspec a ha).2,
    B.surv_lift hS hsd hchain hi⟩
  have := congrArg h.anc e
  rwa [(hspec a ha).2, (hspec b hb).2] at this

end matching

section desig
variable {M₀ : Molecule V D₀} {m : ℕ}

/-- Four distinct darts at an atom of degree at most `4` are all its darts. -/
theorem dartsAt_eq_four {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {u : V} (hd : M.deg u ≤ 4)
    {a b c e : D} (ha : M.atom a = u) (hb : M.atom b = u) (hc : M.atom c = u) (he : M.atom e = u)
    (hab : a ≠ b) (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) (hce : c ≠ e) :
    M.dartsAt u = {a, b, c, e} := by
  have hsub : ({a, b, c, e} : Finset D) ⊆ M.dartsAt u := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact (Mole.mem_dartsAt _ _ _).2 (by assumption)
  have hcard : ({a, b, c, e} : Finset D).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, hae]), Finset.card_insert_of_notMem (by simp [hbc, hbe]),
      Finset.card_insert_of_notMem (by simp [hce]), Finset.card_singleton]
  have hdeg : (M.dartsAt u).card ≤ 4 := hd
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- **The designation of a survivor's joint pair** (75-F1): at a hinge joint `u` of `E i`, the chosen pair is the pair
of the first survivor with joint `u` (`jointPair`, at `u` by `hingeSG`); for `E i` itself it is its own pair, for
`E (i-1)` (the pending re-cut joint) the pair of `E i` is its complement among the four darts at `u`. -/
theorem survDesig {Rn : ℕ} (hS : SubHypL Rn M₀) (C : CollData M₀) (E : Fin m → Object M₀) {L γ η : ℝ} {d : ℕ}
    {w : Mom d} {κ : D₀ → (Fin d → ℤ)} (hobl : SubproOblGMK C E L γ η w κ)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    (i : Fin m) {u : V} (hu : u = (E i).upper ∨ u = (E i).lower) {p q : D₀}
    (hpq : SourceObjectJointPair (E i) u p q) : Desig C u (q, p) := by
  intro hmem
  have hM₀ : M₀.IsMolecule := hS.isMolecule
  obtain ⟨f, s, hf1, hs1, hT, -⟩ := hobl.hingeSG u hmem
  obtain ⟨haf, has, -, hout⟩ := hT
  -- the first survivor with joint `u`
  set S : Finset (Fin m) := Finset.univ.filter fun j => u = (E j).upper ∨ u = (E j).lower with hSdef
  have hSne : S.Nonempty := ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩⟩
  set j₀ := S.min' hSne
  have hj₀S : j₀ ∈ S := S.min'_mem hSne
  have hj₀u : u = (E j₀).upper ∨ u = (E j₀).lower := (Finset.mem_filter.1 hj₀S).2
  have hfirst : SurvFirstJointM E j₀ u := ⟨hj₀u, fun j hj hju =>
    absurd (S.min'_le j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hju⟩)) (not_le.2 hj)⟩
  have hj₀i : j₀ ≤ i := S.min'_le i (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu⟩)
  obtain ⟨f', s', hf1', hs1', hcf, hcs⟩ := hobl.jointPair j₀ u hfirst
  rw [hf1] at hf1'; rw [hs1] at hs1'
  cases hf1'; cases hs1'
  refine ⟨f, s, hf1, hs1, ?_⟩
  rcases eq_or_lt_of_le hj₀i with he | hlt
  · rw [he] at hcf hcs
    left
    exact pair_set_eq (E i) hpq hu hcf hcs haf has hout
  · right
    have hne : j₀ ≠ i := ne_of_lt hlt
    have hu0 : u ∈ (E j₀).atoms := object_mem_of_joint (E j₀) hj₀u
    have hui : u ∈ (E i).atoms := object_mem_of_joint (E i) hu
    have hnd : ¬ Disjoint (E j₀).atoms (E i).atoms := fun hdis => Finset.disjoint_left.1 hdis hu0 hui
    have hcard := (hchain j₀ i hne hnd).2
    have hgp := containsDart_inGroup _ hpq.2.2.1
    have hgq := containsDart_inGroup _ hpq.2.2.2.1
    have hgf := containsDart_inGroup _ hcf
    have hgs := containsDart_inGroup _ hcs
    have hpq' : p ≠ q := fun e => by have h1 := hpq.2.2.2.2.1; have h2 := hpq.2.2.2.2.2; rw [e] at h1; simp_all
    have hfs : f ≠ s := fun e => hout (by rw [e])
    have hpf : p ≠ f := fun e => not_two_groups hS hcard (e ▸ hgf) hgp
    have hps : p ≠ s := fun e => not_two_groups hS hcard (e ▸ hgs) hgp
    have hqf : q ≠ f := fun e => not_two_groups hS hcard (e ▸ hgf) hgq
    have hqs : q ≠ s := fun e => not_two_groups hS hcard (e ▸ hgs) hgq
    have hD := dartsAt_eq_four (Mole.deg_le_four M₀ hM₀ (object_mem_of_joint (E i) hu |> objectAtoms_sub (E i)))
      haf has hpq.1 hpq.2.1 hfs hpf.symm hqf.symm hps.symm hqs.symm hpq'
    rw [hD]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_sdiff, Finset.coe_insert, Finset.coe_singleton]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨Or.inr (Or.inr (Or.inr rfl)), by rintro (e | e) <;> [exact hqf e; exact hqs e]⟩
      · exact ⟨Or.inr (Or.inr (Or.inl rfl)), by rintro (e | e) <;> [exact hpf e; exact hps e]⟩
    · rintro ⟨hx, hxn⟩
      rcases hx with rfl | rfl | rfl | rfl
      · exact absurd (Or.inl rfl) hxn
      · exact absurd (Or.inr rfl) hxn
      · exact Or.inr rfl
      · exact Or.inl rfl

end desig

end WaveTurbulence.Flower.FinalMKPhase1
