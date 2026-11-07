/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Erase
public import WaveTurbulence.Foundations.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.FinalCount.G3Flat
/-! **FINALCOUNT-G3: the erase-atom step** `Step5` (TARGET Remark `remtame` case (ii), L2152; remtame2 L2218).

A degree-`4` `ε`-atom `v` is *erasable* (case (ii)) if every component of `M - v` contains at least two atoms adjacent
to `v` (i.e. "no component contains exactly one atom adjacent to `v`").  Erasing removes `v` and its four bonds and
assigns no new `α`- or `β`-atoms; the neighbours of `v` lose darts and become imperfect (`contrib` increases by the
number of removed bonds).  The invariant `Good` is preserved with `R` replaced by `R + 2`
(`4V - 2E - 2(V_α + V_β)` increases by `4`, TARGET `finalmol` L2187 is false once erasures occur: E9). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

/-- The state after removing `v` and its bonds (before the isolated former neighbours are deleted). -/
def St.erase0 (s : St.{u} V D₀) (v : V) : St.{u} V D₀ where
  D := EDart s.M v
  M := eraseAt s.M v
  down := fun x => s.down x.1
  cls := s.cls

/-- The atoms kept by an erasure: those that still carry a dart.  A former neighbour of `v` all of whose bonds went to `v`
(a *ghost neighbour*) is isolated after the erasure and is deleted together with `v`. -/
def keepE (s : St.{u} V D₀) (v : V) : V → Prop := fun a => 1 ≤ (eraseAt s.M v).deg a

theorem keepE_closed (s : St.{u} V D₀) (v : V) : PClosed (eraseAt s.M v) (keepE s v) := by
  intro x _
  show 1 ≤ (eraseAt s.M v).deg _
  unfold Molecule.deg
  exact Finset.card_pos.2 ⟨(eraseAt s.M v).mate x, by simp [Molecule.dartsAt]⟩

/-- **The state after erasing `v`** (R27): `v` and its bonds are removed, no `α`- or `β`-atom is created, and the neighbours of
`v` that became isolated are deleted. -/
noncomputable def St.eraseSt (s : St.{u} V D₀) (v : V) : St.{u} V D₀ := (s.erase0 v).delSt (keepE s v) (keepE_closed s v)

/-- **Step 5** (R27, TARGET Remark `remtame`): erase a (zero-gap tame) `ε`-atom `v` of degree `≥ 3`.  The tameness (zero gap of
every triple at `v`) is a condition of the run (`HStep5`), not of the graph step. -/
inductive Step5 : St.{u} V D₀ → St.{u} V D₀ → Prop
  | erase (s : St.{u} V D₀) (v : V) (hv : v ∈ s.M.atoms) (hd : 3 ≤ s.M.deg v) (hε : s.cls v = .eps) :
      Step5 s (s.eraseSt v)

section inv
variable {s : St.{u} V D₀} {R : ℕ} {v : V}

theorem mult_pos_adj {a : V} (h : 0 < mult s.M v a) : s.M.Adj v a := by
  unfold mult at h
  obtain ⟨x, hx⟩ := Finset.card_pos.1 h
  simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  exact ⟨s.M.mate x, hx.2, by rw [s.M.mate_mate]; exact hx.1⟩

theorem adj_mult_pos {a : V} (h : s.M.Adj v a) : 0 < mult s.M v a := by
  obtain ⟨z, h1, h2⟩ := h
  unfold mult
  refine Finset.card_pos.2 ⟨s.M.mate z, ?_⟩
  simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨h2, by rw [s.M.mate_mate]; exact h1⟩

theorem contrib_erase0 {a : V} (hav : a ≠ v) : contrib (s.erase0 v) a = contrib s a + mult s.M v a := by
  unfold contrib
  have := eraseAt_dartsAt_card s.M v hav
  show (s.cls a).base - (((eraseAt s.M v).deg a : ℕ) : ℤ) = _
  omega

theorem CompBeta.erase0 (hg : Good R s) (hC : CompBeta s) : CompBeta (s.erase0 v) := by
  have hnl := hg.1.noloop
  intro a ha hga
  have haM : a ∈ s.M.atoms := Finset.mem_of_mem_erase ha
  have hav : a ≠ v := Finset.ne_of_mem_erase ha
  by_cases hsv : s.M.SameComponent a v
  · obtain ⟨w, hw, haw⟩ := comp_to_v hnl hav hsv
    have hwv : w ≠ v := by
      rintro rfl
      obtain ⟨z, h1, h2⟩ := hw
      exact hnl z (h1.trans h2.symm)
    have hwM : w ∈ s.M.atoms := by obtain ⟨z, h1, h2⟩ := hw; exact h2 ▸ s.M.atom_mem _
    refine ⟨w, Finset.mem_erase.2 ⟨hwv, hwM⟩, haw, Or.inr ?_⟩
    rw [contrib_erase0 hwv]
    have := adj_mult_pos (s := s) hw
    have := hg.contrib_nonneg hwM
    omega
  · obtain ⟨b, hb, hab, hprop⟩ := hC a haM hga
    have hbv : b ≠ v := fun e => hsv (e ▸ hab)
    have hm : mult s.M v b = 0 := by
      by_contra hm
      have := mult_pos_adj (s := s) (Nat.pos_of_ne_zero hm)
      exact hsv (Relation.EqvGen.trans _ _ _ hab
        (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ this)))
    refine ⟨b, Finset.mem_erase.2 ⟨hbv, hb⟩, sc_avoid hab hsv, ?_⟩
    rcases hprop with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [contrib_erase0 hbv, hm]; simpa using h

theorem CompBeta.eraseSt (hg : Good R s) (hC : CompBeta s) : CompBeta (s.eraseSt v) :=
  (CompBeta.erase0 hg hC).delSt _ (keepE_closed s v)

theorem eraseSt_atoms : (s.eraseSt v).M.atoms = (s.M.atoms.erase v).filter (keepE s v) := rfl

theorem eraseSt_deg {a : V} (ha : keepE s v a) : (s.eraseSt v).M.deg a = (eraseAt s.M v).deg a :=
  restrictP_deg (eraseAt s.M v) (keepE s v) (keepE_closed s v) ha

theorem eraseSt_cls (a : V) : (s.eraseSt v).cls a = s.cls a := rfl

theorem base_nonneg (c : Cls) : 0 ≤ c.base := by cases c <;> simp [Cls.base]

/-- **`Good` after an erasure** (R27): the invariant `4V - 2E - 2(V_α + V_β)` rises by `2 deg v - 4`; the deleted ghost neighbours
lower it again, so the new index `R'` is at most `R + (deg v - 2)`. -/
theorem Good.erase1 (hg : Good R s) (hv : v ∈ s.M.atoms) (hε : s.cls v = .eps) :
    ∃ R' : ℕ, (R' : ℤ) ≤ (R : ℤ) + (s.M.deg v : ℤ) - 2 ∧ Good R' (s.eraseSt v) := by
  have hnl := hg.1.noloop
  set s' := s.eraseSt v with hs'
  have hat : s'.M.atoms = (s.M.atoms.erase v).filter (keepE s v) := rfl
  have hdeg' : ∀ a ∈ s'.M.atoms, s'.M.deg a = (eraseAt s.M v).deg a := fun a ha =>
    eraseSt_deg (Finset.mem_filter.1 (hat ▸ ha)).2
  have hmem : ∀ a ∈ s'.M.atoms, a ∈ s.M.atoms ∧ a ≠ v ∧ 1 ≤ (eraseAt s.M v).deg a := fun a ha => by
    have := Finset.mem_filter.1 (hat ▸ ha)
    exact ⟨Finset.mem_of_mem_erase this.1, Finset.ne_of_mem_erase this.1, this.2⟩
  have hdle : ∀ a ∈ s'.M.atoms, s'.M.deg a ≤ s.M.deg a := fun a ha => by
    obtain ⟨-, hav, -⟩ := hmem a ha
    have := eraseAt_dartsAt_card s.M v hav
    rw [hdeg' a ha]; omega
  -- the pieces of the invariant
  have hcore : Inv 0 s' ∨ True := Or.inr trivial
  -- the sum of the bases
  have hF1 : ∑ a ∈ s.M.atoms.erase v, (s.cls a).base = Fintype.card s.D + 2 * (R : ℤ) - 4 := by
    have h1 := Finset.add_sum_erase s.M.atoms (fun a => (s.cls a).base) hv
    have h3 := hg.1.phi
    have h6 : (s.cls v).base = 4 := by rw [hε]; rfl
    linarith
  have hF2 : (Fintype.card (EDart s.M v) : ℤ) + 2 * (s.M.deg v : ℤ) = Fintype.card s.D := by
    exact_mod_cast card_edart (M := s.M) (v := v) hnl
  have hF3 : (Fintype.card s'.D : ℤ) = Fintype.card (EDart s.M v) := by
    have h := card_pdart (eraseAt s.M v) (keepE s v)
    have h0 : ∑ a ∈ (eraseAt s.M v).atoms.filter (fun a => ¬ keepE s v a), (eraseAt s.M v).deg a = 0 := by
      refine Finset.sum_eq_zero fun a ha => ?_
      have := (Finset.mem_filter.1 ha).2
      unfold keepE at this; omega
    rw [h0] at h
    show (Fintype.card (PDart (eraseAt s.M v) (keepE s v)) : ℤ) = _
    exact_mod_cast (by omega : Fintype.card (PDart (eraseAt s.M v) (keepE s v)) = Fintype.card (EDart s.M v))
  set B : ℤ := ∑ a ∈ (s.M.atoms.erase v).filter (fun a => ¬ keepE s v a), (s.cls a).base with hB
  have hF4 : ∑ a ∈ s'.M.atoms, (s.cls a).base + B = ∑ a ∈ s.M.atoms.erase v, (s.cls a).base := by
    rw [hat]; exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun a _ => base_nonneg _
  -- `Z = ∑ base - |D'| ≥ 0`
  have hZnn : 0 ≤ ∑ a ∈ s'.M.atoms, (s.cls a).base - Fintype.card s'.D := by
    have hsd := sum_deg_eq s'.M
    have : (Fintype.card s'.D : ℤ) = ∑ a ∈ s'.M.atoms, (s'.M.deg a : ℤ) := by exact_mod_cast hsd.symm
    rw [this, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg fun a ha => ?_
    obtain ⟨haM, -, -⟩ := hmem a ha
    have hle := deg_le_four s.M (hg.1.bounds a haM)
    have h1 := hdle a ha
    by_cases he : s.cls a = .eps
    · rw [he]; simp only [Cls.base]; omega
    · have := (hg.1.ab a haM he).1
      rcases hc : s.cls a with _ | _ | _ | _
      · exact absurd hc he
      · simp only [Cls.base]; omega
      · simp only [Cls.base]; omega
      · exact absurd hc (hg.2 a haM)
  -- parity
  have hZev : Even (∑ a ∈ s'.M.atoms, (s.cls a).base - Fintype.card s'.D) := by
    have h1 : Even (∑ a ∈ s'.M.atoms, (s.cls a).base) :=
      Finset.even_sum _ fun a _ => Cls.even_base _
    have h2 : Even (Fintype.card s'.D : ℤ) := by
      have := card_darts_eq_two_bonds s'.M
      rw [this]; push_cast; exact even_two_mul _
    exact h1.sub h2
  obtain ⟨R'', hR''⟩ := hZev
  have hR''nn : 0 ≤ R'' := by omega
  refine ⟨R''.toNat, ?_, ?_⟩
  · have : (R''.toNat : ℤ) = R'' := Int.toNat_of_nonneg hR''nn
    omega
  · have hR : ((R''.toNat : ℕ) : ℤ) = R'' := Int.toNat_of_nonneg hR''nn
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro a ha
      obtain ⟨haM, hav, -⟩ := hmem a ha
      refine ⟨?_, ?_⟩
      · show (restrictP (eraseAt s.M v) (keepE s v) (keepE_closed s v)).outdeg a ≤ 2
        rw [restrictP_outdeg _ _ _ (Finset.mem_filter.1 (hat ▸ ha)).2]
        exact (eraseAt_outdeg_le a).trans (hg.1.bounds a haM).1
      · show (restrictP (eraseAt s.M v) (keepE s v) (keepE_closed s v)).indeg a ≤ 2
        rw [restrictP_indeg _ _ _ (Finset.mem_filter.1 (hat ▸ ha)).2]
        exact (eraseAt_indeg_le a).trans (hg.1.bounds a haM).2
    · intro a ha _
      obtain ⟨-, -, h1⟩ := hmem a ha
      rw [hdeg' a ha]; exact h1
    · intro a ha hc
      obtain ⟨haM, -, h1⟩ := hmem a ha
      have hab := hg.1.ab a haM hc
      refine ⟨(hdle a ha).trans hab.1, fun hgh => absurd hgh (hg.2 a haM), fun _ => ?_⟩
      rw [hdeg' a ha]; exact h1
    · show ∑ a ∈ s'.M.atoms, (s.cls a).base = _
      omega
    · intro x
      exact hg.1.noloop x.1.1
    · intro a ha
      exact hg.2 a (hmem a ha).1

/-- The original statement (degree `≥ 3`). -/
theorem Good.eraseSt (hg : Good R s) (hv : v ∈ s.M.atoms) (hd : 3 ≤ s.M.deg v) (hε : s.cls v = .eps) :
    ∃ R', R' ≤ R + (s.M.deg v - 2) ∧ Good R' (s.eraseSt v) := by
  obtain ⟨R', h1, h2⟩ := hg.erase1 hv hε
  exact ⟨R', by omega, h2⟩

end inv
end WaveTurbulence.FinalCountG3
