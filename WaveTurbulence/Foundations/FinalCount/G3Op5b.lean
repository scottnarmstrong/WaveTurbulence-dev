/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Op5a
/-! **FINALCOUNT-G3 (R29 item 3): Operation 5 at the state level.**  `St.eraseSetSt s E` erases the set `E` of `ε`-atoms and deletes the
isolated former neighbours; `Good.erase_set`: `2R' + 4|E| ≤ 2R + tch(E)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

/-- The state after removing the set `E` and its bonds (before deleting the isolated former neighbours). -/
def St.eraseSet0 (s : St.{u} V D₀) (E : Finset V) : St.{u} V D₀ where
  D := EDartS s.M E
  M := eraseSet s.M E
  down := fun x => s.down x.1
  cls := s.cls

/-- The atoms kept by a set erasure: those that still carry a dart. -/
def keepS (s : St.{u} V D₀) (E : Finset V) : V → Prop := fun a => 1 ≤ (eraseSet s.M E).deg a

theorem keepS_closed (s : St.{u} V D₀) (E : Finset V) : PClosed (eraseSet s.M E) (keepS s E) := by
  intro x _
  show 1 ≤ (eraseSet s.M E).deg _
  unfold Molecule.deg
  exact Finset.card_pos.2 ⟨(eraseSet s.M E).mate x, by simp [Molecule.dartsAt]⟩

/-- **Operation 5**: erase the set `E` (a tame cluster or the union of the tame clusters); no `α`- or `β`-atom is created; former
neighbours that became isolated are deleted. -/
noncomputable def St.eraseSetSt (s : St.{u} V D₀) (E : Finset V) : St.{u} V D₀ :=
  (s.eraseSet0 E).delSt (keepS s E) (keepS_closed s E)

section inv
variable {s : St.{u} V D₀} {R : ℕ} {E : Finset V}

theorem eraseSetSt_atoms : (s.eraseSetSt E).M.atoms = (s.M.atoms \ E).filter (keepS s E) := rfl

theorem eraseSetSt_deg {a : V} (ha : keepS s E a) : (s.eraseSetSt E).M.deg a = (eraseSet s.M E).deg a :=
  restrictP_deg (eraseSet s.M E) (keepS s E) (keepS_closed s E) ha

theorem eraseSetSt_cls (a : V) : (s.eraseSetSt E).cls a = s.cls a := rfl

/-- **`Good` after erasing a set of `ε`-atoms** (R29 item 3): `2R' + 4|E| ≤ 2R + tch(E)`. -/
theorem Good.erase_set (hg : Good R s) (hE : ∀ v ∈ E, v ∈ s.M.atoms ∧ s.cls v = .eps) :
    ∃ R' : ℕ, 2 * (R' : ℤ) + 4 * (E.card : ℤ) ≤ 2 * (R : ℤ) + (tch s.M E : ℤ) ∧ Good R' (s.eraseSetSt E) := by
  have hnl := hg.1.noloop
  set s' := s.eraseSetSt E with hs'
  have hat : s'.M.atoms = (s.M.atoms \ E).filter (keepS s E) := rfl
  have hdeg' : ∀ a ∈ s'.M.atoms, s'.M.deg a = (eraseSet s.M E).deg a := fun a ha =>
    eraseSetSt_deg (Finset.mem_filter.1 (hat ▸ ha)).2
  have hmem : ∀ a ∈ s'.M.atoms, a ∈ s.M.atoms ∧ a ∉ E ∧ 1 ≤ (eraseSet s.M E).deg a := fun a ha => by
    have := Finset.mem_filter.1 (hat ▸ ha)
    exact ⟨(Finset.mem_sdiff.1 this.1).1, (Finset.mem_sdiff.1 this.1).2, this.2⟩
  have hdle : ∀ a ∈ s'.M.atoms, s'.M.deg a ≤ s.M.deg a := fun a ha => by
    obtain ⟨-, hav, -⟩ := hmem a ha
    have := eraseSet_deg_card s.M E hav
    rw [hdeg' a ha]; omega
  have hEsub : E ⊆ s.M.atoms := fun v hv => (hE v hv).1
  have hF1 : ∑ a ∈ s.M.atoms \ E, (s.cls a).base = Fintype.card s.D + 2 * (R : ℤ) - 4 * (E.card : ℤ) := by
    have h1 := Finset.sum_sdiff hEsub (f := fun a => (s.cls a).base)
    have h3 := hg.1.phi
    have h6 : ∑ a ∈ E, (s.cls a).base = 4 * (E.card : ℤ) := by
      rw [Finset.sum_congr rfl (fun a ha => by rw [(hE a ha).2]; rfl : ∀ a ∈ E, (s.cls a).base = 4)]
      simp [mul_comm]
    linarith
  have hF2 : (Fintype.card (EDartS s.M E) : ℤ) + (tch s.M E : ℤ) = Fintype.card s.D := by
    exact_mod_cast card_edartS s.M E
  have hF3 : (Fintype.card s'.D : ℤ) = Fintype.card (EDartS s.M E) := by
    have h := card_pdart (eraseSet s.M E) (keepS s E)
    have h0 : ∑ a ∈ (eraseSet s.M E).atoms.filter (fun a => ¬ keepS s E a), (eraseSet s.M E).deg a = 0 := by
      refine Finset.sum_eq_zero fun a ha => ?_
      have := (Finset.mem_filter.1 ha).2
      unfold keepS at this; omega
    rw [h0] at h
    show (Fintype.card (PDart (eraseSet s.M E) (keepS s E)) : ℤ) = _
    exact_mod_cast (by omega : Fintype.card (PDart (eraseSet s.M E) (keepS s E)) = Fintype.card (EDartS s.M E))
  set B : ℤ := ∑ a ∈ (s.M.atoms \ E).filter (fun a => ¬ keepS s E a), (s.cls a).base with hB
  have hF4 : ∑ a ∈ s'.M.atoms, (s.cls a).base + B = ∑ a ∈ s.M.atoms \ E, (s.cls a).base := by
    rw [hat]; exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hBnn : 0 ≤ B := Finset.sum_nonneg fun a _ => base_nonneg _
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
      · show (restrictP (eraseSet s.M E) (keepS s E) (keepS_closed s E)).outdeg a ≤ 2
        rw [restrictP_outdeg _ _ _ (Finset.mem_filter.1 (hat ▸ ha)).2]
        exact (eraseSet_outdeg_le s.M E a).trans (hg.1.bounds a haM).1
      · show (restrictP (eraseSet s.M E) (keepS s E) (keepS_closed s E)).indeg a ≤ 2
        rw [restrictP_indeg _ _ _ (Finset.mem_filter.1 (hat ▸ ha)).2]
        exact (eraseSet_indeg_le s.M E a).trans (hg.1.bounds a haM).2
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

end inv
end WaveTurbulence.FinalCountG3
