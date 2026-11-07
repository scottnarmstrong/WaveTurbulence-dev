/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Op5c
public import WaveTurbulence.Foundations.FinalCount.G3MapDec5
/-! **FINALCOUNT-G3 (R29 items 3, 5): `DamagedShape` / `DamagedDec` for the imperfect components after Operation 5.**
`G8Copy.DamagedShape`, `DamagedDec` are verbatim copies of G8-DCB's structures (`Damaged96Statement.lean`, `Prop96DamagedAt`).
The G8 field `classes` was weakened by G8-DCB #2 to `degPos`/`abLow` (our finding); `DamagedShapeW` is now an alias. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open Finset Classical
namespace WaveTurbulence.FinalCountG3.G8Copy
open WaveTurbulence

/-- The shape of an imperfect component (G8-DCB #2, verbatim: `degPos`, `abLow` replace `classes`). -/
structure DamagedShape {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) : Prop where
  nonempty : M.atoms.Nonempty
  isMolecule : M.IsMolecule
  noLoop : ∀ x, M.atom x ≠ M.atom (M.mate x)
  conn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b
  degPos : ∀ a ∈ M.atoms, 1 ≤ M.deg a
  abLow : ∀ a ∈ M.atoms, ¬ (cls a).IsEps → M.deg a ≤ 2
  noTriple : ∀ a b, M.bondsBetween a b ≤ 2
  imperf : ∃ a ∈ M.atoms, ((cls a).IsEps ∧ M.deg a ≠ 4) ∨ (¬ (cls a).IsEps ∧ M.deg a ≠ 2)

/-- The decoration hypothesis of DCB (G8-DCB, verbatim). -/
structure DamagedDec {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) {d : ℕ} (L γ η : ℝ) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop where
  labRange : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η)
  epsLG : ∀ κ, Adm κ → ∀ a ∈ M.atoms, (cls a).IsEps →
    ∀ x y, M.atom x = a → M.atom y = a → M.out x ≠ M.out y →
      L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖

/-- Kept for the consumers of session 11: now the same structure. -/
abbrev DamagedShapeW := @DamagedShape

end WaveTurbulence.FinalCountG3.G8Copy

namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {R : ℕ}

theorem bondsBetween_eraseSet_le {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (E : Finset V) (a b : V) :
    (eraseSet M E).bondsBetween a b ≤ M.bondsBetween a b := by
  unfold Molecule.bondsBetween
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx
  · intro x _ y _ e; exact Subtype.ext e

theorem noTriple_eraseSetSt {s : St.{u} V D₀} (hn : NoTripleBond s.M) (E : Finset V) :
    NoTripleBond (s.eraseSetSt E).M := by
  intro a ha b hb hab
  have ha' := Finset.mem_filter.1 ha
  have hb' := Finset.mem_filter.1 hb
  have h1 : (s.eraseSetSt E).M.bondsBetween a b = (eraseSet s.M E).bondsBetween a b :=
    restrictP_bondsBetween (eraseSet s.M E) (keepS s E) (keepS_closed s E) ha'.2 hb'.2
  rw [h1]
  exact lt_of_le_of_lt (bondsBetween_eraseSet_le _ _ _ _)
    (hn a (Finset.mem_sdiff.1 ha'.1).1 b (Finset.mem_sdiff.1 hb'.1).1 hab)

/-- `contrib ≠ 0` forces degree `≠ 4`. -/
theorem Good.deg_ne_four {s : St.{u} V D₀} (hg : Good R s) {b : V} (hb : b ∈ s.M.atoms) (hc : contrib s b ≠ 0) :
    s.M.deg b ≠ 4 := by
  intro h4
  unfold contrib at hc
  by_cases he : s.cls b = .eps
  · rw [he] at hc; simp [Cls.base, h4] at hc
  · have := (hg.1.ab b hb he).1
    omega

/-- **`DamagedShape` (true form) of an imperfect component** of any state satisfying `Good` and `NoTripleBond`. -/
theorem Good.damagedShape {s : St.{u} V D₀} (hg : Good R s) (hn : NoTripleBond s.M) {a₀ : V} (ha₀ : a₀ ∈ s.M.atoms)
    (himp : ∃ b ∈ s.M.atoms, s.M.SameComponent a₀ b ∧ contrib s b ≠ 0) :
    G8Copy.DamagedShapeW (compMol s.M a₀) (fun a => toCls (s.cls a)) where
  nonempty := ⟨a₀, (mem_compMol _ _).2 ⟨ha₀, Relation.EqvGen.refl _⟩⟩
  isMolecule := by
    refine ⟨fun a ha => ?_, fun v hv => ?_⟩
    · have h := (mem_compMol _ _).1 ha
      rw [compMol_outdeg _ _ h.2, compMol_indeg _ _ h.2]
      exact hg.1.bounds a h.1
    · obtain ⟨b, hb, hsb, hcb⟩ := himp
      have hv' := (mem_compMol _ _).1 hv
      have hbc : b ∈ (compMol s.M a₀).atoms := (mem_compMol _ _).2 ⟨hb, hsb⟩
      refine ⟨b, hbc, ?_, ?_⟩
      · exact restrictP_sc_of _ _ (compP_closed _ a₀)
          (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hv'.2) hsb) hv'.2
      · rw [compMol_deg _ _ hsb]; exact hg.deg_ne_four hb hcb
  noLoop := fun x => hg.1.noloop x.1
  conn := by
    intro a ha b hb
    have h1 := (mem_compMol _ _).1 ha
    have h2 := (mem_compMol _ _).1 hb
    exact restrictP_sc_of _ _ (compP_closed _ a₀)
      (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h1.2) h2.2) h1.2
  degPos := by
    intro a ha
    have h := (mem_compMol _ _).1 ha
    rw [compMol_deg _ _ h.2]
    by_cases he : s.cls a = .eps
    · exact hg.1.eps a h.1 he
    · exact (hg.1.ab a h.1 he).2.2 (hg.2 a h.1)
  abLow := by
    intro a ha hne
    have h := (mem_compMol _ _).1 ha
    rw [compMol_deg _ _ h.2]
    exact (hg.1.ab a h.1 (fun e => hne (toCls_isEps.2 e))).1
  noTriple := fun a b => (compMol_bondsBetween_le _ _ a b).trans (bondsBetween_le_two _ hg.1.noloop hn a b)
  imperf := by
    obtain ⟨b, hb, hsb, hcb⟩ := himp
    refine ⟨b, (mem_compMol _ _).2 ⟨hb, hsb⟩, ?_⟩
    rw [compMol_deg _ _ hsb]
    by_cases he : s.cls b = .eps
    · exact Or.inl ⟨toCls_isEps.2 he, hg.deg_ne_four hb hcb⟩
    · refine Or.inr ⟨fun h => he (toCls_isEps.1 h), ?_⟩
      have h1 := (hg.1.ab b hb he).1
      have h2 := (hg.1.ab b hb he).2.2 (hg.2 b hb)
      unfold contrib at hcb
      rcases hc : s.cls b with _ | _ | _ | _
      · exact absurd hc he
      · simp only [hc, Cls.base] at hcb; omega
      · simp only [hc, Cls.base] at hcb; omega
      · exact absurd hc (hg.2 b hb)


section dam
variable {L γ η : ℝ} {κ : D₀ → (Fin d → ℤ)} {Tm : V → Prop}

/-- **`DamagedDec` for every component of the state after Operation 5** (strict LG at the surviving `ε`-atoms, label ranges), for the
decorations of a family `AdmRun` each of which satisfies the conclusions of Prop 9.5 for the input state. -/
theorem Op5.damagedDec {h : HSt V D₀} {R : ℕ} (hg5 : Good R (h.op5 Tm).s) (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hC : ∀ κ, AdmRun κ → Prop95ConclN L γ η (0 : Mom d) κ Tm R h) (hne : ∃ κ, AdmRun κ) {a₀ : V} :
    G8Copy.DamagedDec (compMol (h.op5 Tm).s.M a₀) (fun a => toCls ((h.op5 Tm).s.cls a)) L γ η
      (compAdm (h.op5 Tm) a₀ AdmRun) where
  labRange := by
    intro a ha hα
    obtain ⟨κ₀, h₀⟩ := hne
    obtain ⟨ρ, kp, e⟩ := toCls_isAlpha.1 hα
    have hl := Op5.label (hC κ₀ h₀) a ((mem_compMol _ _).1 ha).1 ρ kp e
    rw [e]
    exact ⟨hl.2.1, hl.2.2⟩
  epsLG := by
    rintro κ' ⟨κ, hκ, rfl⟩ a ha hε x y hx hy hxy
    have haM := ((mem_compMol _ _).1 ha).1
    have hε' : (h.op5 Tm).s.cls a = .eps := toCls_isEps.1 hε
    have hx' : (h.op5 Tm).s.M.atom x.1 = a := hx
    have hy' : (h.op5 Tm).s.M.atom y.1 = a := hy
    have hlg : ∀ x' y' : (h.op5 Tm).s.D, (h.op5 Tm).s.M.atom x' = a → (h.op5 Tm).s.M.atom y' = a →
        (h.op5 Tm).s.M.out x' = false → (h.op5 Tm).s.M.out y' = true →
        L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) (κ ∘ (h.op5 Tm).s.down) x' -
          Molecule.kvec L (0 : Mom d) (κ ∘ (h.op5 Tm).s.down) y'‖ := by
      intro x' y' h1 h2 o1 o2
      exact lt_norm_of_LG (Op5.epsLG (hC κ hκ) a haM hε' x' y' h1 h2 o1 o2
        (fun e => hg5.1.noloop x' (by rw [← e, h1, h2])))
    have hxy' : (h.op5 Tm).s.M.out x.1 ≠ (h.op5 Tm).s.M.out y.1 := hxy
    cases hox : (h.op5 Tm).s.M.out x.1
    · have hoy : (h.op5 Tm).s.M.out y.1 = true := by
        cases hoy : (h.op5 Tm).s.M.out y.1
        · exact absurd (hox.trans hoy.symm) hxy'
        · rfl
      exact hlg x.1 y.1 hx' hy' hox hoy
    · have hoy : (h.op5 Tm).s.M.out y.1 = false := by
        cases hoy : (h.op5 Tm).s.M.out y.1
        · rfl
        · exact absurd (hox.trans hoy.symm) hxy'
      have := hlg y.1 x.1 hy' hx' hoy hox
      rw [kvec_comp, kvec_comp, norm_sub_rev]
      exact this

end dam
end WaveTurbulence.FinalCountG3
