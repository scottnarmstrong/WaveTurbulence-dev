/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3InvCut
/-! **FINALCOUNT-G3**: preservation of `Inv` by the removal of a union of components. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

section restr
variable {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) (P : V → Prop) [DecidablePred P]
  (h : PClosed M P)

theorem restrictP_outdeg {a : V} (ha : P a) : (restrictP M P h).outdeg a = M.outdeg a := by
  unfold Molecule.outdeg
  rw [restrictP_dartsAt M P h ha]
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    have h3 := Finset.mem_subtype.mp h1
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at h3 ⊢
    exact ⟨h3, h2⟩
  · intro x _ y _ e; exact Subtype.ext e
  · intro y hy
    have hy' : M.atom y = a ∧ M.out y = true := by simpa [Molecule.dartsAt] using hy
    refine ⟨⟨y, hy'.1 ▸ ha⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_subtype.mpr (by simp [Molecule.dartsAt, hy'.1]), hy'.2⟩

theorem restrictP_indeg {a : V} (ha : P a) : (restrictP M P h).indeg a = M.indeg a := by
  unfold Molecule.indeg
  rw [restrictP_dartsAt M P h ha]
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    have h3 := Finset.mem_subtype.mp h1
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at h3 ⊢
    exact ⟨h3, h2⟩
  · intro x _ y _ e; exact Subtype.ext e
  · intro y hy
    have hy' : M.atom y = a ∧ M.out y = false := by simpa [Molecule.dartsAt] using hy
    refine ⟨⟨y, hy'.1 ▸ ha⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_subtype.mpr (by simp [Molecule.dartsAt, hy'.1]), hy'.2⟩

omit h in
theorem card_pdart :
    Fintype.card (PDart M P) + ∑ a ∈ M.atoms.filter (fun a => ¬ P a), M.deg a = Fintype.card D := by
  have h1 : Fintype.card (PDart M P) = (Finset.univ.filter fun x : D => P (M.atom x)).card := by
    rw [Fintype.card_subtype]
  have h2 : ∑ a ∈ M.atoms.filter (fun a => ¬ P a), M.deg a =
      (Finset.univ.filter fun x : D => ¬ P (M.atom x)).card := by
    have := Finset.card_eq_sum_card_fiberwise (f := M.atom)
      (s := (Finset.univ.filter fun x : D => ¬ P (M.atom x))) (t := M.atoms.filter (fun a => ¬ P a))
      (fun x hx => by
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨M.atom_mem x, hx⟩)
    rw [this]
    refine Finset.sum_congr rfl fun a ha => ?_
    simp only [Finset.mem_filter] at ha
    unfold Molecule.deg Molecule.dartsAt
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx; exact ⟨by rw [hx]; exact ha.2, hx⟩
    · intro hx; exact hx.2
  rw [h1, h2]
  exact Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun x : D => P (M.atom x)) |>.trans
    (by simp)

end restr

variable {s : St.{u} V D₀} {R : ℕ}

theorem Inv.delSt (hI : Inv R s) (P : V → Prop) [DecidablePred P] (h : PClosed s.M P)
    (hz : ∀ a ∈ s.M.atoms, ¬ P a → (s.cls a).base = s.M.deg a) :
    Inv R (s.delSt P h) := by
  have hat : (s.delSt P h).M.atoms = s.M.atoms.filter P := rfl
  have hdeg : ∀ a, P a → (s.delSt P h).M.deg a = s.M.deg a := fun a ha => restrictP_deg s.M P h ha
  have hcls : (s.delSt P h).cls = s.cls := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hat, Finset.mem_filter] at ha
    exact ⟨(restrictP_outdeg s.M P h ha.2).symm ▸ (hI.bounds a ha.1).1,
      (restrictP_indeg s.M P h ha.2).symm ▸ (hI.bounds a ha.1).2⟩
  · intro a ha hc
    rw [hat, Finset.mem_filter] at ha
    rw [hcls] at hc
    rw [hdeg a ha.2]; exact hI.eps a ha.1 hc
  · intro a ha hc
    rw [hat, Finset.mem_filter] at ha
    rw [hcls] at hc ⊢
    rw [hdeg a ha.2]; exact hI.ab a ha.1 hc
  · have h1 := card_pdart s.M P
    have h2 : ∑ a ∈ s.M.atoms, (s.cls a).base =
        ∑ a ∈ s.M.atoms.filter P, (s.cls a).base + ∑ a ∈ s.M.atoms.filter (fun a => ¬ P a), (s.cls a).base :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have h3 : ∑ a ∈ s.M.atoms.filter (fun a => ¬ P a), (s.cls a).base =
        ((∑ a ∈ s.M.atoms.filter (fun a => ¬ P a), s.M.deg a : ℕ) : ℤ) := by
      push_cast
      exact Finset.sum_congr rfl fun a ha => by
        simp only [Finset.mem_filter] at ha; exact hz a ha.1 ha.2
    show ∑ a ∈ s.M.atoms.filter P, (s.cls a).base = (Fintype.card (PDart s.M P) : ℤ) + 2 * R
    have := hI.phi
    have h1' : (Fintype.card (PDart s.M P) : ℤ) + ((∑ a ∈ s.M.atoms.filter (fun a => ¬ P a), s.M.deg a : ℕ) : ℤ)
        = Fintype.card s.D := by exact_mod_cast h1
    linarith
  · intro x
    exact hI.noloop x.1

end WaveTurbulence.FinalCountG3
