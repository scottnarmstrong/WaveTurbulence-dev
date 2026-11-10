/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriBase
public import WaveTurbulence.Foundations.FinalCount.RestrictRank
/-! Triangles, part 2 (FINALCOUNT-G2): after the three cuts the triangle `T = {t 0, t 1, t 2}` is a union of
components of `m3` (a 3-cycle, all atoms of degree `2`), `kept` is the molecule on the other atoms, and the
bookkeeping `|kept| = |M|`, `E(kept) = E(M) - 3`, `F(m3) = F(kept) + 1`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- The atoms outside the triangle. -/
def TP : V → Prop := fun a => ∀ j : Fin 3, a ≠ T.t j

instance : DecidablePred T.TP := fun a => by unfold TP; infer_instance

theorem not_TP_iff (a : V) : ¬ T.TP a ↔ ∃ j, a = T.t j := by
  unfold TP; push Not; rfl

theorem m3_dartsAt_t (j : Fin 3) : T.m3.dartsAt (T.t j) = {T.a j, T.b j} := by
  ext x
  rw [mem_dartsAt, T.m3_atom_eq_t]
  simp

theorem m3_deg_t (j : Fin 3) : T.m3.deg (T.t j) = 2 := by
  unfold Molecule.deg
  rw [T.m3_dartsAt_t, Finset.card_pair]
  intro e
  have h1 := T.atom_a j; have h2 := T.atom_b j
  have := T.out_a j; have := T.out_b j
  simp_all

theorem m3_mate (x : D) : T.m3.mate x = M.mate x := rfl
theorem m3_out (x : D) : T.m3.out x = M.out x := rfl

theorem pclosed : PClosed T.m3 T.TP := by
  intro x hx j hj
  rcases (T.m3_atom_eq_t _ j).1 hj with h | h
  · rw [T.m3_mate] at h
    have e : x = T.b (j - 1) := by
      have := congrArg M.mate h
      rw [M.mate_mate] at this
      rw [this]; have := T.mate_a (j - 1); simpa using this
    exact hx (j - 1) (T.m3_atom_tri x (j - 1) (Or.inr e))
  · rw [T.m3_mate] at h
    have e : x = T.a (j + 1) := by
      have := congrArg M.mate h
      rw [M.mate_mate] at this
      rw [this]; exact T.mate_b j
    exact hx (j + 1) (T.m3_atom_tri x (j + 1) (Or.inl e))

/-- The molecule on the atoms outside the triangle. -/
def kept : Molecule V (PDart T.m3 T.TP) := restrictP T.m3 T.TP T.pclosed

/-- The triangle component. -/
def tcomp : Molecule V (PDart T.m3 (fun a => ¬ T.TP a)) := restrictP T.m3 (fun a => ¬ T.TP a) T.pclosed.neg

theorem tcomp_atoms : T.tcomp.atoms = Finset.univ.image T.t := by
  ext a
  unfold tcomp restrictP
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, TP, not_forall, not_not]
  rw [T.m3_atoms]
  constructor
  · rintro ⟨h, j, rfl⟩; exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    refine ⟨?_, j, rfl⟩
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (T.t_mem j)))

theorem tcomp_atoms_card : T.tcomp.atoms.card = 3 := by
  rw [T.tcomp_atoms, Finset.card_image_of_injective _ T.t_inj]; simp

theorem tcomp_deg (j : Fin 3) : T.tcomp.deg (T.t j) = 2 := by
  exact (restrictP_deg T.m3 (fun a => ¬ T.TP a) T.pclosed.neg (a := T.t j) ((T.not_TP_iff _).2 ⟨j, rfl⟩)).trans (T.m3_deg_t j)

theorem m3_atoms_card : T.m3.atoms.card = M.atoms.card + 3 := by
  rw [m3_atoms]
  have h0 : T.f 0 ∉ M.atoms := T.f_fresh 0
  have h1 : T.f 1 ∉ insert (T.f 0) M.atoms := by
    rw [Finset.mem_insert]; rintro (h | h)
    · exact T.f_ne (by decide) h
    · exact T.f_fresh 1 h
  have h2 : T.f 2 ∉ insert (T.f 1) (insert (T.f 0) M.atoms) := by
    rw [Finset.mem_insert, Finset.mem_insert]; rintro (h | h | h)
    · exact T.f_ne (by decide) h
    · exact T.f_ne (by decide) h
    · exact T.f_fresh 2 h
  rw [Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h0]

theorem kept_atoms_card : T.kept.atoms.card = M.atoms.card := by
  have h := restrictP_atoms_card T.m3 T.TP T.pclosed
  have h2 := T.tcomp_atoms_card
  have h3 := T.m3_atoms_card
  change T.kept.atoms.card + T.tcomp.atoms.card = T.m3.atoms.card at h
  omega

theorem tcomp_bonds_card : T.tcomp.bonds.card = 3 := by
  unfold Molecule.bonds
  show (Finset.univ.filter fun x : PDart T.m3 (fun a => ¬ T.TP a) => T.m3.out x.1 = true).card = 3
  rw [card_filter_subtype' (fun x : D => ¬ T.TP (T.m3.atom x)) (fun x => T.m3.out x = true)]
  have : (Finset.univ.filter fun x : D => ¬ T.TP (T.m3.atom x) ∧ T.m3.out x = true) =
      Finset.univ.image T.b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hj, ho⟩
      obtain ⟨j, hj⟩ := (T.not_TP_iff _).1 hj
      rcases (T.m3_atom_eq_t x j).1 hj with h | h
      · exfalso; subst h; rw [T.m3_out, T.out_a] at ho; exact Bool.false_ne_true ho
      · exact ⟨j, h.symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨(T.not_TP_iff _).2 ⟨j, T.m3_atom_tri _ j (Or.inr rfl)⟩, by rw [T.m3_out]; exact T.out_b j⟩
  rw [this, Finset.card_image_of_injective]
  · simp
  · intro i j e
    apply T.t_inj
    rw [← T.atom_b i, ← T.atom_b j, e]

theorem kept_bonds_card : T.kept.bonds.card + 3 = M.bonds.card := by
  have h := restrictP_bonds_card T.m3 T.TP T.pclosed
  change T.kept.bonds.card + T.tcomp.bonds.card = T.m3.bonds.card at h
  rw [T.tcomp_bonds_card] at h
  exact h

theorem tcomp_numComponents : T.tcomp.numComponents = 1 := by
  classical
  unfold Molecule.numComponents
  rw [Nat.card_eq_one_iff_unique]
  have hat : ∀ a : T.tcomp.atoms, ∃ j, a.1 = T.t j := by
    intro a
    have : (a : V) ∈ Finset.univ.image T.t := T.tcomp_atoms ▸ a.2
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp this
    exact ⟨j, hj.symm⟩
  have adj : ∀ j : Fin 3, T.tcomp.Adj (T.t j) (T.t (j + 1)) := by
    intro j
    refine ⟨(⟨T.b j, (T.not_TP_iff _).2 ⟨j, T.m3_atom_tri _ j (Or.inr rfl)⟩⟩ : PDart T.m3 (fun a => ¬ T.TP a)), ?_, ?_⟩
    · exact T.m3_atom_tri _ j (Or.inr rfl)
    · show T.m3.atom (M.mate (T.b j)) = _
      rw [T.mate_b]; exact T.m3_atom_tri _ _ (Or.inl rfl)
  have mem : ∀ j, T.t j ∈ T.tcomp.atoms := fun j => by rw [T.tcomp_atoms]; simp
  have lk : ∀ j : Fin 3, Quot.mk (fun u w : T.tcomp.atoms => T.tcomp.Adj u.1 w.1) (⟨T.t j, mem j⟩ : T.tcomp.atoms) =
      Quot.mk _ (⟨T.t (j + 1), mem (j + 1)⟩ : T.tcomp.atoms) := fun j => Quot.sound (adj j)
  have key : ∀ j, Quot.mk (fun u w : T.tcomp.atoms => T.tcomp.Adj u.1 w.1) (⟨T.t j, mem j⟩ : T.tcomp.atoms) =
      Quot.mk _ (⟨T.t 0, mem 0⟩ : T.tcomp.atoms) := by
    intro j
    fin_cases j
    · rfl
    · exact (lk 0).symm
    · exact ((lk 0).trans (lk 1)).symm
  refine ⟨⟨fun q q' => ?_⟩, ⟨Quot.mk _ ⟨T.t 0, mem 0⟩⟩⟩
  induction q using Quot.ind with
  | _ a =>
  induction q' using Quot.ind with
  | _ b =>
  obtain ⟨i, hi⟩ := hat a
  obtain ⟨j, hj⟩ := hat b
  have ea : a = ⟨T.t i, mem i⟩ := Subtype.ext hi
  have eb : b = ⟨T.t j, mem j⟩ := Subtype.ext hj
  rw [ea, eb, key i, key j]

end TriData
end WaveTurbulence.FinalCount
