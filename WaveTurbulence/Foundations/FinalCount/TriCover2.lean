/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriCover
/-! Triangles, part 5 (FINALCOUNT-G2): the restriction of a decoration of `M` with triangle labels `z` is a
decoration of `kept` for the exact parameters `keptParams z`, and the exact-triple cover of `𝔈(M)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Set
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

theorem tri_vec (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (j : Fin 3) :
    M.dartSign (T.a j) • Molecule.kvec L w κ (T.a j) + M.dartSign (T.b j) • Molecule.kvec L w κ (T.b j) =
      triC L w (T.triZ κ) j := by
  rw [T.dartSign_a, T.dartSign_b]
  unfold Molecule.kvec triC triK triZ
  rw [T.kappa_a κ hκ]
  module

theorem tri_en (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (j : Fin 3) :
    M.dartSign (T.a j) * ‖Molecule.kvec L w κ (T.a j)‖ ^ 2 + M.dartSign (T.b j) * ‖Molecule.kvec L w κ (T.b j)‖ ^ 2 =
      triG L w (T.triZ κ) j := by
  rw [T.dartSign_a, T.dartSign_b]
  unfold Molecule.kvec triG triK triZ
  rw [T.kappa_a κ hκ]
  ring

theorem atom_cases {a : V} (ha : a ∈ T.kept.atoms) :
    (∃ j, a = T.f j) ∨ (a ∈ M.atoms ∧ T.TP a) := by
  have ha' : a ∈ T.m3.atoms ∧ T.TP a := Finset.mem_filter.mp ha
  have := ha'.1
  rw [T.m3_atoms] at this
  simp only [Finset.mem_insert] at this
  rcases this with h | h | h | h
  · exact Or.inl ⟨2, h⟩
  · exact Or.inl ⟨1, h⟩
  · exact Or.inl ⟨0, h⟩
  · exact Or.inr ⟨h, ha'.2⟩

theorem TP_f (j : Fin 3) : T.TP (T.f j) := fun i => T.f_ne_t j i

theorem rho_mem (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) :
    (fun x : PDart T.m3 T.TP => κ x.1) ∈ decSet T.kept L γ δ w Adm'
      (T.keptParams L w c β k0 (T.triZ κ)).1 (T.keptParams L w c β k0 (T.triZ κ)).2.1
      (T.keptParams L w c β k0 (T.triZ κ)).2.2 := by
  obtain ⟨hdec, hres, hadm⟩ := hκ
  refine ⟨⟨fun x => hdec.1 x.1, fun a ha => ?_⟩, ⟨fun a ha => ?_, fun x => hres.2 x.1⟩, hAdm' κ hadm⟩
  · have ha' : T.TP a := (Finset.mem_filter.mp ha).2
    have e : (∑ x ∈ T.kept.dartsAt a, T.kept.dartSign x • Molecule.kvec L w (fun y : PDart T.m3 T.TP => κ y.1) x) =
        ∑ x ∈ T.kept.dartsAt a, (fun y => M.dartSign y • Molecule.kvec L w κ y) x.1 := rfl
    rw [e]
    refine (T.kept_sum ha' (fun y => M.dartSign y • Molecule.kvec L w κ y)).trans ?_
    rcases T.atom_cases ha with ⟨j, rfl⟩ | ⟨ham, -⟩
    · have h1 := T.sum_t j (fun y => M.dartSign y • Molecule.kvec L w κ y)
      rw [hdec.2 (T.t j) (T.t_mem j), T.tri_vec L w κ hdec.1 j] at h1
      have : (T.keptParams L w c β k0 (T.triZ κ)).1 (T.f j) = c (T.t j) - triC L w (T.triZ κ) j :=
        T.fupd_f (fun j => c (T.t j) - triC L w (T.triZ κ) j) c j
      rw [this]
      exact eq_sub_of_add_eq h1.symm
    · have hf : ∀ j, a ≠ T.f j := fun j e => T.f_fresh j (e ▸ ham)
      have : (T.keptParams L w c β k0 (T.triZ κ)).1 a = c a :=
        T.fupd_other (fun j => c (T.t j) - triC L w (T.triZ κ) j) c hf
      rw [this, T.m3_dartsAt_other ham ha']
      exact hdec.2 a ham
  · have ha' : T.TP a := (Finset.mem_filter.mp ha).2
    have e : T.kept.Gamma L w (fun y : PDart T.m3 T.TP => κ y.1) a =
        ∑ x ∈ T.kept.dartsAt a, (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2) x.1 := rfl
    rw [e, T.kept_sum ha' (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2)]
    rcases T.atom_cases ha with ⟨j, rfl⟩ | ⟨ham, -⟩
    · have h1 := T.sum_t j (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2)
      have h2 := hres.1 (T.t j) (T.t_mem j)
      have h3 : ∑ x ∈ M.dartsAt (T.t j), M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 = M.Gamma L w κ (T.t j) := rfl
      rw [h3, T.tri_en L w κ hdec.1 j] at h1
      have : (T.keptParams L w c β k0 (T.triZ κ)).2.1 (T.f j) = β (T.t j) - triG L w (T.triZ κ) j :=
        T.fupd_f (fun j => β (T.t j) - triG L w (T.triZ κ) j) β j
      rw [this]
      have h4 : ∑ x ∈ T.m3.dartsAt (T.f j), M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 - (β (T.t j) - triG L w (T.triZ κ) j) =
          M.Gamma L w κ (T.t j) - β (T.t j) := by linarith
      rw [h4]; exact h2
    · have hf : ∀ j, a ≠ T.f j := fun j e => T.f_fresh j (e ▸ ham)
      have : (T.keptParams L w c β k0 (T.triZ κ)).2.1 a = β a :=
        T.fupd_other (fun j => β (T.t j) - triG L w (T.triZ κ) j) β hf
      rw [this, T.m3_dartsAt_other ham ha']
      exact hres.1 a ham

theorem kappa_eq_of_triZ (κ κ' : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (hκ' : ∀ x, κ' (M.mate x) = κ' x)
    (hz : T.triZ κ = T.triZ κ') (hρ : (fun x : PDart T.m3 T.TP => κ x.1) = fun x => κ' x.1) : κ = κ' := by
  funext x
  by_cases hx : T.TP (T.m3.atom x)
  · exact congrFun hρ ⟨x, hx⟩
  · obtain ⟨j, hj⟩ := (T.not_TP_iff _).1 hx
    rcases (T.m3_atom_eq_t x j).1 hj with rfl | rfl
    · rw [T.kappa_a κ hκ, T.kappa_a κ' hκ']; exact congrFun hz _
    · exact congrFun hz _

end TriData
end WaveTurbulence.FinalCount
