/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriDarts
public import WaveTurbulence.Foundations.FinalCount.CoverProj
/-! Triangles, part 4 (FINALCOUNT-G2): the exact-triple cover. `𝔈(M) ≤ N · 𝔈(kept)`, where `N` bounds the number
of triples `(κ(b 0), κ(b 1), κ(b 2))` of bond labels of the triangle (DH23 L1793: `𝔉`, the number of choices for
`(k_{ℓ₁}, k_{ℓ₂}, k_{ℓ₃})`). The parameters of `kept` for a triple are exact: `c'(f j) = c(t j) - (triangle part)`,
`β'(f j) = β(t j) - (triangle energy)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Set
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

open Classical in
/-- Replace the values at the fresh atoms `f j` by `u j`. -/
noncomputable def fupd {X : Type*} (u : Fin 3 → X) (base : V → X) : V → X :=
  fun a => if h : ∃ j, a = T.f j then u h.choose else base a

theorem fupd_f {X : Type*} (u : Fin 3 → X) (base : V → X) (j : Fin 3) : T.fupd u base (T.f j) = u j := by
  classical
  unfold fupd
  have h : ∃ i, T.f j = T.f i := ⟨j, rfl⟩
  rw [dif_pos h]
  have := h.choose_spec
  rw [T.f_inj this.symm]

theorem fupd_other {X : Type*} (u : Fin 3 → X) (base : V → X) {a : V} (h : ∀ j, a ≠ T.f j) :
    T.fupd u base a = base a := by
  classical
  unfold fupd
  rw [dif_neg (by push Not; exact h)]

/-- The bond vector with label `z j` (`j` indexes the bond `b j`). -/
noncomputable def triK (L : ℝ) (w : Mom d) (z : Fin 3 → (Fin d → ℤ)) (j : Fin 3) : Mom d := w + latticePoint L (z j)

/-- The triangle part of `c(t j)`: `-k_{j-1} + k_j` (`a j` is incoming, `b j` outgoing). -/
noncomputable def triC (L : ℝ) (w : Mom d) (z : Fin 3 → (Fin d → ℤ)) (j : Fin 3) : Mom d :=
  -(triK L w z (j - 1)) + triK L w z j

/-- The triangle part of `Γ(t j)`: `|k_j|² - |k_{j-1}|²`. -/
noncomputable def triG (L : ℝ) (w : Mom d) (z : Fin 3 → (Fin d → ℤ)) (j : Fin 3) : ℝ :=
  ‖triK L w z j‖ ^ 2 - ‖triK L w z (j - 1)‖ ^ 2

/-- The bond labels of the triangle. -/
def triZ (κ : D → (Fin d → ℤ)) : Fin 3 → (Fin d → ℤ) := fun j => κ (T.b j)

theorem dartSign_a (j : Fin 3) : M.dartSign (T.a j) = -1 := by
  unfold Molecule.dartSign; rw [T.out_a]; simp
theorem dartSign_b (j : Fin 3) : M.dartSign (T.b j) = 1 := by
  unfold Molecule.dartSign; rw [T.out_b]; simp

theorem kappa_a (κ : D → (Fin d → ℤ)) (hκ : ∀ x, κ (M.mate x) = κ x) (j : Fin 3) :
    κ (T.a j) = κ (T.b (j - 1)) := by
  have := T.mate_b (j - 1)
  rw [sub_add_cancel] at this
  rw [← this, hκ]

/-- The parameter triple of `kept` for the triple `z`. -/
noncomputable def keptParams (L : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (z : Fin 3 → (Fin d → ℤ)) :
    (V → Mom d) × (V → ℝ) × (PDart T.m3 T.TP → Mom d) :=
  (T.fupd (fun j => c (T.t j) - triC L w z j) c, T.fupd (fun j => β (T.t j) - triG L w z j) β,
    fun x => k0 x.1)

theorem m3_deg_f (j : Fin 3) : T.m3.deg (T.f j) + 2 = M.deg (T.t j) := by
  have := T.sum_t j (fun _ => (1 : ℕ))
  simpa [Molecule.deg] using this.symm

theorem keptParams_ok (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (hP : ParamOK M c k0) (z : Fin 3 → (Fin d → ℤ)) :
    ParamOK T.kept (T.keptParams L w c β k0 z).1 (T.keptParams L w c β k0 z).2.2 := by
  refine ⟨fun a ha hdeg => ?_, fun x => hP.2 x.1⟩
  have ha' : a ∈ T.m3.atoms ∧ T.TP a := Finset.mem_filter.mp ha
  have hdeg' : T.m3.deg a = 4 := by
    have := restrictP_deg T.m3 T.TP T.pclosed ha'.2
    exact this ▸ hdeg
  by_cases hf : ∃ j, a = T.f j
  · obtain ⟨j, rfl⟩ := hf
    have := T.m3_deg_f j
    have := hM _ (T.t_mem j)
    omega
  · push Not at hf
    have ham : a ∈ M.atoms := by
      have := ha'.1
      rw [T.m3_atoms] at this
      simp only [Finset.mem_insert] at this
      rcases this with h | h | h | h
      · exact absurd h (hf 2)
      · exact absurd h (hf 1)
      · exact absurd h (hf 0)
      · exact h
    have e : (T.keptParams L w c β k0 z).1 a = c a := T.fupd_other (fun j => c (T.t j) - triC L w z j) c hf
    rw [e]
    refine hP.1 a ham ?_
    unfold Molecule.deg at hdeg' ⊢
    rwa [T.m3_dartsAt_other ham ha'.2] at hdeg'

end TriData
end WaveTurbulence.FinalCount
