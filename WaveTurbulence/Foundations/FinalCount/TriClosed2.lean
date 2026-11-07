/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.TriClosed
/-! Triangles, part 9 (FINALCOUNT-G2): the conservation relations of a closed set `S` of `m3` containing no `t i`:
`∑_{j : f j ∈ S} (triangle momentum part at t j) = ∑_{S∩M} c + ∑ c(t j)` and the same for the energies up to
`|S∩M| + |I|` windows. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace TriData
variable {M : Molecule V D} (T : TriData M)

/-- The `f`-indices in `S`. -/
noncomputable def idx (S : Finset V) : Finset (Fin 3) := Finset.univ.filter fun j => T.f j ∈ S

theorem filter_not_mem {S : Finset V} (hsub : ∀ a ∈ S, a ∈ T.m3.atoms) :
    S.filter (fun a => a ∉ M.atoms) = (T.idx S).image T.f := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_image, idx, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ha, hn⟩
    have := hsub a ha
    rw [m3_atoms] at this
    simp only [Finset.mem_insert] at this
    rcases this with h | h | h | h
    · exact ⟨2, h ▸ ha, h.symm⟩
    · exact ⟨1, h ▸ ha, h.symm⟩
    · exact ⟨0, h ▸ ha, h.symm⟩
    · exact absurd h hn
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, T.f_fresh j⟩

theorem sum_split {E : Type*} [AddCommMonoid E] {S : Finset V} (hsub : ∀ a ∈ S, a ∈ T.m3.atoms) (h : V → E) :
    ∑ a ∈ S, h a = ∑ a ∈ S.filter (fun a => a ∈ M.atoms), h a + ∑ j ∈ T.idx S, h (T.f j) := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun a => a ∈ M.atoms), T.filter_not_mem hsub,
    Finset.sum_image (fun i _ j _ e => T.f_inj e)]

theorem closed_zero {E : Type*} [AddCommGroup E] {S : Finset V} (hS : IsClosedSet T.m3 S)
    (hsub : ∀ a ∈ S, a ∈ T.m3.atoms) (g : D → E) (hg : ∀ x, g (M.mate x) = - g x) :
    ∑ a ∈ S.filter (fun a => a ∈ M.atoms), ∑ x ∈ T.m3.dartsAt a, g x +
      ∑ j ∈ T.idx S, ∑ x ∈ T.m3.dartsAt (T.f j), g x = 0 := by
  have h0 := sum_dart_closed_zero T.m3 S hS g hg
  rw [T.sum_split hsub (fun a => ∑ x ∈ T.m3.dartsAt a, g x)] at h0
  exact h0

theorem closed_rel {S : Finset V} (hS : IsClosedSet T.m3 S) (hsub : ∀ a ∈ S, a ∈ T.m3.atoms)
    (ht : ∀ j, T.t j ∉ S) (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : κ ∈ decSet M L γ δ w Adm c β k0) :
    (∑ j ∈ T.idx S, triC L w (T.triZ κ) j =
      ∑ a ∈ S.filter (fun a => a ∈ M.atoms), c a + ∑ j ∈ T.idx S, c (T.t j)) ∧
    |∑ j ∈ T.idx S, triG L w (T.triZ κ) j -
        (∑ a ∈ S.filter (fun a => a ∈ M.atoms), β a + ∑ j ∈ T.idx S, β (T.t j))| ≤
      (((S.filter (fun a => a ∈ M.atoms)).card + (T.idx S).card : ℕ) : ℝ) * (δ⁻¹ * L ^ (-2 * γ)) := by
  obtain ⟨hdec, hres, hadm⟩ := hκ
  have hmem : ∀ a ∈ S.filter (fun a => a ∈ M.atoms), a ∈ M.atoms ∧ T.TP a := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact ⟨ha.2, fun j e => ht j (e ▸ ha.1)⟩
  constructor
  · have h := T.closed_zero hS hsub (fun y => M.dartSign y • Molecule.kvec L w κ y) (by
      intro x; have := hdec.1 x; simp only [dartSign_mate, neg_smul, Molecule.kvec, this])
    have e1 : ∑ a ∈ S.filter (fun a => a ∈ M.atoms), ∑ x ∈ T.m3.dartsAt a, M.dartSign x • Molecule.kvec L w κ x =
        ∑ a ∈ S.filter (fun a => a ∈ M.atoms), c a := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [T.m3_dartsAt_other (hmem a ha).1 (hmem a ha).2]
      exact hdec.2 a (hmem a ha).1
    have e2 : ∀ j ∈ T.idx S, ∑ x ∈ T.m3.dartsAt (T.f j), M.dartSign x • Molecule.kvec L w κ x =
        c (T.t j) - triC L w (T.triZ κ) j := by
      intro j _
      have h1 := T.sum_t j (fun y => M.dartSign y • Molecule.kvec L w κ y)
      rw [hdec.2 (T.t j) (T.t_mem j), T.tri_vec L w κ hdec.1 j] at h1
      exact eq_sub_of_add_eq h1.symm
    rw [e1, Finset.sum_congr rfl e2, Finset.sum_sub_distrib] at h
    have key : ∑ j ∈ T.idx S, triC L w (T.triZ κ) j -
        (∑ a ∈ S.filter (fun a => a ∈ M.atoms), c a + ∑ j ∈ T.idx S, c (T.t j)) =
        -(∑ a ∈ S.filter (fun a => a ∈ M.atoms), c a + (∑ j ∈ T.idx S, c (T.t j) - ∑ j ∈ T.idx S, triC L w (T.triZ κ) j)) := by
      abel
    rw [h, neg_zero] at key
    exact sub_eq_zero.mp key
  · have h := T.closed_zero hS hsub (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2) (by
      intro x; have := hdec.1 x; simp only [dartSign_mate, neg_mul, Molecule.kvec, this])
    have e1 : ∑ a ∈ S.filter (fun a => a ∈ M.atoms), ∑ x ∈ T.m3.dartsAt a, M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 =
        ∑ a ∈ S.filter (fun a => a ∈ M.atoms), M.Gamma L w κ a := by
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [T.m3_dartsAt_other (hmem a ha).1 (hmem a ha).2]; rfl
    have e2 : ∀ j ∈ T.idx S, ∑ x ∈ T.m3.dartsAt (T.f j), M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 =
        M.Gamma L w κ (T.t j) - triG L w (T.triZ κ) j := by
      intro j _
      have h1 := T.sum_t j (fun y => M.dartSign y * ‖Molecule.kvec L w κ y‖ ^ 2)
      rw [T.tri_en L w κ hdec.1 j] at h1
      have h3 : ∑ x ∈ M.dartsAt (T.t j), M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 = M.Gamma L w κ (T.t j) := rfl
      rw [h3] at h1
      exact eq_sub_of_add_eq h1.symm
    rw [e1, Finset.sum_congr rfl e2, Finset.sum_sub_distrib] at h
    have key : ∑ j ∈ T.idx S, triG L w (T.triZ κ) j - (∑ a ∈ S.filter (fun a => a ∈ M.atoms), β a + ∑ j ∈ T.idx S, β (T.t j)) =
        (∑ a ∈ S.filter (fun a => a ∈ M.atoms), (M.Gamma L w κ a - β a) + ∑ j ∈ T.idx S, (M.Gamma L w κ (T.t j) - β (T.t j))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; linarith
    rw [key]
    calc _ ≤ |∑ a ∈ S.filter (fun a => a ∈ M.atoms), (M.Gamma L w κ a - β a)| +
          |∑ j ∈ T.idx S, (M.Gamma L w κ (T.t j) - β (T.t j))| := abs_add_le _ _
      _ ≤ ∑ a ∈ S.filter (fun a => a ∈ M.atoms), |M.Gamma L w κ a - β a| +
          ∑ j ∈ T.idx S, |M.Gamma L w κ (T.t j) - β (T.t j)| :=
          add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _a ∈ S.filter (fun a => a ∈ M.atoms), (δ⁻¹ * L ^ (-2 * γ)) +
          ∑ _j ∈ T.idx S, (δ⁻¹ * L ^ (-2 * γ)) :=
          add_le_add (Finset.sum_le_sum fun a ha => hres.1 a (hmem a ha).1)
            (Finset.sum_le_sum fun j _ => hres.1 (T.t j) (T.t_mem j))
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; push_cast; ring

theorem card_le_atoms {S : Finset V} (ht : ∀ j, T.t j ∉ S) :
    (S.filter (fun a => a ∈ M.atoms)).card + (T.idx S).card ≤ M.atoms.card := by
  have h1 : Disjoint (S.filter (fun a => a ∈ M.atoms)) ((T.idx S).image T.t) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hb
    exact ht j (Finset.mem_filter.mp ha).1
  have h2 : (S.filter (fun a => a ∈ M.atoms)) ∪ ((T.idx S).image T.t) ⊆ M.atoms := by
    intro a ha
    rcases Finset.mem_union.mp ha with h | h
    · exact (Finset.mem_filter.mp h).2
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp h; exact T.t_mem j
  have := Finset.card_le_card h2
  rw [Finset.card_union_of_disjoint h1, Finset.card_image_of_injective _ T.t_inj] at this
  exact this

end TriData
end WaveTurbulence.FinalCount
