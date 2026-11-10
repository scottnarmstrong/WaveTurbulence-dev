/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Run
/-! **FINALCOUNT-G3**: the standing hypotheses on `M_sub` and the invariants along a whole run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The standing hypotheses on `M_sub = 𝕄(𝒢_sb)` (DH23 Prop `subpro`/Prop 9.1 (b); TARGET Prop `subpro` (1)):
molecule bounds, all atoms of degree `3` or `4` (`≥ 3` here, and `≤ 4` from the bounds), `n` atoms and `2n - R`
bonds, no self-loop, connected. `R = 1` is the couple case of DH23 (two atoms of degree `3`). -/
structure SubHyp (R : ℕ) (M₀ : Molecule V D₀) : Prop where
  bounds : ∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2
  deg3 : ∀ a ∈ M₀.atoms, 3 ≤ M₀.deg a
  count : M₀.bonds.card + R = 2 * M₀.atoms.card
  noloop : ∀ x, M₀.atom x ≠ M₀.atom (M₀.mate x)
  conn : ∀ a ∈ M₀.atoms, ∀ b ∈ M₀.atoms, M₀.SameComponent a b
  one_le : 1 ≤ R

theorem card_darts_eq_two_bonds (M : Molecule V D₀) : Fintype.card D₀ = 2 * M.bonds.card := by
  have h1 : (Finset.univ.filter fun x : D₀ => M.out x = false).card = M.bonds.card := by
    refine Finset.card_bij (fun x _ => M.mate x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp [Molecule.bonds, M.out_mate, hx]
    · intro x _ y _ e; simpa [M.mate_mate] using congrArg M.mate e
    · intro y hy
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact ⟨M.mate y, by simp [M.out_mate, hy], M.mate_mate y⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D₀)) (fun x => M.out x = true)
  have h3 : (Finset.univ.filter fun x : D₀ => ¬ M.out x = true) =
      Finset.univ.filter fun x : D₀ => M.out x = false := by ext x; simp
  rw [h3, h1] at h2
  simp only [Finset.card_univ] at h2
  unfold Molecule.bonds at *
  omega

theorem SubHyp.odd_card {R : ℕ} {M₀ : Molecule V D₀} (h : SubHyp R M₀) :
    (M₀.atoms.filter fun a => ¬ Even (M₀.deg a)).card = 2 * R := by
  have hD := card_darts_eq_two_bonds M₀
  have hsum := sum_deg_eq M₀
  have hle : ∀ a ∈ M₀.atoms, M₀.deg a ≤ 4 := fun a ha => deg_le_four M₀ (h.bounds a ha)
  have h1 : (M₀.atoms.filter fun a => ¬ Even (M₀.deg a)) = M₀.atoms.filter fun a => M₀.deg a = 3 := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hn⟩
      refine ⟨ha, ?_⟩
      have := h.deg3 a ha; have := hle a ha
      interval_cases hd : M₀.deg a
      · rfl
      · exact absurd (by decide) hn
    · rintro ⟨ha, hn⟩; exact ⟨ha, by rw [hn]; decide⟩
  rw [h1]
  have h2 : ∑ a ∈ M₀.atoms, (4 - M₀.deg a) = (M₀.atoms.filter fun a => M₀.deg a = 3).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun a ha => ?_
    have := h.deg3 a ha; have := hle a ha
    interval_cases hd : M₀.deg a <;> simp
  have h3 : ∑ a ∈ M₀.atoms, (4 - M₀.deg a) + ∑ a ∈ M₀.atoms, M₀.deg a = 4 * M₀.atoms.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (g := fun _ => 4)]
    · simp [mul_comm]
    · intro a ha; have := hle a ha; omega
  have := h.count
  omega

theorem SubHyp.inv {R : ℕ} {M₀ : Molecule V D₀} (h : SubHyp R M₀) : Inv.{_, _, _} R (St.init M₀) := by
  have hD := card_darts_eq_two_bonds M₀
  have hsum := sum_deg_eq M₀
  have hle : ∀ a ∈ M₀.atoms, M₀.deg a ≤ 4 := fun a ha => deg_le_four M₀ (h.bounds a ha)
  refine ⟨h.bounds, fun a ha _ => by show 1 ≤ M₀.deg a; have := h.deg3 a ha; omega, fun a ha hne => absurd rfl hne, ?_, h.noloop⟩
  · show ∑ a ∈ M₀.atoms, (Cls.eps).base = _
    simp only [Cls.base, Finset.sum_const, smul_eq_mul]
    have := h.count
    have hD' : Fintype.card (St.init M₀).D = Fintype.card D₀ := rfl
    rw [hD']
    simp
    omega
theorem St.init_clean (M₀ : Molecule V D₀) : Clean (St.init M₀) := fun a _ h => by
  have : (St.init M₀).cls a = Cls.eps := rfl
  rw [this] at h; exact absurd h (by simp)

end WaveTurbulence.FinalCountG3
