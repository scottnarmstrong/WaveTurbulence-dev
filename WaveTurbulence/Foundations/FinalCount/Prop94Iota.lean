/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Ops
/-! The `ι_v ≠ 0` reading of DH23 Remark `remiota` / L1801 (FINALCOUNT-G2).

Source: "`ι_v = 1` if a cutting operation happened before the cutting at `v`, such that the gaps `r, r'` of
these cuttings satisfy `0 < |r ± r'| ≤ L^{-50η} R_v`" (L1782), and L1801: "the corresponding gap `r` must belong
to a fixed ball of radius `L^{-50η}R`".  After the earlier cut at `v'` (degree `2`, darts `y₁` incoming,
`y₂` outgoing) the gap `r'` of that cut is, up to sign, the charge `c_{v'} = ∑_{x ↔ v'} ζ_{v',x} k_x` of the
cut atom, a *parameter* of the molecule.  So the condition is a condition on the decoration alone,
"`|r - s · charge(v')| ≤ ρ` for the fixed atom `v'` and a sign `s = ±1`", and the fixed ball of L1801 is the one
with centre `s · c_{v'}`, determined by the parameters. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The charge `∑_{x ↔ v'} ζ_{v',x} k_x` of an atom. -/
noncomputable def chargeAt (M : Molecule V D) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (v' : V) : Mom d :=
  ∑ x ∈ M.dartsAt v', M.dartSign x • Molecule.kvec L w κ x

/-- **The `ι_v ≠ 0` condition** (L1782: "`0 < |r ± r'| ≤ L^{-50η} R_v`"): for the fixed earlier cut atom `v'`
(balanced: as many outgoing as incoming darts, e.g. a degree-`2` atom with one of each) and a sign `s = ±1`, every
admissible decoration has `0 < ‖r - s · charge(v')‖ ≤ ρ`, where `r` is the gap along `x₁, x₂`. -/
def IotaReading (M : Molecule V D) (L : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (x₁ x₂ : D) (ρ : ℝ) :
    Prop :=
  ∃ v' ∈ M.atoms, (∑ x ∈ M.dartsAt v', M.dartSign x) = 0 ∧ ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ κ', Adm κ' →
    0 < ‖Molecule.gapAt L w κ' x₁ x₂ - s • chargeAt M L w κ' v'‖ ∧
    ‖Molecule.gapAt L w κ' x₁ x₂ - s • chargeAt M L w κ' v'‖ ≤ ρ

theorem norm_latticePoint_ge {L : ℝ} (hL : 0 < L) (n : Fin d → ℤ) (hn : n ≠ 0) : L⁻¹ ≤ ‖latticePoint L n‖ := by
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    exact hn (funext fun i => by simpa using (not_exists.mp h i))
  have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by
    have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : |(latticePoint L n) i| ≤ ‖latticePoint L n‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (latticePoint L n) i
  have h3 : (latticePoint L n) i = (n i : ℝ) / L := rfl
  rw [h3, abs_div, abs_of_pos hL] at h2
  calc L⁻¹ = 1 / L := by simp
    _ ≤ |(n i : ℝ)| / L := by gcongr
    _ ≤ _ := h2

/-- **The radius of the `ι` ball is at least the lattice spacing** (the content of "`0 < |r ± r'|`" and
`r ± r' ∈ L⁻¹ ℤ^d`): if some decoration is admissible, `L⁻¹ ≤ ρ`. -/
theorem iota_radius_ge {M : Molecule V D} {L : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop} {x₁ x₂ : D}
    {ρ : ℝ} (hL : 0 < L) (h : IotaReading M L w Adm x₁ x₂ ρ) (κ : D → (Fin d → ℤ)) (hκ : Adm κ) : L⁻¹ ≤ ρ := by
  obtain ⟨v', -, hbal, s, hs, hh⟩ := h
  obtain ⟨hpos, hle⟩ := hh κ hκ
  -- integer form of the charge
  set z : D → ℤ := fun x => if M.out x = true then 1 else -1 with hz
  have hzr : ∀ x, ((z x : ℤ) : ℝ) = M.dartSign x := by
    intro x; simp only [hz, Molecule.dartSign]; split_ifs <;> simp
  have hlin : ∀ (m : ℤ) (a : Fin d → ℤ), (m : ℝ) • latticePoint L a = latticePoint L (m • a) := by
    intro m a; ext i; simp [latticePoint]; ring
  have hadd : ∀ (a b : Fin d → ℤ), latticePoint L (a + b) = latticePoint L a + latticePoint L b := by
    intro a b; ext i; simp [latticePoint]; ring
  have hsumlp : ∀ (g : D → (Fin d → ℤ)) (T : Finset D),
      ∑ x ∈ T, latticePoint L (g x) = latticePoint L (∑ x ∈ T, g x) := by
    intro g T
    induction T using Finset.induction_on with
    | empty => ext i; simp [latticePoint]
    | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hch : chargeAt M L w κ v' = latticePoint L (∑ x ∈ M.dartsAt v', z x • κ x) := by
    unfold chargeAt Molecule.kvec
    have : ∀ x ∈ M.dartsAt v', M.dartSign x • (w + latticePoint L (κ x)) =
        M.dartSign x • w + latticePoint L (z x • κ x) := by
      intro x _
      rw [smul_add, ← hzr x, hlin]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.sum_smul, hbal, zero_smul, zero_add,
      hsumlp]
  have hgap : Molecule.gapAt L w κ x₁ x₂ = latticePoint L (κ x₁ - κ x₂) := by
    unfold Molecule.gapAt Molecule.kvec
    ext i; simp [latticePoint]; ring
  set N := ∑ x ∈ M.dartsAt v', z x • κ x with hN
  have hdiff : ∃ n : Fin d → ℤ, Molecule.gapAt L w κ x₁ x₂ - s • chargeAt M L w κ v' = latticePoint L n := by
    rcases hs with rfl | rfl
    · refine ⟨κ x₁ - κ x₂ - N, ?_⟩
      rw [hgap, hch]; ext i; simp [latticePoint]; ring
    · refine ⟨κ x₁ - κ x₂ + N, ?_⟩
      rw [hgap, hch]; ext i; simp [latticePoint]; ring
  obtain ⟨n, hn⟩ := hdiff
  rw [hn] at hpos hle
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h0 : latticePoint L (0 : Fin d → ℤ) = 0 := by ext i; simp [latticePoint]
    rw [h0, norm_zero] at hpos
    exact lt_irrefl _ hpos
  exact (norm_latticePoint_ge hL n hn0).trans hle

/-- **L1801, the fixed ball.** The `ι` condition gives, for every parameter triple, a ball of radius `ρ`
(centre `s · c_{v'}`) containing the gaps of all decorations of that triple. -/
theorem ball_of_iota {M : Molecule V D} {L γ δ : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop} {x₁ x₂ : D}
    {ρ : ℝ} (h : IotaReading M L w Adm x₁ x₂ ρ) :
    ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ' x₁ x₂ - r₀‖ ≤ ρ := by
  obtain ⟨v', hv', -, s, -, hs⟩ := h
  intro c β k0 _
  refine ⟨s • c v', fun κ' hκ' => ?_⟩
  have h1 : chargeAt M L w κ' v' = c v' := hκ'.1.2 v' hv'
  have := (hs κ' hκ'.2.2).2
  rwa [h1] at this

end WaveTurbulence.FinalCount
