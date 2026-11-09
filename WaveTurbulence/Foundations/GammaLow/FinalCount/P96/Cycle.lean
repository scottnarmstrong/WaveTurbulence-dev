/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.CycleCase96
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Odd
import Mathlib.Tactic

/-! # Prop 9.6 at `0 < γ ≤ 1/2`: the cycle components (DH23 L1854–L1862; M2 §4.4)

Port of main's `CycleCase96` with `γ₀ = γ`:
* double bond (vine (I), LG by `vineLG`): main's argument verbatim, margin `η − η² − 2η⁵`;
* `V_α = 0`, length `s ≥ 3`: the TRIVIAL count `3^d L^γ` (`cycle_countA_triv`; one free vector in a unit ball) instead of
  main's `δ⁻¹L^{1−γ}` (which is too weak at `γ < 1/2`), margin `≥ η² − 3η⁵`;
* `V_α ≥ 1`: main's ρ⁻¹ count with slack `γ/4` in place of `(2γ − 1)/2` (`rest_ge_low`): margins `(γ − 3η)/2 − η² − 3η⁵`
  (triangle) and `(γ − 13η)/2 − 3η² − 4η⁵` (`s ≥ 4`). A triangle with two `α`-atoms is excluded by
  `FinalShape.cycle` (this is where the ghost lemma enters, M2 §4.4/§7). No `η ≤ (2γ − 1)/100`. -/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp4

/-- The trivial slab count: `n ≤ (2L+1)^d` gives `n · L^{-(d-γ)} b ≤ 3^d L^γ`. -/
theorem slab_triv {d : ℕ} (hd : 0 < d) {L γ b n : ℝ} (hL : 1 ≤ L) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) (hn0 : 0 ≤ n) (hn : n ≤ (2 * L + 1) ^ d) :
    n * (L ^ (-((d : ℝ) - γ)) * b) ≤ 3 ^ d * L ^ γ := by
  have hLp : 0 < L := by linarith
  have h3 : (2 * L + 1) ^ d ≤ 3 ^ d * L ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hpow : L ^ d * L ^ (-((d : ℝ) - γ)) = L ^ γ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLp]; congr 1; ring
  have hb' : 0 ≤ L ^ (-((d : ℝ) - γ)) := Real.rpow_nonneg hLp.le _
  calc n * (L ^ (-((d : ℝ) - γ)) * b) ≤ (3 ^ d * L ^ d) * (L ^ (-((d : ℝ) - γ)) * 1) :=
        mul_le_mul (hn.trans h3) (mul_le_mul_of_nonneg_left hb1 hb') (mul_nonneg hb' hb0)
          (mul_nonneg (by positivity) (pow_nonneg hLp.le _))
    _ = 3 ^ d * L ^ γ := by rw [← hpow]; ring

theorem cycle_countA_triv {d : ℕ} (hd : 0 < d) {L γ δ C1 ρ : ℝ} (hL : 1 ≤ L) (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (hρ : 0 < ρ) {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (hne : M.atoms.Nonempty) (hch : ∀ b ∈ M.atoms, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (P : Finset V → ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ M.atoms ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖)
    (hMA : MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (3 ^ d * L ^ γ) := by
  classical
  have hLp : 0 < L := by linarith
  have hdeg : ∀ a ∈ M.atoms, M.deg a = 2 := fun a ha => by
    have := Mole.outdeg_add_indeg M a; have := hch a ha; omega
  have hM : M.IsMolecule := by
    refine ⟨fun a ha => by have := hch a ha; omega, fun v hv => ⟨v, hv, Relation.EqvGen.refl _, by
      have := hdeg v hv; omega⟩⟩
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (MoleProp.GapScale L) hMA).trans ?_
  refine (cycle_A hL hδ hC1 hρ M hne hch hconn _ _ (fun κ hκ => hAdm κ hκ.1)).trans ?_
  have hb0 : 0 ≤ C1⁻¹ * δ ^ (1 / 2 : ℝ) := by have := hδ.1; positivity
  have hb1 : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have hC : 0 < C1 := by linarith
    have h1 : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul h1 h2 (by have := hδ.1; positivity) zero_le_one
      _ = 1 := one_mul 1
  set B := min ((2 * L + 1) ^ d) ((2 * L + 1) ^ (d - 1) * (d * (δ⁻¹ * L ^ (-2 * γ)) * L / ρ + 1)) with hB
  have hB0 : 0 ≤ B := le_min (by positivity) (by have := hδ.1; positivity)
  have hfl : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le hB0
  rw [mul_comm, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  exact slab_triv hd hL hb0 hb1 (Nat.cast_nonneg _) (hfl.trans (min_le_left _ _))


section setup
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem cycle_double_low {d : ℕ} (hd : 3 ≤ d) {L γ η δ C1 : ℝ} (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hη : 0 < η)
    (hη1 : η ≤ min γ (1 - γ) / 200) (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (hK : 3 ^ d * (d * δ⁻¹ + 1) ≤ L ^ (η / 2))
    (M : Molecule V D) (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hdeg : ∀ a ∈ M.atoms, M.deg a = 2)
    (hcard : M.atoms.card = 2) (hA : ∃ κ, Adm κ) (hMA : MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hLp : 0 < L := by linarith
  obtain ⟨hch, hnodd, hnnoeps, hMol⟩ := cycle_setup hS hdeg
  have hLG := hF.vineLG (Or.inr ⟨hcard, hdeg⟩)
  -- LG at every pair of opposite darts
  have hgapLG : ∀ κ, Adm κ → ∀ a ∈ M.atoms, ∀ x y, M.atom x = a → M.atom y = a → x ≠ y →
      L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖ := by
    intro κ hκ a ha x y hx hy hxy
    exact hLG κ hκ x y (hx.trans hy.symm) (out_ne_of_two M (hch a ha).1 (hch a ha).2 hx hy hxy)
  -- no α-atom
  have hnoalpha : alphaAtoms M.atoms cls = ∅ := by
    refine eq_empty_of_forall_notMem fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := mem_filter.mp ha
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_darts M (hdeg a ha1)
    -- need an admissible decoration to compare
    obtain ⟨κ, hκ⟩ := hA
    have h1 := hF.alphaSG κ hκ a ha1 ha2 x y hx hy hxy
    have h2 := hgapLG κ hκ a ha1 x y hx hy hxy
    exact absurd h1 (not_le.mpr h2)
  have hVa : (alphaAtoms M.atoms cls).card = 0 := by rw [hnoalpha]; rfl
  have hVab := card_alpha_add_beta M cls hnnoeps
  have hVb : (betaAtoms M.atoms cls).card = 2 := by omega
  obtain ⟨a, ha⟩ := hS.nonempty
  have hρ : 0 < L ^ (-γ + η) := Real.rpow_pos_of_pos hLp _
  have hAdm := hAdm_of_atom M Adm ha (hdeg a ha) (fun κ hκ x y hx hy hxy => (hgapLG κ hκ a ha x y hx hy hxy).le)
  refine (cycle_countA_le (by omega) hL hδ hC1 hρ M hS.nonempty hch hS.conn P Adm hAdm hMA).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  have hηs : η ≤ γ / 200 := by rw [hγ0] at hη1; exact hη1
  have hη10 : η ≤ 1 / 10 := by linarith [hγ.1, hγ.2]
  -- X ≤ L^{-η/2}
  have hX1 : ((d : ℝ) * δ⁻¹ * (L ^ (-γ + η))⁻¹ * L ^ (-γ)) = (d : ℝ) * δ⁻¹ * L ^ (-η) := by
    rw [← Real.rpow_neg hLp.le, mul_assoc, ← Real.rpow_add hLp]; congr 2; ring
  have hX2 : L ^ (γ - 1) ≤ L ^ (-η) := Real.rpow_le_rpow_of_exponent_le hL (by linarith [hγ.2])
  have hδ0 := hδ.1
  have hX3 : (3:ℝ) ^ d * ((d : ℝ) * δ⁻¹ * (L ^ (-γ + η))⁻¹ * L ^ (-γ) + L ^ (γ - 1)) ≤ L ^ (-(η / 2)) := by
    rw [hX1]
    calc _ ≤ (3:ℝ) ^ d * ((d : ℝ) * δ⁻¹ * L ^ (-η) + L ^ (-η)) := by gcongr
      _ = (3:ℝ) ^ d * ((d : ℝ) * δ⁻¹ + 1) * L ^ (-η) := by ring
      _ ≤ L ^ (η / 2) * L ^ (-η) := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hLp.le _)
      _ = L ^ (-(η / 2)) := by rw [← Real.rpow_add hLp]; congr 1; ring
  refine hX3.trans ?_
  refine le_trans ?_ (finalRHS_ge M cls odd hL hη.le hF.labRange)
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  rw [hVa, hVb, if_neg hnodd]
  have hρ0 : (M.rho : ℝ) ≤ 2 := by
    have := rho_le_card_of_deg_le_two M (fun a ha => (hdeg a ha).le)
    rw [hcard] at this; exact_mod_cast this
  have hη5 : η ^ 5 ≤ η ^ 2 := pow_le_pow_of_le_one hη.le (by linarith) (by norm_num)
  have hη2 : η ^ 2 ≤ η / 10 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hρ0 (by positivity : (0:ℝ) ≤ η ^ 5)]



/-- **A cycle of length `≥ 3` without `α`-atoms at `γ ≤ 1/2`** (trivial count). -/
theorem cycle_noalpha_low {d : ℕ} (hd : 3 ≤ d) {L γ η δ C1 : ℝ} (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hη : 0 < η)
    (hη1 : η ≤ min γ (1 - γ) / 200) (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (hK : 3 ^ d * (d * δ⁻¹ + 1) ≤ L ^ (η ^ 2 / 4))
    (M : Molecule V D) (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hdeg : ∀ a ∈ M.atoms, M.deg a = 2)
    (hcard : 3 ≤ M.atoms.card) (hnoalpha : alphaAtoms M.atoms cls = ∅)
    (hMA : MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hLp : 0 < L := by linarith
  by_cases hA : ∃ κ, Adm κ
  swap
  · push Not at hA
    rw [countA_zero_of_noAdm M L γ δ C1 Adm P (fun κ => hA κ)]; exact bot_le
  obtain ⟨hch, hnodd, hnnoeps, hMol⟩ := cycle_setup hS hdeg
  have hVa : (alphaAtoms M.atoms cls).card = 0 := by rw [hnoalpha]; rfl
  have hVab := card_alpha_add_beta M cls hnnoeps
  have hVb : (betaAtoms M.atoms cls).card = M.atoms.card := by omega
  obtain ⟨a, ha⟩ := hS.nonempty
  have hρ : 0 < L⁻¹ := inv_pos.mpr hLp
  have hbeta : (cls a).IsBeta := by
    rcases cls_cases (hnnoeps a ha) with h | h
    · have hmem : a ∈ alphaAtoms M.atoms cls := mem_filter.mpr ⟨ha, h⟩
      rw [hnoalpha] at hmem; simp at hmem
    · exact h
  have hAdm := hAdm_of_atom M Adm ha (hdeg a ha) (fun κ hκ x y hx hy hxy =>
    gap_lower_of_ne hLp (hF.betaGap κ hκ a ha hbeta x y hx hy hxy))
  refine (cycle_countA_triv (by omega) hL hδ hC1 hρ M hS.nonempty hch hS.conn P Adm hAdm hMA).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  have hηs : η ≤ γ / 200 := by rw [hγ0] at hη1; exact hη1
  have hδ0 := hδ.1
  have hX3 : (3:ℝ) ^ d * L ^ γ ≤ L ^ (η ^ 2 / 4) * L ^ γ := by
    refine mul_le_mul_of_nonneg_right (le_trans ?_ hK) (Real.rpow_nonneg hLp.le _)
    have : (0 : ℝ) ≤ 3 ^ d * ((d : ℝ) * δ⁻¹) := by positivity
    nlinarith
  refine hX3.trans ?_
  rw [← Real.rpow_add hLp]
  refine le_trans ?_ (finalRHS_ge M cls odd hL hη.le hF.labRange)
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  rw [hVa, hVb, if_neg hnodd]
  have hρ0 : (M.rho : ℝ) ≤ (M.atoms.card : ℝ) := by
    exact_mod_cast rho_le_card_of_deg_le_two M (fun a ha => (hdeg a ha).le)
  have hs3 : (3 : ℝ) ≤ (M.atoms.card : ℝ) := by exact_mod_cast hcard
  have hη01 : η ≤ 1 / 400 := by linarith [hγ.2]
  have hη5 : η ^ 5 ≤ η ^ 2 / 10 := by
    have h1 : η ^ 3 ≤ 1 / 10 := by nlinarith [pow_pos hη 2]
    nlinarith [pow_pos hη 2]
  rw [hγ0]
  have hγp := hγ.1
  nlinarith [mul_le_mul_of_nonneg_left hρ0 (by positivity : (0:ℝ) ≤ η ^ 5), pow_pos hη 2,
    mul_nonneg (by linarith : (0:ℝ) ≤ (M.atoms.card : ℝ) - 3) (by nlinarith [pow_pos hη 2] : (0:ℝ) ≤ γ + 2 * η ^ 2 - η ^ 5)]

end setup

/-- The exponent bookkeeping for a cycle with an `α`-atom at `γ ≤ 1/2` (slack `γ/4`; a triangle has `V_α ≤ 1`). -/
theorem rest_ge_low {γ η Va Vb ρ0 : ℝ} (hγ1 : 0 < γ) (hγ2 : γ ≤ 1 / 2) (hη : 0 < η)
    (hη1 : η ≤ γ / 200) (hVa : 1 ≤ Va) (hVb : 1 ≤ Vb)
    (hs : 3 ≤ Va + Vb) (htri : Va + Vb < 4 → Va ≤ 1) (hρ : ρ0 ≤ Va + Vb) :
    γ / 4 - (γ - 3 * η) / 2 ≤
      (Va - 1) * ((γ - 5 * η) / 2) + ((γ + 2 * η ^ 2) * Vb - (2 * γ + 5 * η ^ 2) * 1) +
        (-(η ^ 5) * ρ0) := by
  have hη3 : η ≤ 1 / 400 := by linarith
  have hη2' : η ^ 2 ≤ η / 400 := by nlinarith
  have hη5 : η ^ 5 ≤ η ^ 2 / 10 := by
    have h1 : η ^ 3 ≤ 1 / 10 := by nlinarith [pow_pos hη 2]
    nlinarith [pow_pos hη 2]
  have h5 : η ^ 5 * ρ0 ≤ η ^ 5 * (Va + Vb) := mul_le_mul_of_nonneg_left hρ (by positivity)
  set m : ℝ := (γ - 5 * η) / 2 - η ^ 5 with hm
  have hm0 : 0 ≤ m := by nlinarith [pow_pos hη 5]
  have hc2 : m ≤ γ + 2 * η ^ 2 - η ^ 5 := by nlinarith [pow_pos hη 2, pow_pos hη 5]
  have hu : 0 ≤ Va - 1 := by linarith
  have hw : 0 ≤ Vb - 1 := by linarith
  by_cases h4 : Va + Vb < 4
  · have ha1 : Va = 1 := le_antisymm (htri h4) hVa
    subst ha1
    nlinarith [pow_pos hη 2, pow_pos hη 5]
  · push Not at h4
    nlinarith [mul_nonneg hu (sub_nonneg.mpr (le_refl m)), mul_nonneg hw (sub_nonneg.mpr hc2),
      mul_nonneg hm0 (by linarith : (0:ℝ) ≤ (Va - 1) + (Vb - 1) - 2), pow_pos hη 2, pow_pos hη 5]

section cases
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
/-- **A cycle of length `≥ 3` with an `α`-atom** (L1860-L1862). -/
theorem cycle_alpha_low {d : ℕ} (hd : 3 ≤ d) {L γ η δ C1 : ℝ} (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (hη : 0 < η)
    (hη1 : η ≤ min γ (1 - γ) / 200) (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hC1 : 1 ≤ C1) (hK1 : 4 * 3 ^ d * (d * δ⁻¹) ≤ L ^ (γ / 4)) (hK2 : 2 * 3 ^ d ≤ L ^ (1 / 2 - η))
    (M : Molecule V D) (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
    (hS : FinalShape M cls odd) (hF : FinalDec M cls L γ η Adm) (hdeg : ∀ a ∈ M.atoms, M.deg a = 2)
    (hcard : 3 ≤ M.atoms.card) {v₀ : V} (hv₀ : v₀ ∈ alphaAtoms M.atoms cls)
    (hMA : MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm) :
    M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hLp : 0 < L := by linarith
  by_cases hA : ∃ κ, Adm κ
  swap
  · push Not at hA
    rw [countA_zero_of_noAdm M L γ δ C1 Adm P (fun κ => hA κ)]; exact bot_le
  obtain ⟨hch, hnodd, hnnoeps, hMol⟩ := cycle_setup hS hdeg
  obtain ⟨hv₀a, hv₀α⟩ := mem_filter.mp hv₀
  have hlab := hF.labRange v₀ hv₀a hv₀α
  set R0 := (cls v₀).lab with hR0
  have hR0pos : 0 < R0 := lt_of_lt_of_le (inv_pos.mpr hLp) hlab.1
  have hρ : 0 < R0 / 2 := by positivity
  have hAdm := hAdm_of_atom M Adm hv₀a (hdeg v₀ hv₀a) (fun κ hκ x y hx hy hxy =>
    (hF.alphaGap κ hκ v₀ hv₀a hv₀α x y hx hy hxy).1)
  refine (cycle_countA_le (by omega) hL hδ hC1 hρ M hS.nonempty hch hS.conn P Adm hAdm hMA).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  have hηs : η ≤ γ / 200 := by rw [hγ0] at hη1; exact hη1
  have hδ0 := hδ.1
  -- counts
  have hVab := card_alpha_add_beta M cls hnnoeps
  obtain ⟨b, hb, hbβ⟩ := hS.evenBeta hnodd
  have hVa1 : 1 ≤ (alphaAtoms M.atoms cls).card := card_pos.mpr ⟨v₀, hv₀⟩
  have hVb1 : 1 ≤ (betaAtoms M.atoms cls).card := card_pos.mpr ⟨b, mem_filter.mpr ⟨hb, hbβ⟩⟩
  have hρ0 : (M.rho : ℝ) ≤ (M.atoms.card : ℝ) := by
    exact_mod_cast rho_le_card_of_deg_le_two M (fun a ha => (hdeg a ha).le)
  have hVsum : ((alphaAtoms M.atoms cls).card : ℝ) + ((betaAtoms M.atoms cls).card : ℝ) = (M.atoms.card : ℝ) := by
    exact_mod_cast hVab
  have hVa1' : (1 : ℝ) ≤ ((alphaAtoms M.atoms cls).card : ℝ) := by exact_mod_cast hVa1
  have hVb1' : (1 : ℝ) ≤ ((betaAtoms M.atoms cls).card : ℝ) := by exact_mod_cast hVb1
  have hs3 : (3 : ℝ) ≤ ((alphaAtoms M.atoms cls).card : ℝ) + ((betaAtoms M.atoms cls).card : ℝ) := by
    rw [hVsum]; exact_mod_cast hcard
  set rest : ℝ := (((alphaAtoms M.atoms cls).card : ℝ) - 1) * ((γ - 5 * η) / 2) +
    ((γ + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) - (2 * γ + 5 * η ^ 2) * 1) +
    (-(η ^ 5) * (M.rho : ℝ)) with hrest
  have htri : ((alphaAtoms M.atoms cls).card : ℝ) + ((betaAtoms M.atoms cls).card : ℝ) < 4 →
      ((alphaAtoms M.atoms cls).card : ℝ) ≤ 1 := by
    intro h4
    rw [hVsum] at h4
    have h4' : M.atoms.card < 4 := by exact_mod_cast h4
    rcases hS.cycle hdeg with h | h | ⟨_, h⟩
    · omega
    · omega
    · exact_mod_cast h
  have hrest_ge : γ / 4 - (γ - 3 * η) / 2 ≤ rest :=
    rest_ge_low hγ.1 hγ.2 hη hηs hVa1' hVb1' hs3 htri (by rw [hVsum]; exact hρ0)
  -- the lower bound of the right-hand side
  have hR := finalRHS_ge_split M cls odd hL hη.le hF.labRange hv₀
  have hexp : (((alphaAtoms M.atoms cls).card : ℝ) - 1) * ((γ - 5 * η) / 2) +
        ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) -
          (2 * min γ (1 - γ) + 5 * η ^ 2) * (if odd then (0 : ℝ) else 1)) +
        (-(η ^ 5) * (M.rho : ℝ)) = rest := by
    rw [hrest, hγ0, if_neg hnodd]
  rw [hexp] at hR
  refine le_trans ?_ hR
  set T := L ^ (-(γ + 3 * η) / 2) * ((cls v₀).lab)⁻¹ * L ^ rest with hT
  -- the two terms
  have hRinv : L ^ (γ - η) ≤ R0⁻¹ := by
    have : (L ^ (-γ + η))⁻¹ = L ^ (γ - η) := by rw [← Real.rpow_neg hLp.le]; congr 1; ring
    rw [← this]; exact inv_anti₀ hR0pos hlab.2
  have hterm1 : 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ)) ≤ T / 2 := by
    have h1 : 4 * 3 ^ d * ((d : ℝ) * δ⁻¹) * (R0⁻¹ * L ^ (-γ)) ≤ L ^ (γ / 4) * (R0⁻¹ * L ^ (-γ)) :=
      mul_le_mul_of_nonneg_right hK1 (by positivity)
    have h2 : L ^ (γ / 4) * (R0⁻¹ * L ^ (-γ)) ≤ T := by
      calc _ = R0⁻¹ * L ^ (γ / 4 + -γ) := by rw [Real.rpow_add hLp]; ring
        _ ≤ R0⁻¹ * L ^ (-(γ + 3 * η) / 2 + rest) := by
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL ?_) (inv_nonneg.mpr hR0pos.le)
            linarith
        _ = T := by rw [hT, Real.rpow_add hLp]; ring
    have : (R0 / 2)⁻¹ = 2 * R0⁻¹ := by rw [inv_div]; field_simp
    rw [this]
    nlinarith [h1, h2]
  have hterm2 : 3 ^ d * L ^ (γ - 1) ≤ T / 2 := by
    have h1 : 2 * 3 ^ d * L ^ (γ - 1) ≤ L ^ (1 / 2 - η) * L ^ (γ - 1) :=
      mul_le_mul_of_nonneg_right hK2 (Real.rpow_nonneg hLp.le _)
    have h2 : L ^ (1 / 2 - η) * L ^ (γ - 1) ≤ T := by
      calc _ = L ^ ((2 * γ - 1) / 2 - η) := by rw [← Real.rpow_add hLp]; congr 1; ring
        _ ≤ L ^ ((γ - η) + (-(γ + 3 * η) / 2 + rest)) :=
            Real.rpow_le_rpow_of_exponent_le hL (by linarith [hγ.2])
        _ = L ^ (γ - η) * L ^ (-(γ + 3 * η) / 2) * L ^ rest := by
            rw [Real.rpow_add hLp, Real.rpow_add hLp]; ring
        _ ≤ R0⁻¹ * L ^ (-(γ + 3 * η) / 2) * L ^ rest := by gcongr
        _ = T := by rw [hT]; ring
    linarith
  calc 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1))
      = 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ)) + 3 ^ d * L ^ (γ - 1) := by ring
    _ ≤ T / 2 + T / 2 := add_le_add hterm1 hterm2
    _ = T := by ring


end cases

/-- **Cycles** (DH23 L1854-L1862): all three cases, with the thresholds in `L`. -/
theorem cycle_case_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ min γ (1 - γ) / 200) (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀, ∀ C1 : ℝ, 1 ≤ C1 →
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (∀ a ∈ M.atoms, M.deg a = 2) →
        MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  have hη1' : 0 < η ^ 2 / 4 := by positivity
  have hγ12 : 0 < γ / 4 := by linarith [hγ.1]
  have hηs : η ≤ γ / 200 := by
    have : min γ (1 - γ) = γ := min_gamma_low hγ.2
    rw [this] at hη1; exact hη1
  have hη01 : η ≤ 1 / 100 := by linarith [hγ.1, hγ.2]
  obtain ⟨R1, hR1, h1⟩ := const_le_rpow (C := 3 ^ d * (d * δ⁻¹ + 1)) (ε := η / 2) (by have := hδ.1; positivity)
    (by positivity)
  obtain ⟨R2, hR2, h2⟩ := const_le_rpow (C := 3 ^ d * (d * δ⁻¹ + 1)) (ε := η ^ 2 / 4) (by have := hδ.1; positivity) hη1'
  obtain ⟨R3, hR3, h3⟩ := const_le_rpow (C := 4 * 3 ^ d * (d * δ⁻¹)) (ε := γ / 4) (by have := hδ.1; positivity) hγ12
  obtain ⟨R4, hR4, h4⟩ := const_le_rpow (C := 2 * 3 ^ d) (ε := 1 / 2 - η) (by positivity) (by linarith)
  refine ⟨max (max R1 R2) (max R3 R4), le_trans hR1 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro L hL C1 hC1 V D _ _ _ M cls odd Adm P hS hF hdeg hMA
  have hL1 : 1 ≤ L := le_trans hR1 (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hL))
  have hLR1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLR2 : R2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLR3 : R3 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLR4 : R4 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  by_cases hA : ∃ κ, Adm κ
  swap
  · push Not at hA
    rw [countA_zero_of_noAdm M L γ δ C1 Adm P (fun κ => hA κ)]; exact bot_le
  have hc2 := two_le_card_of_loopfree M hS.noLoop hS.degPos hS.nonempty
  by_cases hc : M.atoms.card = 2
  · exact cycle_double_low hd hγ hη hη1 hL1 hδ hC1 (h1 L hLR1) M cls odd Adm P hS hF hdeg hc hA hMA
  · have hc3 : 3 ≤ M.atoms.card := by omega
    by_cases hα : ∃ v₀, v₀ ∈ alphaAtoms M.atoms cls
    · obtain ⟨v₀, hv₀⟩ := hα
      exact cycle_alpha_low hd hγ hη hη1 hL1 hδ hC1 (h3 L hLR3) (h4 L hLR4) M cls odd Adm P hS hF hdeg hc3 hv₀ hMA
    · push Not at hα
      exact cycle_noalpha_low hd hγ hη hη1 hL1 hδ hC1 (h2 L hLR2) M cls odd Adm P hS hF hdeg hc3
        (eq_empty_of_forall_notMem hα) hMA

end WaveTurbulence.GammaLow.FinalCount
