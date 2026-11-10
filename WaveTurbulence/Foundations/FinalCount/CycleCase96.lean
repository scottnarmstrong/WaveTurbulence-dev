/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Cycle96
import Mathlib.Tactic

/-! # Prop 9.6, the cycle components (DH23 L1854-L1862), from `FinalShape` / `FinalDec` -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

section setup
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem out_ne_of_two (M : Molecule V D) {a : V} (ho : M.outdeg a = 1) (hi : M.indeg a = 1) {x y : D}
    (hx : M.atom x = a) (hy : M.atom y = a) (hxy : x ≠ y) : M.out x ≠ M.out y := by
  classical
  intro h
  have hmem : ∀ z, M.atom z = a → z ∈ M.dartsAt a := fun z hz => by simp [Molecule.dartsAt, hz]
  cases hc : M.out x
  · have : (M.dartsAt a).filter (fun z => M.out z = false) ⊇ {x, y} := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_filter.mpr ⟨hmem _ hx, hc⟩
      · exact mem_filter.mpr ⟨hmem _ hy, by rw [← h, hc]⟩
    have h2 := card_le_card this
    rw [card_pair hxy] at h2
    unfold Molecule.indeg at hi
    omega
  · have : (M.dartsAt a).filter (fun z => M.out z = true) ⊇ {x, y} := by
      intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact mem_filter.mpr ⟨hmem _ hx, hc⟩
      · exact mem_filter.mpr ⟨hmem _ hy, by rw [← h, hc]⟩
    have h2 := card_le_card this
    rw [card_pair hxy] at h2
    unfold Molecule.outdeg at ho
    omega

theorem cycle_setup {M : Molecule V D} {cls : V → Cls} {odd : Prop} (hS : FinalShape M cls odd)
    (hdeg : ∀ a ∈ M.atoms, M.deg a = 2) :
    (∀ b ∈ M.atoms, M.outdeg b = 1 ∧ M.indeg b = 1) ∧ ¬ odd ∧ (∀ a ∈ M.atoms, ¬ (cls a).IsEps) ∧
      M.IsMolecule := by
  refine ⟨fun b hb => hS.dir2 b hb (hdeg b hb), ?_, fun a ha => (hS.classes a ha).mp (by have := hdeg a ha; omega), ?_⟩
  · intro hodd
    obtain ⟨u, hu, w, hw, _, hu1, _⟩ := hS.oddDeg hodd
    have := hdeg u hu; omega
  · refine ⟨hS.caps, fun v hv => ⟨v, hv, Relation.EqvGen.refl _, by have := hdeg v hv; omega⟩⟩

end setup


/-- The exponent bookkeeping for a cycle with an `α`-atom. -/
theorem rest_ge_real {γ η Va Vb ρ0 : ℝ} (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ (1 - γ) / 200) (hη2 : η ≤ (2 * γ - 1) / 100) (hVa : 1 ≤ Va) (hVb : 1 ≤ Vb)
    (hs : 3 ≤ Va + Vb) (hρ : ρ0 ≤ Va + Vb) :
    (2 * γ - 1) / 2 - (γ - 3 * η) / 2 ≤
      (Va - 1) * ((γ - 5 * η) / 2) + ((1 - γ + 2 * η ^ 2) * Vb - (2 * (1 - γ) + 5 * η ^ 2) * 1) +
        (-(η ^ 5) * ρ0) := by
  have hη3 : η ≤ 1 / 100 := by linarith only [hη1, hγ1]
  have hη2' : η ^ 2 ≤ η / 100 := by
    calc η ^ 2 = η * η := sq η
      _ ≤ η * (1 / 100) := mul_le_mul_of_nonneg_left hη3 hη.le
      _ = η / 100 := by ring
  have hη5 : η ^ 5 ≤ η ^ 2 / 10 := by
    have h1 : η ^ 3 ≤ 1 / 10 := (pow_le_of_le_one hη.le (by linarith) (by norm_num)).trans (by linarith)
    calc η ^ 5 = η ^ 2 * η ^ 3 := by ring
      _ ≤ η ^ 2 * (1 / 10) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = η ^ 2 / 10 := by ring
  have h5 : η ^ 5 * ρ0 ≤ η ^ 5 * (Va + Vb) := mul_le_mul_of_nonneg_left hρ (by positivity)
  set m : ℝ := (1 - γ) / 2 + 3 * η / 2 + 3 * η ^ 2 + 2 * η ^ 5 with hm
  have hm0 : 0 ≤ m := by positivity
  have hc1 : m ≤ (γ - 5 * η) / 2 - η ^ 5 := by linarith [pow_pos hη 2, pow_pos hη 5]
  have hc2 : m ≤ 1 - γ + 2 * η ^ 2 - η ^ 5 := by linarith [pow_pos hη 2, pow_pos hη 5]
  have hu : 0 ≤ Va - 1 := by linarith
  have hw : 0 ≤ Vb - 1 := by linarith
  nlinarith [mul_nonneg hu (sub_nonneg.mpr hc1), mul_nonneg hw (sub_nonneg.mpr hc2),
    mul_nonneg hm0 (by linarith : (0:ℝ) ≤ (Va - 1) + (Vb - 1) - 1)]

section cases
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem countA_zero_of_noAdm {d : ℕ} (M : Molecule V D) (L γ δ C1 : ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (hA : ∀ κ, ¬ Adm κ) : M.countA L γ δ C1 (0 : Mom d) Adm P = 0 := by
  unfold Molecule.countA Molecule.countE
  have : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d),
      {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}.encard = 0 := by
    intro c β k0
    rw [Set.encard_eq_zero]
    ext κ; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun h => hA κ h.2.2
  simp [this]

/-- gap lower bound at an atom of degree two (in = out = 1) from a bound on opposite pairs. -/
theorem hAdm_of_atom {d : ℕ} (M : Molecule V D) {L ρ : ℝ} (Adm : (D → (Fin d → ℤ)) → Prop) {a : V}
    (ha : a ∈ M.atoms) (hdeg : M.deg a = 2)
    (h : ∀ κ, Adm κ → ∀ x y, M.atom x = a → M.atom y = a → x ≠ y →
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖) :
    ∀ κ, Adm κ → ∃ y y', M.atom y ∈ M.atoms ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      ρ ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := by
  intro κ hκ
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_darts M hdeg
  exact ⟨x, y, hx ▸ ha, hy.trans hx.symm, hxy, h κ hκ x y hx hy hxy⟩

/-- **The double bond** (L1854-L1855): it is vine (I), hence LG; both atoms are `β`. -/
theorem cycle_double {d : ℕ} (hd : 3 ≤ d) {L γ η δ C1 : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (hη : 0 < η)
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
  have hγ0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  have hηs : η ≤ (1 - γ) / 200 := by rw [hγ0] at hη1; exact hη1
  have hη10 : η ≤ 1 / 10 := by linarith [hγ.1, hγ.2]
  -- X ≤ L^{-η/2}
  have hX1 : ((d : ℝ) * δ⁻¹ * (L ^ (-γ + η))⁻¹ * L ^ (-γ)) = (d : ℝ) * δ⁻¹ * L ^ (-η) := by
    rw [← Real.rpow_neg hLp.le, mul_assoc, ← Real.rpow_add hLp]; congr 2; ring
  have hX2 : L ^ (γ - 1) ≤ L ^ (-η) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
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
  have hη2 : η ^ 2 ≤ η / 10 := by
    have hη10 : η ≤ 1 / 10 := by have := min_le_right γ (1 - γ); linarith [hγ.1]
    calc η ^ 2 = η * η := sq η
      _ ≤ η * (1 / 10) := mul_le_mul_of_nonneg_left hη10 hη.le
      _ = η / 10 := by ring
  nlinarith [mul_le_mul_of_nonneg_left hρ0 (by positivity : (0:ℝ) ≤ η ^ 5)]


/-- A nonzero gap has norm at least `L⁻¹` (lattice spacing). -/
theorem gap_lower_of_ne {d : ℕ} {L : ℝ} (hL : 0 < L) {κ : D → (Fin d → ℤ)} {x y : D}
    (h : Molecule.gapAt L (0 : Mom d) κ x y ≠ 0) :
    L⁻¹ ≤ ‖Molecule.gapAt L (0 : Mom d) κ x y‖ := by
  have hne : κ x - κ y ≠ 0 := by
    intro h0
    apply h
    have : κ x = κ y := sub_eq_zero.mp h0
    simp [Molecule.gapAt, Molecule.kvec, this]
  have : Molecule.gapAt L (0 : Mom d) κ x y = latticePoint L (κ x - κ y) := by
    simp [Molecule.gapAt, Molecule.kvec, latticePoint_sub']
  rw [this]
  exact inv_le_norm_latticePoint hL hne


/-- **A cycle of length `≥ 3` without `α`-atom** (L1859-L1860). -/
theorem cycle_noalpha {d : ℕ} (hd : 3 ≤ d) {L γ η δ C1 : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (hη : 0 < η)
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
  refine (cycle_countA_le (by omega) hL hδ hC1 hρ M hS.nonempty hch hS.conn P Adm hAdm hMA).trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hγ0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  have hηs : η ≤ (1 - γ) / 200 := by rw [hγ0] at hη1; exact hη1
  have hδ0 := hδ.1
  have hX1 : ((d : ℝ) * δ⁻¹ * (L⁻¹)⁻¹ * L ^ (-γ)) = (d : ℝ) * δ⁻¹ * L ^ (1 - γ) := by
    rw [inv_inv, mul_assoc, show (1 - γ) = 1 + -γ by ring, Real.rpow_add hLp, Real.rpow_one]
  have hX2 : L ^ (γ - 1) ≤ L ^ (1 - γ) := Real.rpow_le_rpow_of_exponent_le hL (by linarith [hγ.2])
  have hX3 : (3:ℝ) ^ d * ((d : ℝ) * δ⁻¹ * (L⁻¹)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) ≤ L ^ (η ^ 2 / 4) * L ^ (1 - γ) := by
    rw [hX1]
    calc _ ≤ (3:ℝ) ^ d * ((d : ℝ) * δ⁻¹ * L ^ (1 - γ) + L ^ (1 - γ)) := by gcongr
      _ = (3:ℝ) ^ d * ((d : ℝ) * δ⁻¹ + 1) * L ^ (1 - γ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hLp.le _)
  refine hX3.trans ?_
  rw [← Real.rpow_add hLp]
  refine le_trans ?_ (finalRHS_ge M cls odd hL hη.le hF.labRange)
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  rw [hVa, hVb, if_neg hnodd]
  have hρ0 : (M.rho : ℝ) ≤ (M.atoms.card : ℝ) := by
    exact_mod_cast rho_le_card_of_deg_le_two M (fun a ha => (hdeg a ha).le)
  have hs3 : (3 : ℝ) ≤ (M.atoms.card : ℝ) := by exact_mod_cast hcard
  have hη5 : η ^ 5 ≤ η ^ 2 / 10 := by
    have h1 : η ^ 3 ≤ 1 / 10 := by
      have : η ≤ 1 / 100 := by linarith [hγ.1, hγ.2, hηs]
      exact (pow_le_of_le_one hη.le (by linarith) (by norm_num)).trans (by linarith)
    calc η ^ 5 = η ^ 2 * η ^ 3 := by ring
      _ ≤ η ^ 2 * (1 / 10) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = η ^ 2 / 10 := by ring
  rw [hγ0]
  nlinarith [mul_le_mul_of_nonneg_left hρ0 (by positivity : (0:ℝ) ≤ η ^ 5), pow_pos hη 2]


/-- **A cycle of length `≥ 3` with an `α`-atom** (L1860-L1862). -/
theorem cycle_alpha {d : ℕ} (hd : 3 ≤ d) {L γ η δ C1 : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (hη : 0 < η)
    (hη1 : η ≤ min γ (1 - γ) / 200) (hη2 : η ≤ (2 * γ - 1) / 100) (hL : 1 ≤ L) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1)
    (hC1 : 1 ≤ C1) (hK1 : 4 * 3 ^ d * (d * δ⁻¹) ≤ L ^ ((2 * γ - 1) / 2)) (hK2 : 2 * 3 ^ d ≤ L ^ (1 / 2 - η))
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
  have hγ0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  have hηs : η ≤ (1 - γ) / 200 := by rw [hγ0] at hη1; exact hη1
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
    ((1 - γ + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) - (2 * (1 - γ) + 5 * η ^ 2) * 1) +
    (-(η ^ 5) * (M.rho : ℝ)) with hrest
  have hrest_ge : (2 * γ - 1) / 2 - (γ - 3 * η) / 2 ≤ rest :=
    rest_ge_real hγ.1 hγ.2 hη hηs hη2 hVa1' hVb1' hs3 (by rw [hVsum]; exact hρ0)
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
    have h1 : 4 * 3 ^ d * ((d : ℝ) * δ⁻¹) * (R0⁻¹ * L ^ (-γ)) ≤ L ^ ((2 * γ - 1) / 2) * (R0⁻¹ * L ^ (-γ)) :=
      mul_le_mul_of_nonneg_right hK1 (by positivity)
    have h2 : L ^ ((2 * γ - 1) / 2) * (R0⁻¹ * L ^ (-γ)) ≤ T := by
      calc _ = R0⁻¹ * L ^ ((2 * γ - 1) / 2 + -γ) := by rw [Real.rpow_add hLp]; ring
        _ ≤ R0⁻¹ * L ^ (-(γ + 3 * η) / 2 + rest) := by
            refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL ?_) (inv_nonneg.mpr hR0pos.le)
            linarith
        _ = T := by rw [hT, Real.rpow_add hLp]; ring
    have : (R0 / 2)⁻¹ = 2 * R0⁻¹ := by rw [inv_div]; field_simp
    rw [this]
    linarith only [h1, h2]
  have hterm2 : 3 ^ d * L ^ (γ - 1) ≤ T / 2 := by
    have h1 : 2 * 3 ^ d * L ^ (γ - 1) ≤ L ^ (1 / 2 - η) * L ^ (γ - 1) :=
      mul_le_mul_of_nonneg_right hK2 (Real.rpow_nonneg hLp.le _)
    have h2 : L ^ (1 / 2 - η) * L ^ (γ - 1) ≤ T := by
      calc _ = L ^ ((2 * γ - 1) / 2 - η) := by rw [← Real.rpow_add hLp]; congr 1; ring
        _ ≤ L ^ ((γ - η) + (-(γ + 3 * η) / 2 + rest)) :=
            Real.rpow_le_rpow_of_exponent_le hL (by linarith)
        _ = L ^ (γ - η) * L ^ (-(γ + 3 * η) / 2) * L ^ rest := by
            rw [Real.rpow_add hLp, Real.rpow_add hLp]; ring
        _ ≤ R0⁻¹ * L ^ (-(γ + 3 * η) / 2) * L ^ rest := by gcongr
        _ = T := by rw [hT]; ring
    linarith
  calc 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1))
      = 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ)) + 3 ^ d * L ^ (γ - 1) := by ring
    _ ≤ T / 2 + T / 2 := add_le_add hterm1 hterm2
    _ = T := by ring


theorem two_le_card_of_loopfree (M : Molecule V D) (hloop : ∀ x, M.atom x ≠ M.atom (M.mate x))
    (hdeg : ∀ a ∈ M.atoms, 1 ≤ M.deg a) (hne : M.atoms.Nonempty) : 2 ≤ M.atoms.card := by
  classical
  obtain ⟨a, ha⟩ := hne
  have h1 := hdeg a ha
  unfold Molecule.deg at h1
  obtain ⟨x, hx⟩ := card_pos.mp h1
  have hxa : M.atom x = a := by simpa [Molecule.dartsAt] using hx
  have hb : M.atom (M.mate x) ∈ M.atoms := M.atom_mem _
  have hne' : M.atom (M.mate x) ≠ a := fun h => hloop x (hxa.trans h.symm)
  by_contra hlt
  push Not at hlt
  have : ({a, M.atom (M.mate x)} : Finset V) ⊆ M.atoms := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
  have := card_le_card this
  rw [card_pair hne'.symm] at this
  omega

end cases

/-- **Cycles** (DH23 L1854-L1862): all three cases, with the thresholds in `L`. -/
theorem cycle_case (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ min γ (1 - γ) / 200) (hη2 : η ≤ (2 * γ - 1) / 100) (δ : ℝ) (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀, ∀ C1 : ℝ, 1 ≤ C1 →
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (∀ a ∈ M.atoms, M.deg a = 2) →
        MaxLadderGapAdm M L (0 : Mom d) P (MoleProp.GapScale L) Adm →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  have hη1' : 0 < η ^ 2 / 4 := by positivity
  have hγ12 : 0 < (2 * γ - 1) / 2 := by linarith [hγ.1]
  have hηs : η ≤ (1 - γ) / 200 := by
    have : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1]); rw [this] at hη1; exact hη1
  have hη01 : η ≤ 1 / 100 := by linarith [hγ.1, hγ.2]
  obtain ⟨R1, hR1, h1⟩ := const_le_rpow (C := 3 ^ d * (d * δ⁻¹ + 1)) (ε := η / 2) (by have := hδ.1; positivity)
    (by positivity)
  obtain ⟨R2, hR2, h2⟩ := const_le_rpow (C := 3 ^ d * (d * δ⁻¹ + 1)) (ε := η ^ 2 / 4) (by have := hδ.1; positivity) hη1'
  obtain ⟨R3, hR3, h3⟩ := const_le_rpow (C := 4 * 3 ^ d * (d * δ⁻¹)) (ε := (2 * γ - 1) / 2) (by have := hδ.1; positivity) hγ12
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
  · exact cycle_double hd hγ hη hη1 hL1 hδ hC1 (h1 L hLR1) M cls odd Adm P hS hF hdeg hc hA hMA
  · have hc3 : 3 ≤ M.atoms.card := by omega
    by_cases hα : ∃ v₀, v₀ ∈ alphaAtoms M.atoms cls
    · obtain ⟨v₀, hv₀⟩ := hα
      exact cycle_alpha hd hγ hη hη1 hη2 hL1 hδ hC1 (h3 L hLR3) (h4 L hLR4) M cls odd Adm P hS hF hdeg hc3 hv₀ hMA
    · push Not at hα
      exact cycle_noalpha hd hγ hη hη1 hL1 hδ hC1 (h2 L hLR2) M cls odd Adm P hS hF hdeg hc3
        (eq_empty_of_forall_notMem hα) hMA

end WaveTurbulence.FinalCountG8
