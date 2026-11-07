/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.PairCount
public import WaveTurbulence.Foundations.FinalCount.Pair33Count
public import WaveTurbulence.Foundations.FinalCount.ErasePair
import Mathlib.Tactic

/-! # `PairGainAt`, the `(3,4)` double-bond branch (DH23 L1965, Lemma A.3(4))

`𝔈(M) ≤ ⌈C δ⁻² L^{3(d−γ)−γ₀}⌉ · 𝔈(M ∖ {a,b})` (G6's five-label count) and `Δχ = −3` give
`𝔄(M) ≤ (C δ⁻² + 1) (C₁⁻¹ δ^{1/2})³ (log L)^8 L^{−γ₀} · 𝔄*(M ∖ {a,b})`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

/-- Absorbing the ceiling and the exponents: `⌈c L^e⌉ L^{−e'}…`. -/
theorem ceil_mul_le {c e : ℝ} (hc : 0 ≤ c) {L : ℝ} (hL : 1 ≤ L) (he : 0 ≤ e) :
    ((⌈c * L ^ e⌉₊ : ℕ) : ℝ) ≤ (c + 1) * L ^ e := by
  have h1 : (1 : ℝ) ≤ L ^ e := Real.one_le_rpow hL he
  have := Nat.ceil_lt_add_one (mul_nonneg hc (Real.rpow_nonneg (show (0 : ℝ) ≤ L by linarith) e))
  nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ L by linarith) e]

theorem pairGain34 {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ C R : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ C1 > 0, ∀ L ≥ max R (Real.exp 1),
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (_ : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) (_ : ∀ z, M.atom z ≠ M.atom (M.mate z))
        (a b : V), a ∈ M.atoms → b ∈ M.atoms → a ≠ b → M.deg a = 3 → M.deg b = 4 → M.bondsBetween a b = 2 →
        (∀ p ∈ M.atoms, ∀ q ∈ M.atoms, M.SameComponent p q) →
        (∀ p ∈ (Degen.eraseAtoms M {a, b}).atoms, ∀ q ∈ (Degen.eraseAtoms M {a, b}).atoms,
          (Degen.eraseAtoms M {a, b}).SameComponent p q) →
        ∀ (η : ℝ) (P : Finset V → ℝ), (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) (lgAdm M L γ η P) P ≤
          ENNReal.ofReal ((C * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * Real.log L ^ 8 *
            L ^ (-min γ (1 - γ))) * AFreeSup (Degen.eraseAtoms M {a, b}) d L γ δ η C1 := by
  obtain ⟨C, R, hC, hB⟩ := pair34_count_bound d hd γ hγ
  refine ⟨C, R, hC, fun δ hδ C1 hC1 L hL V D _ _ _ M hcap hloop a b ha hb hab hda hdb hbb hconnM hconnP η P hP => ?_⟩
  classical
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hg : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  have hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4 := fun v hv => by
    have h := hcap v hv
    have hsum := Mole.outdeg_add_indeg M v
    omega
  have hmol : M.IsMolecule := isMolecule_of_connected M hcap hconnM ha (by omega)
  have hne : (Degen.eraseAtoms M {a, b}).atoms.Nonempty := erase_pair_nonempty M hloop hab (by omega)
  have hcount := hB L hLR δ hδ M hmol a ha b hb hab hda hdb hbb (lgAdm M L γ η P)
  have hr : ((M.deg a + M.deg b - M.bondsBetween a b : ℤ) - 2) = ((3 : ℕ) : ℤ) := by rw [hda, hdb, hbb]; norm_num
  have hmain := countAFree_le_erase_pair M hloop hdeg hab ha hb hconnM hconnP hne (d := d) (η := η) (C1 := C1) hL1 hlog hδ.1 hC1
    P hP (lgAdm M L γ η P) (fun κ h => h) ⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ hr hcount
  refine hmain.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hce := ceil_mul_le (c := C * δ⁻¹ ^ 2) (e := 3 * ((d : ℝ) - γ) - min γ (1 - γ)) (by have := hδ.1; positivity) hL1
    (by have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith [hγ.2, min_le_right γ (1 - γ)])
  have hexp : L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) * L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) = L ^ (-min γ (1 - γ)) := by
    rw [← Real.rpow_add hLp]; congr 1; push_cast; ring
  have hb0 : 0 ≤ (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 := by have := hδ.1; positivity
  have hlog8 : (Real.log L ^ 2) ^ 4 = Real.log L ^ 8 := by ring
  rw [hlog8]
  calc ((⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ : ℕ) : ℝ) *
        (L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * Real.log L ^ 8
      ≤ ((C * δ⁻¹ ^ 2 + 1) * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))) *
        (L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * Real.log L ^ 8 := by
        gcongr
    _ = _ := by
        rw [mul_assoc (C * δ⁻¹ ^ 2 + 1), mul_assoc, ← mul_assoc (L ^ _), hexp]; ring



theorem pairGain33 {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ C1 > 0, ∀ L ≥ max R (Real.exp 1),
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (_ : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2) (_ : ∀ z, M.atom z ≠ M.atom (M.mate z))
        (a b : V), a ∈ M.atoms → b ∈ M.atoms → a ≠ b → M.deg a = 3 → M.deg b = 3 → M.bondsBetween a b = 1 →
        (∀ p ∈ M.atoms, ∀ q ∈ M.atoms, M.SameComponent p q) →
        (∀ p ∈ (Degen.eraseAtoms M {a, b}).atoms, ∀ q ∈ (Degen.eraseAtoms M {a, b}).atoms,
          (Degen.eraseAtoms M {a, b}).SameComponent p q) →
        ∀ (η : ℝ) (P : Finset V → ℝ), (∀ T ∈ MoleProp.ladderCells M, 0 ≤ P T) →
        MoleProp.countAFree M L γ δ C1 (0 : Mom d) (lgAdm M L γ η P) P ≤
          ENNReal.ofReal ((C * δ⁻¹ ^ 2 + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 * Real.log L ^ 8 *
            L ^ (-min γ (1 - γ))) * AFreeSup (Degen.eraseAtoms M {a, b}) d L γ δ η C1 := by
  obtain ⟨C, hC, hB⟩ := pair33_count_bound d hd γ hγ
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := hB δ hδ
  refine ⟨R, fun C1 hC1 L hL V D _ _ _ M hcap hloop a b ha hb hab hda hdb hbb hconnM hconnP η P hP => ?_⟩
  classical
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hg : 0 < min γ (1 - γ) := lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
  have hdeg : ∀ v ∈ M.atoms, M.deg v ≤ 4 := fun v hv => by
    have h := hcap v hv
    have hsum := Mole.outdeg_add_indeg M v
    omega
  have hmol : M.IsMolecule := isMolecule_of_connected M hcap hconnM ha (by omega)
  have hne : (Degen.eraseAtoms M {a, b}).atoms.Nonempty := erase_pair_nonempty M hloop hab (by omega)
  have hcount := hR L hLR M hmol a ha b hb hab hda hdb hbb (lgAdm M L γ η P)
  have hr : ((M.deg a + M.deg b - M.bondsBetween a b : ℤ) - 2) = ((3 : ℕ) : ℤ) := by rw [hda, hdb, hbb]; norm_num
  have hmain := countAFree_le_erase_pair M hloop hdeg hab ha hb hconnM hconnP hne (d := d) (η := η) (C1 := C1) hL1 hlog hδ.1 hC1
    P hP (lgAdm M L γ η P) (fun κ h => h) ⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ hr hcount
  refine hmain.trans ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  have hce := ceil_mul_le (c := C * δ⁻¹ ^ 2) (e := 3 * ((d : ℝ) - γ) - min γ (1 - γ)) (by have := hδ.1; positivity) hL1
    (by have : (3 : ℝ) ≤ d := by exact_mod_cast hd
        linarith [hγ.2, min_le_right γ (1 - γ)])
  have hexp : L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) * L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) = L ^ (-min γ (1 - γ)) := by
    rw [← Real.rpow_add hLp]; congr 1; push_cast; ring
  have hb0 : 0 ≤ (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3 := by have := hδ.1; positivity
  have hlog8 : (Real.log L ^ 2) ^ 4 = Real.log L ^ 8 := by ring
  rw [hlog8]
  calc ((⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ : ℕ) : ℝ) *
        (L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * Real.log L ^ 8
      ≤ ((C * δ⁻¹ ^ 2 + 1) * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))) *
        (L ^ (-((d : ℝ) - γ) * ((3 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 3) * Real.log L ^ 8 := by
        gcongr
    _ = _ := by
        rw [mul_assoc (C * δ⁻¹ ^ 2 + 1), mul_assoc, ← mul_assoc (L ^ _), hexp]; ring


end WaveTurbulence.FinalCountG8
