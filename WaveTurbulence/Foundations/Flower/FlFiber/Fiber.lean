/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LatticeBox
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# FL-FIBER: supplement Lemma 7.1

Localized spectral fibers and the mixed-norm conversion (7.1).

* `localizedTuples`: tuples of lattice points of `ℤ_L^d` each in a unit ball around a real center.
* `card_localizedTuples_le`: at most `(2L+1)^(|ι| d)` of them.
* `ncard_values_le`: for every function `Ω` of the tuple, the value set has at most `(3L)^(4d)`
  elements when `|ι| ≤ 4` and `L ≥ 1` (so `C_d = 3`).
* `exists_cover_values`: the `α`-values are covered by that many intervals of a fixed length.
* `setLIntegral_integral_le`, `setIntegral_integral_le`: the bound (7.1).
-/

public section

open MeasureTheory

namespace WaveTurbulence.Flower.FlFiber

open WaveTurbulence WaveTurbulence.Counting

variable {d : ℕ}

/-- Tuples (indexed by `ι`) of integer vectors whose lattice points `n/L` lie in the closed unit
balls around the centers `c j`. -/
@[expose] def localizedTuples {ι : Type*} [Fintype ι] (L : ℝ) (c : ι → Mom d) :
    Set (ι → Fin d → ℤ) :=
  {n | ∀ j, ‖latticePoint L (n j) - c j‖ ≤ 1}

theorem localizedTuples_subset {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℝ} (hL : 0 < L) (c : ι → Mom d) :
    localizedTuples L c ⊆
      ↑(Fintype.piFinset fun j => latticeBox (fun i => L * c j i) L) := by
  intro n hn
  simp only [Finset.mem_coe, Fintype.mem_piFinset, mem_latticeBox]
  intro j i
  have h1 : ‖(latticePoint L (n j) - c j) i‖ ≤ ‖latticePoint L (n j) - c j‖ :=
    PiLp.norm_apply_le _ i
  have h2 := h1.trans (hn j)
  have h3 : (latticePoint L (n j) - c j) i = (n j i : ℝ) / L - c j i := rfl
  rw [h3, Real.norm_eq_abs] at h2
  have h4 : (n j i : ℝ) - L * c j i = L * ((n j i : ℝ) / L - c j i) := by field_simp
  rw [h4, abs_mul, abs_of_pos hL]
  nlinarith [abs_nonneg ((n j i : ℝ) / L - c j i)]

/-- The localized tuples are finite. -/
theorem finite_localizedTuples {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (c : ι → Mom d) :
    (localizedTuples L c).Finite := by
  classical
  exact (Finset.finite_toSet _).subset (localizedTuples_subset hL c)

/-- At most `(2L+1)^(|ι| d)` localized tuples. -/
theorem ncard_localizedTuples_le {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (c : ι → Mom d) :
    ((localizedTuples L c).ncard : ℝ) ≤ (2 * L + 1) ^ (Fintype.card ι * d) := by
  classical
  have h1 : (localizedTuples L c).ncard ≤
      (Fintype.piFinset fun j => latticeBox (fun i => L * c j i) L).card := by
    have := Set.ncard_le_ncard (localizedTuples_subset hL c) (Finset.finite_toSet _)
    rwa [Set.ncard_coe_finset] at this
  rw [Fintype.card_piFinset] at h1
  calc ((localizedTuples L c).ncard : ℝ)
      ≤ ((∏ j, (latticeBox (fun i => L * c j i) L).card : ℕ) : ℝ) := by exact_mod_cast h1
    _ = ∏ j, (((latticeBox (fun i => L * c j i) L).card : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∏ _j : ι, (2 * L + 1) ^ d :=
        Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
          (fun j _ => card_latticeBox_le _ hL.le)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm d]

/-- **Lemma 7.1, counting.** For any function `Ω` of the incident momenta (`|ι| ≤ 4` of them, each
in a unit ball of a translate of `ℤ_L^d`), the set of values has at most `(3L)^(4d)` elements,
uniformly in the centers. -/
theorem ncard_values_le {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4) {L : ℝ} (hL : 1 ≤ L)
    (c : ι → Mom d) (Ω : (ι → Mom d) → ℝ) :
    (((fun n : ι → Fin d → ℤ => Ω fun j => latticePoint L (n j)) '' localizedTuples L c).Finite) ∧
    ((((fun n : ι → Fin d → ℤ => Ω fun j => latticePoint L (n j)) ''
        localizedTuples L c).ncard : ℕ) : ℝ) ≤ (3 * L) ^ (4 * d) := by
  have hL0 : 0 < L := by linarith
  refine ⟨(finite_localizedTuples hL0 c).image _, ?_⟩
  have h1 := Set.ncard_image_le (f := fun n : ι → Fin d → ℤ => Ω fun j => latticePoint L (n j))
    (finite_localizedTuples hL0 c)
  have h2 := ncard_localizedTuples_le hL0 c
  have h3 : (2 * L + 1) ≤ 3 * L := by linarith
  calc _ ≤ ((localizedTuples L c).ncard : ℝ) := by exact_mod_cast h1
    _ ≤ (2 * L + 1) ^ (Fintype.card ι * d) := h2
    _ ≤ (2 * L + 1) ^ (4 * d) :=
        pow_le_pow_right₀ (by linarith) (Nat.mul_le_mul_right _ hι)
    _ ≤ (3 * L) ^ (4 * d) := pow_le_pow_left₀ (by linarith) h3 _

/-- **Lemma 7.1, covering.** The values `α = a * Ω` (`a = δ L^{2γ}`) are covered by at most
`(3L)^(4d)` intervals `[p, p + c]` of any fixed length `c ≥ 0`. -/
theorem exists_cover_values {ι : Type*} [Fintype ι] (hι : Fintype.card ι ≤ 4) {L : ℝ}
    (hL : 1 ≤ L) (c : ι → Mom d) (Ω : (ι → Mom d) → ℝ) (a ℓ : ℝ) (hℓ : 0 ≤ ℓ) :
    ∃ P : Finset ℝ, (P.card : ℝ) ≤ (3 * L) ^ (4 * d) ∧
      ∀ n ∈ localizedTuples L c,
        ∃ p ∈ P, a * Ω (fun j => latticePoint L (n j)) ∈ Set.Icc p (p + ℓ) := by
  obtain ⟨hf, hc⟩ := ncard_values_le hι hL c (fun x => a * Ω x)
  refine ⟨hf.toFinset, ?_, ?_⟩
  · rw [← Set.ncard_eq_toFinset_card _ hf]; exact hc
  · intro n hn
    exact ⟨_, hf.mem_toFinset.mpr ⟨n, hn, rfl⟩, by simp [hℓ]⟩

/-- A union of at most `Q` order-connected sets, each of length at most `ℓ`, has measure at most
`Q ℓ`. -/
theorem volume_iUnion_le {Q : ℕ} {ℓ : ℝ} (I : Fin Q → Set ℝ)
    (hI : ∀ q, volume (I q) ≤ ENNReal.ofReal ℓ) :
    volume (⋃ q, I q) ≤ ENNReal.ofReal (Q * ℓ) := by
  refine (measure_iUnion_fintype_le _ _).trans ?_
  refine (Finset.sum_le_sum fun q _ => hI q).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]; simp

/-- The allowed region: each of `b` exceptional variables lies in a union of at most `Q`
intervals `I i q` of length at most `ℓ`. -/
@[expose] def allowedRegion {b Q : ℕ} (I : Fin b → Fin Q → Set ℝ) : Set (Fin b → ℝ) :=
  Set.pi Set.univ fun i => ⋃ q, I i q

theorem measurableSet_allowedRegion {b Q : ℕ} (I : Fin b → Fin Q → Set ℝ)
    (hI : ∀ i q, (I i q).OrdConnected) : MeasurableSet (allowedRegion I) :=
  MeasurableSet.univ_pi fun i =>
    MeasurableSet.iUnion fun q => (hI i q).measurableSet

theorem volume_allowedRegion_le {b Q : ℕ} {ℓ : ℝ} (I : Fin b → Fin Q → Set ℝ)
    (hI : ∀ i q, volume (I i q) ≤ ENNReal.ofReal ℓ) :
    volume (allowedRegion I) ≤ ENNReal.ofReal (ℓ * Q) ^ b := by
  rw [allowedRegion, volume_pi, Measure.pi_pi]
  calc ∏ i, volume (⋃ q, I i q) ≤ ∏ _i : Fin b, ENNReal.ofReal (ℓ * Q) :=
        by
          gcongr with i
          simpa [mul_comm] using volume_iUnion_le (I i) (hI i)
    _ = _ := by simp

variable {J E : Type*} [MeasurableSpace J] [NormedAddCommGroup E]

/-- **Lemma 7.1, (7.1), `lintegral` form.** The iterated integral of `‖B‖` over the allowed region
is at most `(ℓ Q)^b` times the supremum of the inner integral over the allowed `α_E`. -/
theorem setLIntegral_integral_le {b Q : ℕ} {ℓ : ℝ} (I : Fin b → Fin Q → Set ℝ)
    (hO : ∀ i q, (I i q).OrdConnected)
    (hI : ∀ i q, volume (I i q) ≤ ENNReal.ofReal ℓ) (μ : Measure J)
    (B : (Fin b → ℝ) → J → E) :
    ∫⁻ x in allowedRegion I, ∫⁻ y, ‖B x y‖ₑ ∂μ ≤
      ENNReal.ofReal (ℓ * Q) ^ b *
        ⨆ x ∈ allowedRegion I, ∫⁻ y, ‖B x y‖ₑ ∂μ := by
  calc ∫⁻ x in allowedRegion I, ∫⁻ y, ‖B x y‖ₑ ∂μ
      ≤ ∫⁻ _x in allowedRegion I, ⨆ x ∈ allowedRegion I, ∫⁻ y, ‖B x y‖ₑ ∂μ :=
        setLIntegral_mono' (measurableSet_allowedRegion I hO) fun x hx =>
          le_iSup₂ (f := fun x (_ : x ∈ allowedRegion I) => ∫⁻ y, ‖B x y‖ₑ ∂μ) x hx
    _ = (⨆ x ∈ allowedRegion I, ∫⁻ y, ‖B x y‖ₑ ∂μ) * volume (allowedRegion I) :=
        setLIntegral_const _ _
    _ ≤ (⨆ x ∈ allowedRegion I, ∫⁻ y, ‖B x y‖ₑ ∂μ) * ENNReal.ofReal (ℓ * Q) ^ b :=
        mul_le_mul_right (volume_allowedRegion_le I hI) _
    _ = _ := mul_comm _ _

/-- **Lemma 7.1, (7.1), real form.** If the inner integral is at most `M` on the allowed region,
the double integral is at most `(ℓ Q)^b M`. -/
theorem setIntegral_integral_le {b Q : ℕ} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (I : Fin b → Fin Q → Set ℝ)
    (hO : ∀ i q, (I i q).OrdConnected)
    (hI : ∀ i q, volume (I i q) ≤ ENNReal.ofReal ℓ) (μ : Measure J)
    (B : (Fin b → ℝ) → J → E) {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ x ∈ allowedRegion I, ∫ y, ‖B x y‖ ∂μ ≤ M) :
    ∫ x in allowedRegion I, ∫ y, ‖B x y‖ ∂μ ≤ (ℓ * Q) ^ b * M := by
  have hA := measurableSet_allowedRegion I hO
  have hv : volume (allowedRegion I) ≤ ENNReal.ofReal ((ℓ * Q) ^ b) := by
    refine (volume_allowedRegion_le I hI).trans ?_
    rw [ENNReal.ofReal_pow (by positivity)]
  have hfin : volume (allowedRegion I) < ⊤ := hv.trans_lt ENNReal.ofReal_lt_top
  by_cases hint : IntegrableOn (fun x => ∫ y, ‖B x y‖ ∂μ) (allowedRegion I)
  · calc ∫ x in allowedRegion I, ∫ y, ‖B x y‖ ∂μ
        ≤ ∫ _x in allowedRegion I, M :=
          setIntegral_mono_on hint (integrableOn_const hfin.ne) hA hB
      _ = M * (volume (allowedRegion I)).toReal := by simp [Measure.real, mul_comm]
      _ ≤ M * (ℓ * Q) ^ b := by
          refine mul_le_mul_of_nonneg_left ?_ hM
          have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
          rwa [ENNReal.toReal_ofReal (by positivity)] at this
      _ = _ := mul_comm _ _
  · rw [integral_undef hint]; positivity

end WaveTurbulence.Flower.FlFiber
