/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VineExcess5`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 Vine removal, part 13 (FINALCOUNT-G2): **DH23 Prop 9.4, Step 1, a VC formed by two double bonds**, conditional on the
count (L1801 last sentence). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace VineCut
open WaveTurbulence.FinalCount.VineCut
variable {M : Molecule V D} (K : VineCut g M)

/-- **DH23 Prop 9.4, Step 1, `𝕍ℂ` formed by two double bonds** (`4` bonds on `3` atoms, `Δχ = -3`; no ladder inside),
given the count of its labels (`hcount`). -/
theorem vine_excess_double (hd : 3 ≤ d) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ C₁ η : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ) (hγ1 : γ < 1)
    (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 4) (hA : K.C.atoms.card = 3) (hlad : K.vc.maximalLadders = ∅)
    (R : ℝ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (Cf : ℝ) (hCf : 0 ≤ Cf) (e : ℕ)
    (hcount : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (K.labelSet L γ δ w Adm c β k0).encard ≤ ENNReal.ofReal (vineG d L γ δ R ρ Cf e)) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (K.post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((Cf * (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1)) * (1 + δ⁻¹)) *
        excessRHS L γ η [(R, κ), (R, κ)] 0 0)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hlog1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  have hR : 0 < R := lt_of_lt_of_le (inv_pos.2 hL0) hRl
  have hρ0 : 0 ≤ ρ := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · linarith
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR.le
  have hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (K.labelSet L γ δ w Adm c β k0).encard ≤ ((⌊vineG d L γ δ R ρ Cf e⌋₊ : ℕ) : ℕ∞) :=
    fun c β k0 hp => encard_le_floor (hcount c β k0 hp)
  have h := K.vine_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P hL hδ hC hP0 hP1 hP2 _ hN
  have hrk : M.circuitRank - K.post.circuitRank = ((3 : ℕ) : ℤ) := by
    rw [K.circuitRank_diff_gen hF, hB, hA]; norm_num
  rw [hrk] at h
  refine isDeviation_mono h ?_
  have hΛ : ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S = 1 := by
    rw [hlad]; simp
  rw [hΛ, mul_one]
  have hNx : ((⌊vineG d L γ δ R ρ Cf e⌋₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal (rankFactor d L γ δ C₁ ((3 : ℕ) : ℤ) * Real.log L ^ 8) =
      ENNReal.ofReal ((⌊vineG d L γ δ R ρ Cf e⌋₊ : ℝ) * (rankFactor d L γ δ C₁ ((3 : ℕ) : ℤ) * Real.log L ^ 8)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hNx, excessRHS_alpha]
  refine ENNReal.ofReal_le_ofReal ?_
  have hreal := vine_real_double d e (γ := γ) (C₁ := C₁) (ρ := ρ) (Cf := Cf) (R := R) (by omega) hL1 hδ hδ1 hC hR hρ0 hCf hlog1
  have hT1 : ρ ^ d * L ^ (3 * γ - 1) * Real.log L ^ (e + 8) ≤
      (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1)) *
        (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) ^ 2) ∧
      ρ ^ d * R⁻¹ * L ^ γ * Real.log L ^ (e + 8) ≤
      (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1)) *
        (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) ^ 2) := by
    rcases hρ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have a1 := vine_arith_t1 d (e + 8) (a := 0) hd hη hη1 hηγ hγ1 le_rfl hL hR.le hRu hρ0 (by simp)
      have a2 := vine_arith_t2 d (e + 8) (a := 0) hd hη hη1 hηγ le_rfl hL hR hRu hρ0 (by simp)
      exact ⟨by simpa using a1, by simpa using a2⟩
    · have hρa : L ^ (-50 * η) * R ≤ 2 * L ^ (-(50 * η)) * R := by
        rw [show -50 * η = -(50 * η) by ring]
        nlinarith [mul_nonneg (Real.rpow_nonneg hL0.le (-(50 * η))) hR.le]
      have a1 := vine_arith_t1 d (e + 8) (a := 50 * η) hd hη hη1 hηγ hγ1 (by linarith) hL hR.le hRu hρ0 hρa
      have a2 := vine_arith_t2 d (e + 8) (a := 50 * η) hd hη hη1 hηγ (by linarith) hL hR hRu hρ0 hρa
      exact ⟨by simpa using a1, by simpa using a2⟩
  obtain ⟨hT1, hT2⟩ := hT1
  set T := (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1)) *
        (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) ^ 2) with hT
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ.le
  calc _ ≤ Cf * (ρ ^ d * L ^ (3 * γ - 1) * Real.log L ^ (e + 8)) +
        δ⁻¹ * (Cf * (ρ ^ d * R⁻¹ * L ^ γ * Real.log L ^ (e + 8))) := hreal
    _ ≤ Cf * T + δ⁻¹ * (Cf * T) := by
        gcongr
    _ = _ := by rw [hT]; ring

end VineCut
end WaveTurbulence.GammaLow.FinalCount.Step1
