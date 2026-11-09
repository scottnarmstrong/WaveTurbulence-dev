/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCExcess
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCExcess`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 0: the re-scoped vine label count `VineCountInput'` and Step 1 of DH23 Prop 9.4 from it
(R17; DH23 L1797--L1801).

Changes with respect to `FinalCount.VineCountInput` / `VineCut.vine_excess_single` (ruling R17):
* `vineF'` carries `C₂ ^ m` (the dimension constant per interior atom, absorbed in the source by "`C₁` large",
  `C₂ ≤ C₁`);
* the extra premises of the count (shape `.vc`, single vine, ladder scales in `Adm`, lower gap bound) are premises of
  the theorems producing `VineCountInput'` (`VCCount`), not of its statement. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **The vine label count (L1799--L1801), single vine, re-scoped (R17).** -/
def VineCountInput' {M : Molecule V D} (K : VineCut g M) (L γ δ ρ Cf C₂ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (e : ℕ) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    (K.labelSet L γ δ w Adm c β k0).encard ≤
      ENNReal.ofReal (vineF' d L γ δ ρ Cf C₂ (K.ladderProdVC L γ δ P) K.C.atoms.card e)

/-- **DH23 Prop 9.4, Step 1, a single vine, given the re-scoped count `𝔉`** (L1797--L1801) -- `VineExcess3'`. -/
theorem vine_excess_single' {M : Molecule V D} (K : VineCut g M) (hd : 3 ≤ d)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ C₁ C₂ η : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop)
    (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1)) (P : Finset V → ℝ)
    (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 1 ≤ C₁) (hC₂ : 0 ≤ C₂) (hle : C₂ ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hη : 0 < η) (hη1 : η < 1) (hηγ : η ≤ γ)
    (hF : K.post.numComponents = M.numComponents)
    (hB : K.vc.bonds.card = 2 * (K.C.atoms.card - 1)) (hm : 2 ≤ K.C.atoms.card)
    (R : ℝ) (hR0 : 0 ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (ρ : ℝ)
    (hρ : (κ = 0 ∧ ρ = 2 * R) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * R))
    (Cf : ℝ) (hCf : 0 ≤ Cf) (e : ℕ) (hcount : VineCountInput' K L γ δ ρ Cf C₂ w Adm P e) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (K.post.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal ((Cf * (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1))) *
        excessRHS L γ η [(R, κ), (R, κ)] 0 0)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hlog1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  have hΛ1 := K.ladderProdVC_ge_one L γ δ P hL hδ.le hP0
  have hΛ0 : 0 < K.ladderProdVC L γ δ P := lt_of_lt_of_le zero_lt_one hΛ1
  set Λ := K.ladderProdVC L γ δ P with hΛ
  set m := K.C.atoms.card with hmdef
  set Fv := vineF' d L γ δ ρ Cf C₂ Λ m e with hFv
  have hN : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      (K.labelSet L γ δ w Adm c β k0).encard ≤ ((⌊Fv⌋₊ : ℕ) : ℕ∞) :=
    fun c β k0 hp => encard_le_floor (hcount c β k0 hp)
  have h := K.vine_isDeviation hM L γ δ C₁ w Adm Adm' hAdm' P hL hδ hC hP0 hP1 hP2 ⌊Fv⌋₊ hN
  have hrk : M.circuitRank - K.post.circuitRank = ((m : ℕ) : ℤ) := K.circuitRank_diff_card hF hB (by omega)
  rw [hrk] at h
  refine isDeviation_mono h ?_
  have hρ0 : 0 ≤ ρ := by
    rcases hρ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · linarith
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _) hR0
  rw [rankFactor_nat d L γ δ C₁ hL0 m]
  have hΛd : ∏ S ∈ K.vc.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S = Λ := rfl
  rw [hΛd]
  have hNx : ((⌊Fv⌋₊ : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((L ^ (-((d : ℝ) - γ))) ^ m * qq δ C₁ ^ m * Real.log L ^ 8 * Λ) =
      ENNReal.ofReal ((⌊Fv⌋₊ : ℝ) * ((L ^ (-((d : ℝ) - γ))) ^ m * qq δ C₁ ^ m * Real.log L ^ 8 * Λ)) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [hNx, excessRHS_alpha]
  refine ENNReal.ofReal_le_ofReal ?_
  have hreal := vine_real' d m e (γ := γ) (C₁ := C₁) (C₂ := C₂) (ρ := ρ) (Cf := Cf) hL1 hδ hC hC₂ hle hρ0 hCf hΛ0 hlog1
  have harith : ρ ^ d * L ^ (2 * γ) * Real.log L ^ (e + 8) ≤
      (2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1)) *
        (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) ^ 2) := by
    rcases hρ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := vine_arith d (e + 8) (a := 0) hd hη hη1 hηγ le_rfl hL hR0 hRu hρ0 (by simp)
      simpa using this
    · have := vine_arith d (e + 8) (a := 50 * η) hd hη hη1 hηγ (by linarith) hL hR0 hRu
        hρ0 (by
          rw [show -50 * η = -(50 * η) by ring]
          nlinarith [mul_nonneg (Real.rpow_nonneg hL0.le (-(50 * η))) hR0])
      simpa using this
  calc _ ≤ Cf * (ρ ^ d * L ^ (2 * γ) * Real.log L ^ (e + 8)) := hreal
    _ ≤ Cf * ((2 ^ d * (((e + 8 + 1 : ℕ) : ℝ) / (2 * η - η ^ 3)) ^ (e + 8 + 1)) *
        (L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) ^ 2)) := mul_le_mul_of_nonneg_left harith hCf
    _ = _ := by ring

end WaveTurbulence.GammaLow.FinalCount.Step1
