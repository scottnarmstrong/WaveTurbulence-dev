/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePhysicalScalarSplit
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeadingScalarControl

/-! # The actual physical NT/Wick error vanishes at empty order -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT WithLp

/-- The original finite-dimensional zero-order sum and approximation coincide. -/
theorem tree_approxSum_eq_approxApp_zero {d : ℕ} (L μ δ γ : ℝ) (J : Finset (Fin 0))
    (C : ({j : Fin 0 // j ∉ J} → ℝ) → ℝ × ℝ → ℂ)
    (W : (Fin 0 → Mom d) → (Fin 0 → Mom d) → ℂ) (lam : ℝ × ℝ) :
    approxSum L μ W (resProfile J (fun Ω => C (ofLp Ω) lam)) =
      approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) W := by
  have hmean : (∫ Ω : EuclideanSpace ℝ {j : Fin 0 // j ∉ J}, C (ofLp Ω) lam) = C 0 lam := by
    rw [(PiLp.volume_preserving_ofLp _).integral_comp
      (MeasurableEquiv.toLp 2 (({j : Fin 0 // j ∉ J}) → ℝ)).symm.measurableEmbedding
      (fun β => C β lam),Measure.volume_pi_eq_dirac (x := (0 : {j : Fin 0 // j ∉ J} → ℝ)),integral_dirac]
  have hsum : approxSum L μ W (resProfile J (fun Ω => C (ofLp Ω) lam)) = W 0 0*C 0 lam := by
    let : Unique ((Fin 0 → Fin d → ℤ) × (Fin 0 → Fin d → ℤ)) := uniqueOfSubsingleton 0
    unfold approxSum
    rw [tsum_fintype,Fintype.sum_unique,resProfile]
    have hp (Ω : Fin 0 → ℝ) : (∏ j ∈ J, ((Fourier.chiInfinity (Ω j)/Ω j:ℝ):ℂ))=1 := by
      apply Finset.prod_eq_one
      intro j _
      exact Fin.elim0 j
    rw [hp,one_mul]
    congr 1
    · apply congrArg₂ W <;> exact Subsingleton.elim _ _
    · congr 1
      exact Subsingleton.elim _ _
  rw [hsum,approxApp,hmean,tree_singInt_eq_eval_of_zero rfl,pow_zero,one_mul]
  ring

/-- The Wick correction has no exceptional link at order zero. -/
theorem tree_normalizedWickCorrection_zero {d : ℕ} (L δ γ : ℝ)
    (z : (Fin 0 × Fin 2) → Fin d → ℤ) (β γ' : Fin 0 → Mom d) (J : Finset (Fin 0))
    (C : ({j : Fin 0 // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ) :
    normalizedWickCorrection L δ γ z β γ' J C lam=0 := by
  unfold normalizedWickCorrection
  simp

/-- The actual physical error density is identically zero at empty order. -/
theorem treePhysicalErrorScalar_zero {d : ℕ} (L δ γ : ℝ) (J : Finset (Fin 0))
    (C : ({j : Fin 0 // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ)
    (β γ' : Fin 0 → Mom d) (z : (Fin 0 × Fin 2) → Fin d → ℤ) :
    treePhysicalErrorScalar L δ γ J C lam β γ' z=0 := by
  rw [treePhysicalErrorScalar,tree_normalizedWickCorrection_zero]
  unfold localRemainder
  rw [tree_approxSum_eq_approxApp_zero,sub_self,mul_zero,add_zero,mul_zero]

/-- The empty-order identity transports through the original code's dependent link count. -/
theorem treePhysicalErrorScalar_zero_of_eq {d n : ℕ} (hn : n=0)
    (L δ γ : ℝ) (J : Finset (Fin n))
    (C : ({j : Fin n // j ∉ J} → ℝ) → ℝ × ℝ → ℂ) (lam : ℝ × ℝ)
    (β γ' : Fin n → Mom d) (z : (Fin n × Fin 2) → Fin d → ℤ) :
    treePhysicalErrorScalar L δ γ J C lam β γ' z=0 := by
  subst n
  exact treePhysicalErrorScalar_zero L δ γ J C lam β γ' z

end WaveTurbulence.RegAsymp
