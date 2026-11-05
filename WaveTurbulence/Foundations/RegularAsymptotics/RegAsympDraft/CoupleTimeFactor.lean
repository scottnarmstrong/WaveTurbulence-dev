/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ActualTimeExpansion
public import WaveTurbulence.Foundations.Sumint.TimeBridge
public import WaveTurbulence.Foundations.RegAsymp.FiniteVariableIntegral
public import WaveTurbulence.Foundations.RegAsymp.TimeCoefficientMass

/-! # The actual dominant-couple time factor has the source geometric mass -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory TTree Reg Links ClassJR Cancel Set
open scoped ENNReal

/-- DH23 (kqtermsest), time-factor part, with its literal J3 coefficient
mass. No order exponent or step-size parameter enters this constant. -/
theorem mixedRestrictionNorm00_couple_JB_le {η A : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) (hd : Q.dominant = true)
    {T : Set (Fin 2 → ℝ)} (hT : ∀ t ∈ T, ∀ i, t i ∈ Icc (0:ℝ) 1) :
    Fourier.mixedRestrictionNorm00 (1-η) T (Set.univ : Set Unit)
      (fun ts _ => (Q.JB 0 ((ts : Fin 2 → ℝ) 0) ((ts : Fin 2 → ℝ) 1) : ℂ)) ≤
      ENNReal.ofReal (2^(1-η))*Fourier.timeFourierNorm (1-η) unitSquareCutoff*
        (ENNReal.ofReal (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1))*
          ∑' k : ℕ, ENNReal.ofReal (A^k*((2*k).factorial:ℝ)/(4*k).factorial)) := by
  classical
  obtain ⟨G,hG,-,hlim⟩ := couple_time_expansion_classified hη (hη1.trans (by norm_num)) hA Q hwf
  obtain ⟨ι,hι,f,C,hf,hr,hN,hC,hmain,-,hrep⟩ := hG ∅ (Finset.empty_subset _)
  let := hι
  have hr' : Set.range f = ↑(chosenSet Q.links) := by simpa only [Finset.sdiff_empty] using hr
  have heq (ts : Fin 2 → ℝ) (hts : ts ∈ T) :
      (Q.JB 0 (ts 0) (ts 1) : ℂ) = ∫ β, ∫ lam, C β lam*e2 lam (ts 0) (ts 1) := by
    have hlim0 := hlim ∅ (Finset.empty_subset _) (ts 0) (hT ts hts 0)
      (ts 1) (hT ts hts 1) (0 : Cancel.Addr → ℝ)
    simp only [Finset.sdiff_empty,Finset.card_empty,pow_zero,one_mul] at hlim0
    rw [ite_eq_left ⟨hd,by simp only [IsSpecialSet,Finset.notMem_empty,false_implies,implies_true]⟩] at hlim0
    have hfun : (fun α => G ∅ α (ts 0) (ts 1)) =
        (fun α => ∫ lam, C (α ∘ f) lam*e2 lam (ts 0) (ts 1)) := by
      funext α
      exact hrep α (ts 0) (ts 1) (hT ts hts 0) (hT ts hts 1)
    rw [hfun] at hlim0
    exact hlim0.symm.trans (mint_comp_eq_integral (chosenSet Q.links) f hf hr'
      (fun β => ∫ lam, C β lam*e2 lam (ts 0) (ts 1)) 0)
  have heqfun : (fun ts : T => fun _ : (Set.univ : Set Unit) =>
      (Q.JB 0 ((ts : Fin 2 → ℝ) 0) ((ts : Fin 2 → ℝ) 1) : ℂ)) =
      (fun ts : T => fun _ : (Set.univ : Set Unit) =>
        ∫ β, ∫ lam, C β lam*e2 lam ((ts : Fin 2 → ℝ) 0) ((ts : Fin 2 → ℝ) 1)) := by
    funext ts _
    exact heq ts.val ts.property
  rw [heqfun]
  exact mixedRestrictionNorm00_integrated_coefficient_le hC (by linarith) (by linarith)
    hN (A1_nonneg.trans hA) hmain hT

/-- The time-factor conclusion with the final geometric quantifiers.
Its single constant depends only on eta, before every order cutoff. -/
theorem exists_couple_JB_time_bound {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : RegCpl), Q.wf = true → Q.dominant = true →
      ∀ n : ℕ, Q.size = 2*n → ∀ T : Set (Fin 2 → ℝ),
      (∀ t ∈ T, ∀ i, t i ∈ Icc (0:ℝ) 1) →
      XNorm00Restr (V := Unit) (1-η) T Set.univ
        (fun ts _ => (Q.JB 0 (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (C*C^n) := by
  let B := C0 (1-η/8) (η/4) (1-η/2)
  let H : ℝ≥0∞ := ENNReal.ofReal (2^(1-η))*Fourier.timeFourierNorm (1-η) unitSquareCutoff*
    ∑' k : ℕ, ENNReal.ofReal (A1^k*((2*k).factorial:ℝ)/(4*k).factorial)
  have hB : 1 ≤ B := one_le_C0 _ _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hH : H < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (timeFourierNorm_unitSquareCutoff_lt_top _))
    (summable_gevrey_ratio A1 A1_nonneg).tsum_ofReal_lt_top
  let C := max 1 (H.toReal*B+B^4)
  have hC : 1 ≤ C := le_max_left _ _
  have hfront : H.toReal*B ≤ C :=
    (le_add_of_nonneg_right (pow_nonneg hB0 4)).trans (le_max_right _ _)
  have hbase : B^4 ≤ C :=
    (le_add_of_nonneg_left (mul_nonneg ENNReal.toReal_nonneg hB0)).trans (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro Q hwf hd n hsize T hT
  rw [NormBridgeScratch.XNorm00Restr_eq_mixedRestrictionNorm00]
  apply (mixedRestrictionNorm00_couple_JB_le hη hη1 le_rfl Q hwf hd hT).trans
  have hexp : 2*Q.size+1 = 4*n+1 := by omega
  change ENNReal.ofReal (2^(1-η))*Fourier.timeFourierNorm (1-η) unitSquareCutoff*
    (ENNReal.ofReal (B^(2*Q.size+1))*
      ∑' k : ℕ, ENNReal.ofReal (A1^k*((2*k).factorial:ℝ)/(4*k).factorial)) ≤ _
  have he : ENNReal.ofReal (2^(1-η))*Fourier.timeFourierNorm (1-η) unitSquareCutoff*
      (ENNReal.ofReal (B^(2*Q.size+1))*
        ∑' k : ℕ, ENNReal.ofReal (A1^k*((2*k).factorial:ℝ)/(4*k).factorial)) =
      H*ENNReal.ofReal (B^(4*n+1)) := by rw [hexp]; dsimp only [H]; ac_rfl
  rw [he,← ENNReal.ofReal_toReal hH.ne,← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = (H.toReal*B)*(B^4)^n := by rw [pow_add,pow_mul,pow_one]; ring
    _ ≤ C*C^n := mul_le_mul hfront (pow_le_pow_left₀ (pow_nonneg hB0 4) hbase n)
      (by positivity) (zero_le_one.trans hC)

end WaveTurbulence.RegAsymp
