/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS3.Step3Facts

/-! # Step 3: the engine bound in the literal form `(C√δ)^{n₍₂₎} L^{-η⁸n₍₃₎ - η²b + η⁷}` -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS3
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3.Eng WaveTurbulence.PL2330 VineParamContract TTree Reg Reg.Skeleton RegRed
open scoped ENNReal
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem ccη_lt_top (η : ℝ) : ccη η < ⊤ := by
  unfold ccη
  exact Fourier.cutoffMultiplierConstant_lt_top _ (FS.cutQ_hasCompactSupport _) (FS.cutQ_contDiff _)

theorem one_le_ccη_toReal (η : ℝ) : 1 ≤ (ccη η + 1).toReal := by
  have h : ccη η + 1 ≠ ⊤ := ENNReal.add_ne_top.2 ⟨(ccη_lt_top η).ne, ENNReal.one_ne_top⟩
  rw [← ENNReal.toReal_one]
  exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top h).2 le_add_self

/-- The explicit constants entering the final `C*`. -/
noncomputable def finalC0 (η : ℝ) : ℝ := (2 : ℝ) ^ (2 * η ^ 8) * Real.sqrt 2 ^ (η ^ 6)
noncomputable def finalC1 (η : ℝ) : ℝ := (2 : ℝ) ^ (2 * η ^ 8 + η ^ 6) * 4 ^ (η ^ 6)

theorem engineConst_eq (η : ℝ) (K : ℕ) : engineConst η K = finalC0 η * finalC1 η ^ K := rfl

theorem one_le_finalC0 {η : ℝ} (h0 : 0 ≤ η) : 1 ≤ finalC0 η := by
  unfold finalC0
  have h1 : (1 : ℝ) ≤ 2 ^ (2 * η ^ 8) := Real.one_le_rpow (by norm_num) (by positivity)
  have h2 : (1 : ℝ) ≤ Real.sqrt 2 ^ (η ^ 6) := Real.one_le_rpow
    (by rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)) (by positivity)
  nlinarith

theorem one_le_finalC1 {η : ℝ} (h0 : 0 ≤ η) : 1 ≤ finalC1 η := by
  unfold finalC1
  have h1 : (1 : ℝ) ≤ 2 ^ (2 * η ^ 8 + η ^ 6) := Real.one_le_rpow (by norm_num) (by positivity)
  have h2 : (1 : ℝ) ≤ 4 ^ (η ^ 6) := Real.one_le_rpow (by norm_num) (by positivity)
  nlinarith

theorem ennreal_reduce {ι : Type*} [Fintype ι] {Cfs E1 : ℝ≥0∞} (hCfs : Cfs ≠ ⊤) (cf : ℝ) (hcf : Cfs.toReal ≤ cf)
    (cc : ℝ) (hE1 : E1 = ENNReal.ofReal cc) (hcc : 0 ≤ cc) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) {cp Q : ℝ}
    (hcp : 0 ≤ cp) (hQ : 0 ≤ Q) :
    ENNReal.ofReal cp * (E1 * ENNReal.ofReal Q * ∏ i, (Cfs * ENNReal.ofReal (x i))) ≤
      ENNReal.ofReal (cp * (cc * Q * ∏ i, (cf * x i))) := by
  have hcf0 : 0 ≤ cf := (ENNReal.toReal_nonneg).trans hcf
  have hC : Cfs ≤ ENNReal.ofReal cf := by
    rw [← ENNReal.ofReal_toReal hCfs]; exact ENNReal.ofReal_le_ofReal hcf
  have h1 : ∏ i, (Cfs * ENNReal.ofReal (x i)) ≤ ∏ i, (ENNReal.ofReal cf * ENNReal.ofReal (x i)) :=
    Finset.prod_le_prod' fun i _ => mul_le_mul_left hC _
  have h2 : ∏ i, (ENNReal.ofReal cf * ENNReal.ofReal (x i)) = ENNReal.ofReal (∏ i, (cf * x i)) := by
    rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg hcf0 (hx i))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ENNReal.ofReal_mul hcf0]
  have hprod : 0 ≤ ∏ i, (cf * x i) := Finset.prod_nonneg fun i _ => mul_nonneg hcf0 (hx i)
  calc ENNReal.ofReal cp * (E1 * ENNReal.ofReal Q * ∏ i, (Cfs * ENNReal.ofReal (x i)))
      ≤ ENNReal.ofReal cp * (E1 * ENNReal.ofReal Q * ENNReal.ofReal (∏ i, (cf * x i))) := by
        rw [← h2]; gcongr
    _ = ENNReal.ofReal (cp * (cc * Q * ∏ i, (cf * x i))) := by
        rw [hE1, ← ENNReal.ofReal_mul hcc, ← ENNReal.ofReal_mul (mul_nonneg hcc hQ),
          ← ENNReal.ofReal_mul hcp]

theorem prod_side {ι : Type*} [Fintype ι] (cf k q L e : ℝ) (hL : 0 < L) (n g : ι → ℕ) :
    ∏ i, (cf * (2 * (k * q ^ (n i) * L ^ (e * (g i : ℝ))))) =
      (cf * 2 * k) ^ Fintype.card ι * q ^ (∑ i, n i) * L ^ (e * ((∑ i, g i : ℕ) : ℝ)) := by
  have h1 : ∀ i, cf * (2 * (k * q ^ (n i) * L ^ (e * (g i : ℝ)))) = (cf * 2 * k) * q ^ (n i) * L ^ (e * (g i : ℝ)) :=
    fun i => by ring
  simp_rw [h1]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Finset.prod_pow_eq_pow_sum, ← Real.rpow_sum_of_pos hL, ← Finset.mul_sum]
  congr 3
  push_cast; rfl

section Parts
variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (P : WTParams)
  (W : SumintWeightClockData (assemblyShape hM9 B) P.d)

/-- The product of the row bounds. -/
theorem prod_rowBound_eq (hL : 0 < P.L) (hg : W.g = rowCoupleG hM9 B RD hG layer hLayer)
    (hg' : W.g' = rowTreeG hM9 B RD hG layer hLayer) (cf : ℝ) :
    ∏ ρ : Row (sourceSumintDatum hM9 B hG W), (cf * (2 * rowBound hM9 B RD hG layer hLayer P W ρ)) =
      (cf * 2 * (rowCb P * P.C₁ ^ 2)) ^ (2 * clLocalOrder1 R) *
        (2 * P.C₁ ^ 2 * P.δ) ^ ((∑ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size / 2) +
          ∑ v : (assemblyShape hM9 B).VIdx, (rowTree hM9 B RD v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * ((sourceSumintDatum hM9 B hG W).M₁ : ℝ)) := by
  unfold Row
  rw [Fintype.prod_sum_type]
  have hc := prod_side cf (rowCb P * P.C₁ ^ 2) (2 * P.C₁ ^ 2 * P.δ) P.L (-(P.gamma1 - Real.sqrt P.η)) hL
    (fun v : (assemblyShape hM9 B).VIdx => (rowCouple hM9 B RD hG v).size / 2)
    (rowCoupleG hM9 B RD hG layer hLayer)
  have ht := prod_side cf (rowCb P * P.C₁ ^ 2) (2 * P.C₁ ^ 2 * P.δ) P.L (-(P.gamma1 - Real.sqrt P.η)) hL
    (fun v : (assemblyShape hM9 B).VIdx => (rowTree hM9 B RD v).size / 2)
    (rowTreeG hM9 B RD hG layer hLayer)
  have e1 : ∀ v, cf * (2 * rowBound hM9 B RD hG layer hLayer P W (Sum.inl v)) =
      cf * (2 * ((rowCb P * P.C₁ ^ 2) * (2 * P.C₁ ^ 2 * P.δ) ^ ((rowCouple hM9 B RD hG v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (rowCoupleG hM9 B RD hG layer hLayer v : ℝ)))) := fun v => rfl
  have e2 : ∀ v, cf * (2 * rowBound hM9 B RD hG layer hLayer P W (Sum.inr v)) =
      cf * (2 * ((rowCb P * P.C₁ ^ 2) * (2 * P.C₁ ^ 2 * P.δ) ^ ((rowTree hM9 B RD v).size / 2) *
        P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (rowTreeG hM9 B RD hG layer hLayer v : ℝ)))) := fun v => rfl
  simp_rw [e1, e2]
  beta_reduce at hc ht
  refine (congrArg₂ (· * ·) hc ht).trans ?_
  have hcard : Fintype.card (assemblyShape hM9 B).VIdx = clLocalOrder1 R := by
    rw [Sumint.card_vector_index, assemblyShape_M]
  rw [hcard, show 2 * clLocalOrder1 R = clLocalOrder1 R + clLocalOrder1 R by ring]
  have hM1 : ((sourceSumintDatum hM9 B hG W).M₁ : ℝ) =
      ((∑ v : (assemblyShape hM9 B).VIdx, rowCoupleG hM9 B RD hG layer hLayer v : ℕ) : ℝ) +
        ((∑ v : (assemblyShape hM9 B).VIdx, rowTreeG hM9 B RD hG layer hLayer v : ℕ) : ℝ) := by
    unfold SumintDatum.M₁
    rw [← Nat.cast_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun v _ => ?_
    show W.g v + W.g' v = _
    rw [hg, hg']
  rw [hM1, mul_add, Real.rpow_add hL]
  simp only [pow_add]
  ring

end Parts

theorem weightExp_eq (P : WTParams) : weightExp P.d P.γ P.η = P.gamma1 - Real.sqrt P.η := rfl

theorem Q_eq (P : WTParams) (D : SumintDatum P.d) (hI : 0 < D.S.I) (hpar : ∀ v, D.param v = 0)
    (hL : 0 < P.L) (hδ : 0 < P.δ) {m : ℕ} (hDM : D.S.M = m) {u : ℕ} (hU : u = m + 1) :
    (3 : ℝ) ^ u * (engineConst P.η (2 * D.S.M) * maxPar D ^ (P.η ^ 6) * sumintRHS0 P D *
        ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) =
      3 ^ (D.S.M + 1) * (finalC0 P.η * finalC1 P.η ^ (2 * D.S.M) *
        (P.C₁ * (P.C₁ * (Real.sqrt P.δ)⁻¹) ^ D.S.M * ((P.L ^ ((P.d : ℝ) - P.γ)) ^ D.S.M *
          P.L ^ (-(P.η ^ 2 * (((Finset.univ.filter fun i => D.S.nor i = false).card : ℕ) + (D.M₁ : ℝ))) -
            P.η ^ 8 * (D.M₀ : ℝ) + P.η ^ 7))) *
        P.L ^ ((P.gamma1 - Real.sqrt P.η) * (D.M₁ : ℝ))) := by
  rw [engineConst_eq, maxPar_one D hI hpar, Real.one_rpow, mul_one, prod_rpow_rowG D hL, weightExp_eq, hU, ← hDM]
  unfold sumintRHS0
  have hexp : (D.S.M : ℝ) * ((P.d : ℝ) - P.γ) - P.η ^ 2 * (((Finset.univ.filter fun i => D.S.nor i = false).card : ℕ) +
      (D.M₁ : ℝ)) - P.η ^ 8 * (D.M₀ : ℝ) + P.η ^ 7 =
      ((P.d : ℝ) - P.γ) * (D.S.M : ℝ) + (-(P.η ^ 2 * (((Finset.univ.filter fun i => D.S.nor i = false).card : ℕ) +
        (D.M₁ : ℝ))) - P.η ^ 8 * (D.M₀ : ℝ) + P.η ^ 7) := by ring
  rw [hexp, Real.rpow_add hL, Real.rpow_mul hL.le, Real.rpow_natCast]
  have hsq : P.δ ^ (-(1 : ℝ) / 2) = (Real.sqrt P.δ)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hδ.le]; congr 1; ring
  rw [hsq]

theorem order2_eq' (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain) :
    clLocalOrder2 RD hG R = clLocalOrder1 R + 2 * ((∑ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size / 2) +
      ∑ v : (assemblyShape hM9 B).VIdx, (rowTree hM9 B RD v).size / 2) := by
  rw [order2_eq hM9 B RD hG, mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 2
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact (Nat.two_mul_div_two_of_even (code_size_even _)).symm
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact (Nat.two_mul_div_two_of_even (chain_size_even _)).symm

/-- **The engine bound in the literal form.** -/
theorem step3Bound_le (P : WTParams) {Cfs : ℝ≥0∞} (hCfs : Cfs ≠ ⊤) (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (RD : ReconstructionData G) (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ)
    (hLayer : IsLayering (RD.garden hG) layer) (badKind : Fin (assemblyShape hM9 B).I → Fin 4)
    (qOut : Fin 3 → ℕ) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (hη0 : 0 < P.η) (hη1 : P.η ≤ 1) (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) :
    step3Bound P Cfs hM9 B RD hG layer hLayer badKind qOut centre wBar ≤
      ENNReal.ofReal ((numCstar (ccη P.η + 1).toReal (finalC0 P.η) (finalC1 P.η) (max Cfs.toReal 1) (rowCb P) P.C₁ *
          Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
        P.L ^ (-(P.η ^ 8 * (((step3D hM9 B RD hG layer hLayer badKind qOut centre wBar).M₀ +
          (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar).M₁ : ℕ) : ℝ)) -
          P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7)) := by
  classical
  set W := step3W hM9 B RD hG layer hLayer badKind qOut centre wBar with hW
  set D := sourceSumintDatum hM9 B hG W with hD
  have hI := assemblyShape_I_pos hM9 B
  have hL0 : 0 < P.L := by linarith
  have hM1 := M_pos hM9 B
  have hDM : D.S.M = clLocalOrder1 R := assemblyShape_M hM9 B
  have hpar : ∀ v, D.param v = 0 := fun _ => rfl
  have hU := card_U_eq B
  have hC0 : 0 ≤ P.C₁ := by linarith
  have hcc1 := one_le_ccη_toReal P.η
  have hE1 : ccη P.η + 1 = ENNReal.ofReal (ccη P.η + 1).toReal :=
    (ENNReal.ofReal_toReal (ENNReal.add_ne_top.2 ⟨(ccη_lt_top P.η).ne, ENNReal.one_ne_top⟩)).symm
  have hcf1 : 1 ≤ max Cfs.toReal 1 := le_max_right _ _
  have hx : ∀ ρ, 0 ≤ 2 * rowBound hM9 B RD hG layer hLayer P W ρ := by
    intro ρ
    rcases ρ with v | v
    · have := rowB_pos (P := P) hC hδ hL0 ((rowCouple hM9 B RD hG v).size / 2) (rowCoupleG hM9 B RD hG layer hLayer v)
      exact mul_nonneg (by norm_num) this.le
    · have := rowB_pos (P := P) hC hδ hL0 ((rowTree hM9 B RD v).size / 2) (rowTreeG hM9 B RD hG layer hLayer v)
      exact mul_nonneg (by norm_num) this.le
  have hcpl : 0 < coupling P.d P.L P.γ P.δ := by unfold coupling; positivity
  have hQ0 : 0 ≤ (3 : ℝ) ^ Fintype.card ↥U * (engineConst P.η (Fintype.card (Row D)) * maxPar D ^ (P.η ^ 6) *
        sumintRHS0 P D * ∏ ρ, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ))) := by
    unfold sumintRHS0
    have := engineConst_nonneg P.η (Fintype.card (Row D))
    have h2 : 0 ≤ maxPar D ^ (P.η ^ 6) := by
      rw [maxPar_one D hI hpar]; simp
    have h3 : ∀ ρ : Row D, 0 ≤ P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) := fun ρ => Real.rpow_nonneg hL0.le _
    have h4 : 0 ≤ ∏ ρ : Row D, P.L ^ (weightExp P.d P.γ P.η * (rowG D ρ : ℝ)) := Finset.prod_nonneg fun ρ _ => h3 ρ
    have h5 : 0 ≤ P.C₁ * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M * P.L ^ ((D.S.M : ℝ) * ((P.d : ℝ) - P.γ) -
        P.η ^ 2 * (((Finset.univ.filter fun i => D.S.nor i = false).card : ℕ) + (D.M₁ : ℝ)) -
        P.η ^ 8 * (D.M₀ : ℝ) + P.η ^ 7) := by
      have := Real.rpow_nonneg hδ.le (-(1 : ℝ) / 2)
      positivity
    positivity
  unfold step3Bound
  dsimp only
  refine (ennreal_reduce hCfs (max Cfs.toReal 1) (le_max_left _ _) _ hE1 (by linarith) _ hx
    (pow_nonneg hcpl.le _) hQ0).trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [card_Row_eq D, Q_eq P D hI hpar hL0 hδ hDM hU,
    prod_rowBound_eq hM9 B RD hG layer hLayer P W hL0 rfl rfl (max Cfs.toReal 1), order2_eq' hM9 B RD hG]
  set M := clLocalOrder1 R with hMd
  set Sn := (∑ v : (assemblyShape hM9 B).VIdx, (rowCouple hM9 B RD hG v).size / 2) +
      ∑ v : (assemblyShape hM9 B).VIdx, (rowTree hM9 B RD v).size / 2 with hSn
  set cc := (ccη P.η + 1).toReal with hcc
  set cf := max Cfs.toReal 1 with hcf
  have hs : 0 < Real.sqrt P.δ := Real.sqrt_pos.2 hδ
  have hu : 0 < P.L ^ ((P.d : ℝ) - P.γ) := Real.rpow_pos_of_pos hL0 _
  have hcb : 1 ≤ rowCb P := by
    unfold rowCb; have := cLeib_nonneg P.d (30 * P.d); linarith
  set e1 := -(P.η ^ 2 * (((Finset.univ.filter fun i => D.S.nor i = false).card : ℕ) + (D.M₁ : ℝ))) -
            P.η ^ 8 * (D.M₀ : ℝ) + P.η ^ 7 with he1
  have hcore := numeric_core M Sn hM1 (c := P.C₁) (s := Real.sqrt P.δ) (u := P.L ^ ((P.d : ℝ) - P.γ))
    (Le := P.L ^ e1) (cc := cc) (c0 := finalC0 P.η) (c1 := finalC1 P.η) (cf := cf) (cb := rowCb P) hC hs hu
    (Real.rpow_nonneg hL0.le _) hcc1 (one_le_finalC0 hη0.le) (one_le_finalC1 hη0.le) hcf1 hcb
  rw [Real.sq_sqrt hδ.le] at hcore
  have ht : P.L ^ ((P.gamma1 - Real.sqrt P.η) * (D.M₁ : ℝ)) *
      (P.L ^ ((P.gamma1 - Real.sqrt P.η) * (D.M₁ : ℝ)))⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.rpow_pos_of_pos hL0 _).ne'
  have hneg : P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (D.M₁ : ℝ)) =
      (P.L ^ ((P.gamma1 - Real.sqrt P.η) * (D.M₁ : ℝ)))⁻¹ := by
    rw [neg_mul, Real.rpow_neg hL0.le]
  have hcp : coupling P.d P.L P.γ P.δ = P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ)) := rfl
  rw [hcp, hneg]
  have hLe : P.L ^ e1 ≤ P.L ^ (-(P.η ^ 8 * (((D.M₀ + D.M₁ : ℕ)) : ℝ)) -
      P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) := by
    apply Real.rpow_le_rpow_of_exponent_le hL
    rw [he1]
    push_cast
    have h8 : P.η ^ 8 ≤ P.η ^ 2 := pow_le_pow_of_le_one hη0.le hη1 (by norm_num)
    have hM1' : (0 : ℝ) ≤ (D.M₁ : ℝ) := Nat.cast_nonneg _
    have hbb : ((Finset.univ.filter fun i => D.S.nor i = false).card : ℝ) =
        ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) := rfl
    rw [hbb]
    nlinarith
  refine le_trans (le_of_eq ?_) (hcore.trans (mul_le_mul_of_nonneg_left hLe (pow_nonneg (mul_nonneg (numCstar_nonneg (by linarith) (by linarith [one_le_finalC0 hη0.le]) hC0) hs.le) _)))
  calc _ = ((P.δ / (2 * P.L ^ ((P.d : ℝ) - P.γ))) ^ M * (cc * (3 ^ (M + 1) *
      (finalC0 P.η * finalC1 P.η ^ (2 * M) * (P.C₁ * (P.C₁ * (Real.sqrt P.δ)⁻¹) ^ M *
        ((P.L ^ ((P.d : ℝ) - P.γ)) ^ M * P.L ^ e1))) * cf ^ (2 * M) *
      ((2 * rowCb P * P.C₁ ^ 2) ^ (2 * M) * (2 * P.C₁ ^ 2 * P.δ) ^ Sn)))) *
      (P.L ^ ((P.gamma1 - Real.sqrt P.η) * (D.M₁ : ℝ)) * (P.L ^ ((P.gamma1 - Real.sqrt P.η) * (D.M₁ : ℝ)))⁻¹) := by
        rw [hDM]; ring
    _ = _ := by rw [ht, mul_one]

end WaveTurbulence.VineEstS3
