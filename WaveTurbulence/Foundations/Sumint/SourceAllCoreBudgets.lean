/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CoreBudgetComparison
public import WaveTurbulence.Foundations.Sumint.SourceCoreNormalPairPower
public import WaveTurbulence.Foundations.Sumint.SourceSpecialCorePower
public import WaveTurbulence.Foundations.Sumint.SourceCoreBareLinearPower
public import WaveTurbulence.Foundations.Sumint.TouchedCoreProductBound

/-!
# A common actual full-mass budget for every source core

The constant is chosen before delta and the number of time steps. Every
core bound comes from the proved original source estimates, including
the ordered first bad core and the F23 case-(d) branch. Discrepancy gains
are discarded only at this positive-endpoint budget.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- TARGET sumint Step 3: every actual full source core mass has the same explicit input-arity budget. -/
theorem exists_source_all_core_budgets (d : ℕ) (hd : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Ioo (0:ℝ) 1) (η : ℝ) (hη : 0 < η) (hηbase : η ≤ gammaBase γ)
    (hηsmall : η ≤ 1/24) (hγη : γ+η ≤ 1) (τstar : ℝ) (hτstar : 0 < τstar)
    (β : ℝ) (hβ : 0 < β) (hβγ : β/2 < 2*γ)
    (hβη : β/2 < 2*((d:ℝ)-1)*(1-γ)-η) (hβnormal : β < 20*γ)
    (hhigh : 1/2 < γ → β/20 < min (2*γ-1) (1-γ)) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ (δ : ℝ) (N : ℕ), δ ∈ Ioc (0:ℝ) (1/16) → τstar = (N:ℝ)*δ →
      ∃ R : ℝ, 2 ≤ R ∧ ∀ L ≥ R,
      ∀ (D : SumintDatum d) (A : ℝ), D.Admissible A L γ η N →
      ∀ (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d),
      1/L ≤ ‖r‖ → ‖r‖ ≤ L^(-γ+η) → ∀ (t c : ℝ) (b : FactorIdx D.S),
      (∫⁻ z, sourceCoreNormFactor D L γ δ η p ν r t c (L^(-β)) b z) ≤
        ENNReal.ofReal (sourceCorePowerBudget D G L γ δ b) := by
  have hηγ : η ≤ γ := hηbase.trans (min_le_left _ _)
  have hηthird : η ≤ 1/3 := by linarith only [hηsmall]
  obtain ⟨CN,hCN,hN⟩ := exists_source_normal_core_power_bound d hd γ hγ τstar hτstar β hβ hβnormal hhigh
  obtain ⟨CP,hCP,hP⟩ := exists_source_pair_core_power_bound d hd γ hγ η hη hηthird τstar hτstar β hβ hβγ hβη
  let G := max CN CP
  have hG : 1 ≤ G := hCN.trans (le_max_left _ _)
  have hCGN : CN ≤ G^4 := (le_max_left _ _).trans (by
    calc
      G = G^1 := (pow_one G).symm
      _ ≤ G^4 := pow_le_pow_right₀ hG (by decide))
  have hCGP : CP ≤ G^2 := (le_max_right _ _).trans (by
    calc
      G = G^1 := (pow_one G).symm
      _ ≤ G^2 := pow_le_pow_right₀ hG (by decide))
  refine ⟨G,hG,?_⟩
  intro δ N hδ hτ
  have hδone : δ ∈ Ioc (0:ℝ) 1 := ⟨hδ.1,by linarith only [hδ.2]⟩
  obtain ⟨RN,hRN,hN⟩ := hN δ hδ.1 hδ.2
  obtain ⟨RP,hRP,hP⟩ := hP δ N hδone hτ
  obtain ⟨RS,hRS,hS⟩ := exists_source_special_core_power_bound d hd γ hγ η hη hηbase hηsmall hγη
    τstar hτstar β hβ hβγ hβη δ N hδ hτ
  obtain ⟨RB,hRB,hB⟩ := exists_source_bare_linear_core_power_bound d hγ δ hδ.1 hδ.2
  refine ⟨max (max RN RP) (max RS RB),hRN.trans ((le_max_left _ _).trans (le_max_left _ _)),?_⟩
  intro L hL D A hD p ν r hr hrupper t c b
  have hLN : RN ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLP : RP ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLS : RS ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLB : RB ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := by linarith only [hRN,hLN]
  have hLp : 0 < L := zero_lt_one.trans_le hL1
  have hh : L^(-β) ∈ Icc (0:ℝ) 1 := ⟨Real.rpow_nonneg hLp.le _,
    Real.rpow_le_one_of_one_le_of_nonpos hL1 (neg_nonpos.mpr hβ.le)⟩
  have hgap (e : Prop) [Decidable e] : 0 ≤ (if e then β/20 else 0) := by split_ifs <;> linarith only [hβ]
  rcases b with i | (a | i)
  · by_cases hn : D.S.nor i = true
    · have hmass := hN L hLN D N hτ A η hD hγη p ν r hr hrupper t c ⟨i,hn⟩
      have hcost : sourceCoreBadCost D γ (.inl i) = 0 := by simp [sourceCoreBadCost,badBlockCost,hn]
      have hnum := coefficient_power_le_sourceCorePowerBudget D hL1 hδ.1 (zero_le_one.trans hCN)
        (.inl i) 4 (sourceCoreArity_normal D ⟨i,hn⟩) hCGN
        (show 4*((d:ℝ)-γ)-(if normalIncoherent D ⟨i,hn⟩ then β/20 else 0) ≤
          (4:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ (.inl i) by rw [hcost]; linarith only [hgap (normalIncoherent D ⟨i,hn⟩)])
      norm_num only [Nat.cast_ofNat,neg_div,show -(4:ℝ)/2 = -2 by norm_num] at hnum
      exact hmass.trans (ENNReal.ofReal_le_ofReal hnum)
    · have hn' : D.S.nor i = false := Bool.eq_false_iff.mpr hn
      by_cases hk : D.badKind i = 0 ∨ D.badKind i = 2
      · have hm : 0 < D.S.m i := by
          rcases hk with h0 | h2
          · exact ((hD.2.2.2.2.2.2.2.2.2 i hn').1 h0).choose
          · exact (hD.2.2.2.2.2.2.2.2.2 i hn').2.1 h2
        let a : Σ i : Fin D.S.I, Fin (D.S.m i) := ⟨i,⟨0,hm⟩⟩
        have ha : caseAPair D a ∨ caseCPair D a := by
          rcases hk with h0 | h2
          · exact Or.inl ⟨hn',h0,rfl⟩
          · exact Or.inr ⟨hn',h2,rfl⟩
        have hnot3 : D.badKind i ≠ 3 := by rcases hk with h0 | h2 <;> omega
        have hcost : sourceCoreBadCost D γ (.inl i) = -gammaBase γ/4 := by
          simp only [sourceCoreBadCost,badBlockCost,hn',ite_true,ite_eq_right hnot3]
        have hnum := power_le_sourceCorePowerBudget D hG hL1 hδone (.inl i)
          (show 3*((d:ℝ)-γ)-gammaBase γ/4-(if pairIncoherent D a then β/20 else 0) ≤
            (sourceCoreArity D (.inl i):ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ (.inl i) by
              rw [sourceCoreArity_special D a ha,hcost]
              push_cast
              linarith only [hgap (pairIncoherent D a)])
        exact (hS L hLS D A hD p ν r hr hrupper t c a ha).trans (ENNReal.ofReal_le_ofReal hnum)
      · have hk' : D.badKind i = 1 ∨ D.badKind i = 3 := by omega
        have harity := sourceCoreArity_bare_linear D i hn' (no_special_pair_of_kind_b_or_d D i hk')
        have hcost : sourceCoreBadCost D γ (.inl i) =
            (if D.badKind i = 3 then 3*gammaBase γ/2 else -gammaBase γ/4) := by
          simp only [sourceCoreBadCost,badBlockCost,hn',ite_true]
        have hnum := power_le_sourceCorePowerBudget D hG hL1 hδone (.inl i)
          (show (d:ℝ)-γ+(if D.badKind i = 3 then 3*gammaBase γ/2 else -gammaBase γ/2) ≤
            (sourceCoreArity D (.inl i):ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ (.inl i) by
              rw [harity,hcost]
              norm_num only [Nat.cast_one,one_mul]
              split_ifs <;> linarith only [gammaBase_pos hγ])
        exact (hB L hLB D η hγη p ν r hr hrupper t c (L^(-β)) i hh hn' hk').trans (ENNReal.ofReal_le_ofReal hnum)
  · by_cases ha : caseAPair D a ∨ caseCPair D a
    · have hnotfixed : sourceCoreGroup D (.inr (.inl a)) ≠ .inr (.inl a) := by
        change (if caseAPair D a ∨ caseCPair D a then Sum.inl a.1 else Sum.inr (Sum.inl a)) ≠ Sum.inr (Sum.inl a)
        rw [ite_eq_left ha]
        exact Sum.inl_ne_inr
      have harity := sourceCoreArity_eq_zero_of_not_fixed D _ hnotfixed
      have hηp : 0 ≤ 1-3*η := by linarith only [hηthird]
      have hrone : ‖r‖ ≤ 1 := hrupper.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1
        (by linarith only [hηγ]))
      have hb := lintegral_sourceCore_fixed_count_pow_le D hD hLp hηp δ p ν r hrone t c hh.2
        (.inr (.inl a)) ∅ (fun _ => 0)
      simp only [harity,pow_zero] at hb
      have hvol : (Measure.pi fun j => fixedCoordinateMeasure (∅:Set D.S.TVar) (fun _ => 0)
          (sourceCoreCoordinateTimeEquiv D ⟨.inr (.inl a),j⟩)) = volume := by simp only [fixedCoordinateMeasure,Set.mem_empty_iff_false,ite_false]; rfl
      rw [hvol] at hb
      simpa only [sourceCorePowerBudget,harity,pow_zero,Nat.cast_zero,neg_zero,zero_div,Real.rpow_zero,
        sourceCoreBadCost,zero_mul,add_zero,mul_one,ENNReal.ofReal_one] using hb
    · have hmass := hP L hLP D A hD p ν r t c a ha
      have hnum := coefficient_power_le_sourceCorePowerBudget D hL1 hδ.1 (zero_le_one.trans hCP)
        (.inr (.inl a)) 2 (sourceCoreArity_pair D a ha) hCGP
        (show 2*((d:ℝ)-γ)-(if pairIncoherent D a then β/2 else 0) ≤
          (2:ℝ)*((d:ℝ)-γ)+sourceCoreBadCost D γ (.inr (.inl a)) by
            change _ ≤ 2*((d:ℝ)-γ)+0
            have hg : 0 ≤ (if pairIncoherent D a then β/2 else 0) := by split_ifs <;> linarith only [hβ]
            linarith only [hg])
      norm_num only [Nat.cast_ofNat,show -(2:ℝ)/2 = -1 by norm_num,Real.rpow_neg_one] at hnum
      exact hmass.trans (ENNReal.ofReal_le_ofReal hnum)
  · have harity := sourceCoreArity_eq_zero_of_not_fixed D (.inr (.inr i)) (by
      change Sum.inl i.1 ≠ Sum.inr (Sum.inr i)
      exact Sum.inl_ne_inr)
    have hηp : 0 ≤ 1-3*η := by linarith only [hηthird]
    have hrone : ‖r‖ ≤ 1 := hrupper.trans (Real.rpow_le_one_of_one_le_of_nonpos hL1
      (by linarith only [hηγ]))
    have hb := lintegral_sourceCore_fixed_count_pow_le D hD hLp hηp δ p ν r hrone t c hh.2
      (.inr (.inr i)) ∅ (fun _ => 0)
    simp only [harity,pow_zero] at hb
    have hvol : (Measure.pi fun j => fixedCoordinateMeasure (∅:Set D.S.TVar) (fun _ => 0)
        (sourceCoreCoordinateTimeEquiv D ⟨.inr (.inr i),j⟩)) = volume := by simp only [fixedCoordinateMeasure,Set.mem_empty_iff_false,ite_false]; rfl
    rw [hvol] at hb
    simpa only [sourceCorePowerBudget,harity,pow_zero,Nat.cast_zero,neg_zero,zero_div,Real.rpow_zero,
      sourceCoreBadCost,zero_mul,add_zero,mul_one,ENNReal.ofReal_one] using hb

end WaveTurbulence.Sumint
