/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEngLit
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.TermNum1
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRowsBnd
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W13.WPF
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecCert
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.TermNum1
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRowsBnd` (sha256 e209b5f107be5388…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 19, step 1): `hrows_rec`, the product of the row sizes of a term with records

`recM1_le`: `M₁(recEng) ≤ M₁(native) + #{kd = 3}`; `recM1_ge`: `M₁(native) ≤ M₁(recEng)`.
`hrows_rec`: `∏ Rb ≤ Kr^{2M} (2C₁²δ)^{Sn} L^{-(γ₁-√η) M₁(recEng)} (Kb^{bb} lf)` from `prod_Rb_le`, `prod_rowBoundH_le` and the per-record bound
`bnd r ≤ Kc (N(vp) N(vb)) Loss r` with `Loss r = L^{-(γ₁-√η)}` iff `kd r = 3`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P2 WaveTurbulence.GammaLow.Famb.VineEstS5C.P3 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS4
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem recM1_geΓ {d : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (recs : List (ExcRec G d))
    (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (centre : Fin 4 → Mom d) (wBar : Mom d) (lam : ℝ) :
    (sourceSumintDatumΓ hM9 B hG (recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam)).M₁ ≤
      (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).M₁ := by
  unfold SumintPar.SumintDatum.M₁
  refine Finset.sum_le_sum fun v _ => Nat.add_le_add ?_ le_rfl
  show rowCoupleGΓ hM9 B RD hG layer hLayer v ≤ recGΓ B hM9 hG recs kd (rowCoupleGΓ hM9 B RD hG layer hLayer) v
  unfold recGΓ
  split_ifs <;> omega

open Classical in
theorem recM1_leΓ {d : ℕ} (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (recs : List (ExcRec G d))
    (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (centre : Fin 4 → Mom d) (wBar : Mom d) (lam : ℝ)
    (vpf : ExcRec G d → (assemblyShapeΓ hM9 B).VIdx)
    (hvp : ∀ r ∈ recs, (assemblyPairOfΓ hM9 B hG (vpf r)).1 = r.p0) :
    (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).M₁ ≤
      (sourceSumintDatumΓ hM9 B hG (recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam)).M₁ +
        (recs.toFinset.filter fun r => kd r = 3).card := by
  classical
  unfold SumintPar.SumintDatum.M₁
  have key : ∀ v : (assemblyShapeΓ hM9 B).VIdx,
      recGΓ B hM9 hG recs kd (rowCoupleGΓ hM9 B RD hG layer hLayer) v + rowTreeGΓ hM9 B RD hG layer hLayer v ≤
        (rowCoupleGΓ hM9 B RD hG layer hLayer v + rowTreeGΓ hM9 B RD hG layer hLayer v) +
          (if v ∈ ((recs.toFinset.filter fun r => kd r = 3).image vpf) then 1 else 0) := by
    intro v
    unfold recGΓ
    by_cases h : ∃ r ∈ recs, kd r = 3 ∧ (assemblyPairOfΓ hM9 B hG v).1 = r.p0
    · obtain ⟨r, hr, hk, hpr⟩ := h
      have hv : v ∈ ((recs.toFinset.filter fun r => kd r = 3).image vpf) := by
        refine Finset.mem_image.2 ⟨r, Finset.mem_filter.2 ⟨List.mem_toFinset.2 hr, hk⟩, ?_⟩
        have h1 : assemblyPairOfΓ hM9 B hG (vpf r) = assemblyPairOfΓ hM9 B hG v := Subtype.ext ((hvp r hr).trans hpr.symm)
        have h2 := congrArg (assemblyPairBijΓ hG B hM9) h1
        rwa [assemblyPairBij_assemblyPairOfΓ, assemblyPairBij_assemblyPairOfΓ] at h2
      rw [if_pos ⟨r, hr, hk, hpr⟩, if_pos hv]; omega
    · rw [if_neg h]; split_ifs <;> omega
  calc ∑ v, (recGΓ B hM9 hG recs kd (rowCoupleGΓ hM9 B RD hG layer hLayer) v + rowTreeGΓ hM9 B RD hG layer hLayer v)
      ≤ ∑ v, ((rowCoupleGΓ hM9 B RD hG layer hLayer v + rowTreeGΓ hM9 B RD hG layer hLayer v) +
          (if v ∈ ((recs.toFinset.filter fun r => kd r = 3).image vpf) then 1 else 0)) := Finset.sum_le_sum fun v _ => key v
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_boole]
      simp only [Nat.cast_id]
      refine Nat.add_le_add le_rfl ?_
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.card_image_le

open Classical in
/-- **`hrows` of `engine_literal` for a term with records.**  `hb`: each record row pair carries `bnd r ≤ Kc · (N N) · Loss r` with `N ρ = C · 2 rowBoundH ρ` and
`Loss r = L^{-(γ₁-√η)}` iff `kd r = 3`; the number of records is at most `bb`. -/
theorem hrows_recΓ {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ} (hB : ProfileBound P h Bh p)
    (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (recs : List (ExcRec G P.d)) (kd : ExcRec G P.d → ℕ) (zc : ExcRec G P.d → Prop)
    (addr : ExcRec G P.d → Finset ((assemblyShapeΓ hM9 B).TVar × (assemblyShapeΓ hM9 B).TVar))
    (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
    (hL : 1 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (cf : ℝ) (hcf : C.toReal ≤ cf)
    (vpf vbf : ExcRec G P.d → (assemblyShapeΓ hM9 B).VIdx)
    (hvp : ∀ r ∈ recs, (assemblyPairOfΓ hM9 B hG (vpf r)).1 = r.p0)
    (hinj1 : ∀ r ∈ recs, ∀ r' ∈ recs, vpf r = vpf r' → r = r') (hinj2 : ∀ r ∈ recs, ∀ r' ∈ recs, vbf r = vbf r' → r = r')
    (bnd : ExcRec G P.d → ℝ≥0∞) (Rb : Row (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) → ℝ≥0∞)
    (hn : ∀ ρ, (∀ r ∈ recs, ρ ≠ Sum.inl (vpf r) ∧ ρ ≠ Sum.inr (vbf r)) →
      Rb ρ = C * ENNReal.ofReal (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh (recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam) ρ))
    (h1 : ∀ r ∈ recs, Rb (Sum.inl (vpf r)) = bnd r) (h2 : ∀ r ∈ recs, Rb (Sum.inr (vbf r)) = 1)
    (Kc : ℝ) (hKc : 0 ≤ Kc)
    (hb : ∀ r ∈ recs, bnd r ≤ ENNReal.ofReal Kc *
      ((C * ENNReal.ofReal (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh (recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam) (Sum.inl (vpf r)))) *
       (C * ENNReal.ofReal (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh (recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam) (Sum.inr (vbf r))))) *
      (if kd r = 3 then ENNReal.ofReal (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) else 1))
    (Kr Kb : ℝ) (hKr : cf * 2 * (rowCb P * P.C₁ ^ 2) ≤ Kr) (hKcb : Kc ≤ Kb) (hKb1 : 1 ≤ Kb) (hX : 0 ≤ cf * 2 * (rowCb P * P.C₁ ^ 2))
    {bb : ℕ} (hbb : recs.toFinset.card ≤ bb) :
    ∏ ρ, Rb ρ ≤ ENNReal.ofReal (Kr ^ (2 * clLocalOrder1 R) *
      (2 * P.C₁ ^ 2 * P.δ) ^ ((∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowCoupleΓ hM9 B RD hG v).size / 2) +
          ∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowTreeΓ hM9 B RD v).size / 2) *
      P.L ^ (-(weightExp P.d P.γ P.η) * ((recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).M₁ : ℝ)) *
      (Kb ^ bb * regionLeafSize RD hG R layer hLayer Bh)) := by
  classical
  set W := recWΓ hM9 B RD hG layer hLayer recs kd zc centre wBar lam with hW
  set N : Row (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) → ℝ≥0∞ :=
    fun ρ => C * ENNReal.ofReal (2 * rowBoundHΓ hM9 B RD hG layer hLayer P Bh W ρ) with hN
  set S := recs.toFinset with hS
  set Loss : ExcRec G P.d → ℝ≥0∞ := fun r => if kd r = 3 then ENNReal.ofReal (P.L ^ (-(P.gamma1 - Real.sqrt P.η))) else 1 with hLoss
  have hinjS1 : Set.InjOn (fun r => (Sum.inl (vpf r) : Row (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam))) ↑S := by
    intro r hr r' hr' he
    exact hinj1 r (List.mem_toFinset.1 hr) r' (List.mem_toFinset.1 hr') (Sum.inl_injective he)
  have hinjS2 : Set.InjOn (fun r => (Sum.inr (vbf r) : Row (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam))) ↑S := by
    intro r hr r' hr' he
    exact hinj2 r (List.mem_toFinset.1 hr) r' (List.mem_toFinset.1 hr') (Sum.inr_injective he)
  have key := prod_Rb_le N Rb S (fun r => Sum.inl (vpf r)) (fun r => Sum.inr (vbf r)) hinjS1 hinjS2
    (fun k _ k' _ => Sum.inl_ne_inr) bnd Loss (ENNReal.ofReal Kc)
    (fun ρ hρ => hn ρ (fun r hr => by
      refine ⟨fun he => hρ (Finset.mem_union_left _ (Finset.mem_image.2 ⟨r, List.mem_toFinset.2 hr, he.symm⟩)),
        fun he => hρ (Finset.mem_union_right _ (Finset.mem_image.2 ⟨r, List.mem_toFinset.2 hr, he.symm⟩))⟩))
    (fun k hk => h1 k (List.mem_toFinset.1 hk)) (fun k hk => h2 k (List.mem_toFinset.1 hk))
    (fun k hk => hb k (List.mem_toFinset.1 hk))
  have hnat := prod_rowBoundH_leΓ (R := R) hB hM9 B RD hG layer hLayer hlay W rfl rfl (by linarith) hC1 hδ hC cf hcf
  have hLoss' : ∏ k ∈ S, Loss k = ENNReal.ofReal ((P.L ^ (-(P.gamma1 - Real.sqrt P.η))) ^ (S.filter fun r => kd r = 3).card) := by
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const,
      ENNReal.ofReal_pow (Real.rpow_nonneg (by linarith) _)]
  have hM1 := recM1_leΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam vpf hvp
  refine key.trans ?_
  rw [hLoss', ← ENNReal.ofReal_pow hKc]
  refine le_trans (mul_le_mul' (mul_le_mul' le_rfl hnat) le_rfl) ?_
  have hlf : 0 ≤ regionLeafSize RD hG R layer hLayer Bh := regionLeafSize_nonnegΓ hB hM9 B RD hG layer hLayer hlay W
  have hC10 : 0 ≤ P.C₁ := by linarith
  have hT : 0 ≤ (2 * P.C₁ ^ 2 * P.δ) ^ ((∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowCoupleΓ hM9 B RD hG v).size / 2) +
          ∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowTreeΓ hM9 B RD v).size / 2) := by positivity
  have hLw : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η)) := Real.rpow_nonneg (by linarith) _
  have hX0 : 0 ≤ (cf * 2 * (rowCb P * P.C₁ ^ 2)) ^ (2 * clLocalOrder1 R) := pow_nonneg hX _
  have hLR : 0 ≤ P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (((sourceSumintDatumΓ hM9 B hG W).M₁ : ℕ) : ℝ)) := Real.rpow_nonneg (by linarith) _
  rw [← ENNReal.ofReal_mul (pow_nonneg hKc _), ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hKc _)
    (mul_nonneg (mul_nonneg (mul_nonneg hX0 hT) hLR) hlf))]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hrows_real (Kc := Kc) (Kb := Kb) (Kr := Kr) (X := cf * 2 * (rowCb P * P.C₁ ^ 2)) (T := (2 * P.C₁ ^ 2 * P.δ) ^ ((∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowCoupleΓ hM9 B RD hG v).size / 2) +
          ∑ v : (assemblyShapeΓ hM9 B).VIdx, (rowTreeΓ hM9 B RD v).size / 2)) (L := P.L) (wt := P.gamma1 - Real.sqrt P.η)
    (lf := regionLeafSize RD hG R layer hLayer Bh) (card := S.card) (bb := bb) (m := clLocalOrder1 R) (k := (S.filter fun r => kd r = 3).card)
    (m1n := (sourceSumintDatumΓ hM9 B hG W).M₁) (m1r := (recEngΓ hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).M₁)
    hKc hKcb hKb1 hbb hX hKr hT hL hw hM1 hlf
  exact this

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
