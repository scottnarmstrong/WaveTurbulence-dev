/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz7
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRowsBnd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEngLit
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRegion
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Final.Iface
public import WaveTurbulence.Foundations.VineEst.HFree.Inst

/-! # P4-W2 (session 19, step 5): the uniform certificate of the terms with records (kinds `0`, `1`, `3`)

`NoKind2`: the staging hypothesis (no kind-2 summand in any bundle), to be replaced by the kind-2 packet.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open VineParamContract
open scoped ENNReal


variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

theorem rowBoundH_nonneg
    {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ} (hB : ProfileBound P h Bh p)
    (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 0 < P.L)
    (W : SumintWeightClockData (assemblyShape hM9 B) P.d) (ρ : (assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx) :
    0 ≤ rowBoundH hM9 B RD hG layer hLayer P Bh W ρ := by
  unfold rowBoundH
  refine mul_nonneg ?_ (rowCostH_nonneg (hLayer := hLayer) hB hlay W ρ)
  rcases ρ with v | v <;> exact (rowB_pos (P := P) hC1 hδ hL _ _).le

theorem recEng_param {d : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (recs : List (ExcRec G d))
    (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar))
    (centre : Fin 4 → Mom d) (wBar : Mom d) (lam : ℝ) (v : (assemblyShape hM9 B).TVar) :
    (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).param v =
      if v = (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩ : (assemblyShape hM9 B).TVar) then lam else 0 := rfl

theorem Jb_le_one_add (t : ℝ) : WaveTurbulence.VineEstS3.Eng.Jb t ≤ 1 + |t| := by
  unfold WaveTurbulence.VineEstS3.Eng.Jb
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [abs_nonneg t, sq_abs t]

/-- **`maxPar` of the engine datum of a term with records**: `maxPar^{η⁶} ≤ (1+|λ|)^{6η⁶}`. -/
theorem maxPar_rec_le {d : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (recs : List (ExcRec G d))
    (kd : ExcRec G d → ℕ) (zc : ExcRec G d → Prop)
    (addr : ExcRec G d → Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar))
    (centre : Fin 4 → Mom d) (wBar : Mom d) (lam η : ℝ) (hη : 0 < η) :
    maxPar (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) ^ (η ^ 6) ≤ (1 + |lam|) ^ (6 * η ^ 6) := by
  have hne : Nonempty (assemblyShape hM9 B).TVar := ⟨.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩⟩
  have hmp : maxPar (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) ≤ 1 + |lam| := by
    rw [maxPar_eq]
    haveI : Nonempty (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam).S.TVar := hne
    refine ciSup_le fun v => ?_
    refine (le_of_eq (congrArg WaveTurbulence.VineEstS3.Eng.Jb (recEng_param hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam v))).trans ?_
    split_ifs
    · exact Jb_le_one_add lam
    · have : WaveTurbulence.VineEstS3.Eng.Jb 0 = 1 := by simp [WaveTurbulence.VineEstS3.Eng.Jb]
      rw [this]; linarith [abs_nonneg lam]
  have hmp0 : 0 ≤ maxPar (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) := by
    rw [maxPar_eq]
    exact Real.iSup_nonneg fun v => (WaveTurbulence.VineEstS3.Eng.Jb_pos _).le
  have h1 : (1 : ℝ) ≤ 1 + |lam| := by linarith [abs_nonneg lam]
  calc maxPar (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) ^ (η ^ 6) ≤ (1 + |lam|) ^ (η ^ 6) :=
        Real.rpow_le_rpow hmp0 hmp (by positivity)
    _ ≤ (1 + |lam|) ^ (6 * η ^ 6) := Real.rpow_le_rpow_of_exponent_le h1 (by nlinarith [pow_pos hη 6])

theorem le_C_mul_two {C : ℝ≥0∞} (hC : 1 ≤ C) {x : ℝ} (hx : 0 ≤ x) : ENNReal.ofReal x ≤ C * ENNReal.ofReal (2 * x) := by
  calc ENNReal.ofReal x = 1 * ENNReal.ofReal x := (one_mul _).symm
    _ ≤ C * ENNReal.ofReal (2 * x) := by
        refine mul_le_mul' hC ?_
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- The per-record size bound in the form of `hrows_rec`. -/
theorem rec_bnd_le {K : ℝ≥0∞} (hK : K ≠ ⊤) {KZ x y Lw : ℝ} (hKZ : 0 ≤ KZ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hLw : 0 ≤ Lw)
    {C : ℝ≥0∞} (hC : 1 ≤ C) (k3 : Prop) [Decidable k3] :
    K * ENNReal.ofReal (KZ * (x * y) * (if k3 then Lw else 1)) ≤
      ENNReal.ofReal (K.toReal * KZ) * ((C * ENNReal.ofReal (2 * x)) * (C * ENNReal.ofReal (2 * y))) *
        (if k3 then ENNReal.ofReal Lw else 1) := by
  have hKe : ENNReal.ofReal (K.toReal * KZ) = K * ENNReal.ofReal KZ := by
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hK]
  rw [hKe]
  have hxy : ENNReal.ofReal (x * y) = ENNReal.ofReal x * ENNReal.ofReal y := ENNReal.ofReal_mul hx
  have h1 := le_C_mul_two hC hx
  have h2 := le_C_mul_two hC hy
  by_cases hk : k3
  · simp only [if_pos hk]
    rw [ENNReal.ofReal_mul (mul_nonneg hKZ (mul_nonneg hx hy)), ENNReal.ofReal_mul hKZ, hxy]
    calc K * (ENNReal.ofReal KZ * (ENNReal.ofReal x * ENNReal.ofReal y) * ENNReal.ofReal Lw)
        = K * ENNReal.ofReal KZ * (ENNReal.ofReal x * ENNReal.ofReal y) * ENNReal.ofReal Lw := by ring
      _ ≤ K * ENNReal.ofReal KZ * ((C * ENNReal.ofReal (2 * x)) * (C * ENNReal.ofReal (2 * y))) * ENNReal.ofReal Lw := by
          gcongr
  · simp only [if_neg hk]
    rw [mul_one, mul_one, ENNReal.ofReal_mul hKZ, hxy]
    calc K * (ENNReal.ofReal KZ * (ENNReal.ofReal x * ENNReal.ofReal y))
        = K * ENNReal.ofReal KZ * (ENNReal.ofReal x * ENNReal.ofReal y) := by ring
      _ ≤ K * ENNReal.ofReal KZ * ((C * ENNReal.ofReal (2 * x)) * (C * ENNReal.ofReal (2 * y))) := by gcongr

end WaveTurbulence.VineEstS5C.P4.W2
