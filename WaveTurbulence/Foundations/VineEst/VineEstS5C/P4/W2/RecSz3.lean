/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module


public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxLeaf3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSz2
public import Mathlib
public import WaveTurbulence.Foundations.VineEst.HFree.Main
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecBotMom
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStepBot
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Win
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecVanish
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcStep
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcWinGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcGeo
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.DomEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrcOf


/-! # P4-W2 (session 18, step 4c-3): the size algebra

`sz_idx_alg`: the four size products `szQ szT`, `szQ CRt`, `CRq szT`, `CRq CRt` of a good bundle member are bounded by `KZ · N` resp. `KZ · L^{-w} · N`, `N` the native row-bound product,
`KZ = 4 TR² trC²/cb²`.  `native_size_start`: the sizes of the native couple and tree of the start-state member add to `2 zpN`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence.LGSpine WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P4.W13 TTree Finset
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
  MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS5A WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.ZpSurj WaveTurbulence.VineEstS5C.P4.W13
open scoped ENNReal

variable {w : ℕ} {P : WTParams} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ} {p : ℕ} {kind : Bool}
variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

theorem native_size_start (i : (assemblySourceFamily B).CoreIndex) :
    (RD.couple (pairOfLeaf G hG ((startState B RD hG layer hLayer).family.placement i).retained)).size +
      (RD.tree ((startState B RD hG layer hLayer).family.placement i).lower).size =
      2 * zpN (startState B RD hG layer hLayer) i :=
  (Nat.add_comm _ _).trans (ZpSurj.two_zpN (startState B RD hG layer hLayer) (pstar := i)).symm

theorem sz_idx_alg (TR trc C1 d cb Lw cC cT : ℝ) (n m N : ℕ) (hN : n + m = N) (hTR : 1 ≤ TR) (htrc : 1 ≤ trc)
    (hC1 : 1 ≤ C1) (hd : 0 < d) (hcb : 0 < cb) (hLw0 : 0 ≤ Lw) (hLw1 : Lw ≤ 1) (hcC : 0 ≤ cC) (hcT : 0 ≤ cT) :
    let x := C1 ^ 2 * d
    let SQ := 2 * TR * C1 ^ 2 * x ^ n * cC
    let ST := 2 * TR * C1 ^ 2 * x ^ m * cT
    let RQ := 2 * trc * C1 * (C1 * d) ^ n * Lw * cC
    let RT := 2 * trc * C1 * (C1 * d) ^ m * Lw * cT
    let NN := cb ^ 2 * C1 ^ 4 * (2 * x) ^ N * (cC * cT)
    let KZ := 4 * TR ^ 2 * trc ^ 2 / cb ^ 2
    SQ * ST ≤ KZ * NN ∧ SQ * RT ≤ KZ * (Lw * NN) ∧ RQ * ST ≤ KZ * (Lw * NN) ∧ RQ * RT ≤ KZ * (Lw * NN) := by
  intro x SQ ST RQ RT NN KZ
  have hC0 : 0 < C1 := by linarith
  have hx0 : 0 < x := by positivity
  have hTR0 : 0 < TR := by linarith
  have htrc0 : 0 < trc := by linarith
  have hcd : ∀ k : ℕ, (C1 * d) ^ k ≤ x ^ k := fun k => by
    apply pow_le_pow_left₀ (by positivity)
    show C1 * d ≤ C1 ^ 2 * d
    nlinarith [mul_pos hC0 hd]
  have hxN : x ^ N ≤ (2 * x) ^ N := pow_le_pow_left₀ hx0.le (by linarith) N
  have hxsplit : x ^ N = x ^ n * x ^ m := by rw [← hN, pow_add]
  have h2N : (2 * x) ^ N = 2 ^ N * x ^ N := mul_pow _ _ _
  have hcb2 : cb ^ 2 ≠ 0 := by positivity
  have hKZNN : KZ * NN = 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * (2 * x) ^ N * (cC * cT) := by
    simp only [KZ, NN]; field_simp
  have hxnm : x ^ n * x ^ m = x ^ N := hxsplit.symm
  have hA : 0 ≤ (2 * x) ^ N * (cC * cT) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- SQ ST
    have e : SQ * ST = 4 * TR ^ 2 * C1 ^ 4 * x ^ N * (cC * cT) := by
      simp only [SQ, ST]; rw [← hxnm]; ring
    rw [e, hKZNN]
    have h1 : x ^ N * (cC * cT) ≤ (2 * x) ^ N * (cC * cT) := mul_le_mul_of_nonneg_right hxN (by positivity)
    have h3 : 1 ≤ trc ^ 2 := one_le_pow₀ htrc
    calc 4 * TR ^ 2 * C1 ^ 4 * x ^ N * (cC * cT) = 4 * TR ^ 2 * C1 ^ 4 * (x ^ N * (cC * cT)) := by ring
      _ ≤ 4 * TR ^ 2 * C1 ^ 4 * ((2 * x) ^ N * (cC * cT)) := by gcongr
      _ ≤ 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * ((2 * x) ^ N * (cC * cT)) := by
          have : 0 ≤ 4 * TR ^ 2 * C1 ^ 4 * ((2 * x) ^ N * (cC * cT)) := by positivity
          nlinarith
      _ = 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * (2 * x) ^ N * (cC * cT) := by ring
  · -- SQ RT
    have e : SQ * RT = 4 * TR * trc * C1 ^ 3 * (x ^ n * (C1 * d) ^ m) * Lw * (cC * cT) := by
      simp only [SQ, RT]; ring
    have h1 : x ^ n * (C1 * d) ^ m ≤ x ^ N := by
      rw [← hxnm]; exact mul_le_mul_of_nonneg_left (hcd m) (by positivity)
    have hZ : 0 ≤ Lw * ((2 * x) ^ N * (cC * cT)) := by positivity
    have hcoef : 4 * TR * trc * C1 ^ 3 ≤ 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 := by
      have : 1 ≤ TR * trc * C1 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hTR htrc) hC1
      have h3 : 0 ≤ 4 * TR * trc * C1 ^ 3 := by positivity
      nlinarith [mul_nonneg h3 (sub_nonneg.2 this)]
    calc SQ * RT = 4 * TR * trc * C1 ^ 3 * ((x ^ n * (C1 * d) ^ m) * (Lw * (cC * cT))) := by rw [e]; ring
      _ ≤ 4 * TR * trc * C1 ^ 3 * (x ^ N * (Lw * (cC * cT))) := by
          gcongr
      _ ≤ 4 * TR * trc * C1 ^ 3 * ((2 * x) ^ N * (Lw * (cC * cT))) := by
          gcongr
      _ ≤ 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * ((2 * x) ^ N * (Lw * (cC * cT))) := by
          have : 0 ≤ (2 * x) ^ N * (Lw * (cC * cT)) := by positivity
          exact mul_le_mul_of_nonneg_right hcoef this
      _ = KZ * (Lw * NN) := by
          have := hKZNN
          calc _ = Lw * (4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * (2 * x) ^ N * (cC * cT)) := by ring
            _ = _ := by rw [← this]; ring
  · -- RQ ST
    have e : RQ * ST = 4 * TR * trc * C1 ^ 3 * ((C1 * d) ^ n * x ^ m) * Lw * (cC * cT) := by
      simp only [RQ, ST]; ring
    have h1 : (C1 * d) ^ n * x ^ m ≤ x ^ N := by
      rw [← hxnm]; exact mul_le_mul_of_nonneg_right (hcd n) (by positivity)
    have hcoef : 4 * TR * trc * C1 ^ 3 ≤ 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 := by
      have : 1 ≤ TR * trc * C1 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hTR htrc) hC1
      have h3 : 0 ≤ 4 * TR * trc * C1 ^ 3 := by positivity
      nlinarith [mul_nonneg h3 (sub_nonneg.2 this)]
    calc RQ * ST = 4 * TR * trc * C1 ^ 3 * (((C1 * d) ^ n * x ^ m) * (Lw * (cC * cT))) := by rw [e]; ring
      _ ≤ 4 * TR * trc * C1 ^ 3 * (x ^ N * (Lw * (cC * cT))) := by
          gcongr
      _ ≤ 4 * TR * trc * C1 ^ 3 * ((2 * x) ^ N * (Lw * (cC * cT))) := by
          gcongr
      _ ≤ 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * ((2 * x) ^ N * (Lw * (cC * cT))) := by
          have : 0 ≤ (2 * x) ^ N * (Lw * (cC * cT)) := by positivity
          exact mul_le_mul_of_nonneg_right hcoef this
      _ = KZ * (Lw * NN) := by
          have := hKZNN
          calc _ = Lw * (4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * (2 * x) ^ N * (cC * cT)) := by ring
            _ = _ := by rw [← this]; ring
  · -- RQ RT
    have e : RQ * RT = 4 * trc ^ 2 * C1 ^ 2 * ((C1 * d) ^ n * (C1 * d) ^ m) * (Lw * Lw) * (cC * cT) := by
      simp only [RQ, RT]; ring
    have h1 : (C1 * d) ^ n * (C1 * d) ^ m ≤ x ^ N := by
      rw [← hxnm]; exact mul_le_mul (hcd n) (hcd m) (by positivity) (by positivity)
    have hLL : Lw * Lw ≤ Lw := by nlinarith
    have hcoef : 4 * trc ^ 2 * C1 ^ 2 ≤ 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 := by
      have hC2 : C1 ^ 2 ≤ C1 ^ 4 := pow_le_pow_right₀ hC1 (by norm_num)
      have hT2 : 1 ≤ TR ^ 2 := one_le_pow₀ hTR
      have : 0 ≤ 4 * trc ^ 2 := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.2 hC2), mul_nonneg (mul_nonneg this (pow_nonneg hC0.le 4)) (sub_nonneg.2 hT2)]
    calc RQ * RT = 4 * trc ^ 2 * C1 ^ 2 * (((C1 * d) ^ n * (C1 * d) ^ m) * ((Lw * Lw) * (cC * cT))) := by rw [e]; ring
      _ ≤ 4 * trc ^ 2 * C1 ^ 2 * (x ^ N * (Lw * (cC * cT))) := by
          gcongr
      _ ≤ 4 * trc ^ 2 * C1 ^ 2 * ((2 * x) ^ N * (Lw * (cC * cT))) := by
          gcongr
      _ ≤ 4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * ((2 * x) ^ N * (Lw * (cC * cT))) := by
          have : 0 ≤ (2 * x) ^ N * (Lw * (cC * cT)) := by positivity
          exact mul_le_mul_of_nonneg_right hcoef this
      _ = KZ * (Lw * NN) := by
          have := hKZNN
          calc _ = Lw * (4 * TR ^ 2 * trc ^ 2 * C1 ^ 4 * (2 * x) ^ N * (cC * cT)) := by ring
            _ = _ := by rw [← this]; ring

end WaveTurbulence.VineEstS5C.P4.W2
