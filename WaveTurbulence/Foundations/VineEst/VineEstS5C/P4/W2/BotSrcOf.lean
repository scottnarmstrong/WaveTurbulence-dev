/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemSrcOf
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotRemFar
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.BotExcWin


/-! # P4-W2 (session 9, bottom family): `botCertSrcOf` and the certified source `botSrcOf` of the bottom bundle (copy of `ExcSrcOf` and `RemSrcOf`) -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P4.Bot

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {Bh : ℕ → ℝ}

variable (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family) (hA : IsPrimeGarden A.skeleton)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

variable (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))

section CS
variable (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc hup hA E hN in
/-- **The certified terms of a level as a `CertSrc`** (windows `L₄` = `false`, `Lₕ` = `true`). -/
noncomputable def botCertSrcOf :
    CertSrc P (botSepFamOf (κ := κ) A c0 hA hcan hel htc hcc hup E hN).S (zpQ2 A pstar : ℝ) (zpQ4 A pstar : ℝ) (zpQh A pstar : ℝ) where
  good b := b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0
  BQ s := cond s (winCh A pstar) (winCl A pstar)
  qQ s := cond s (cornH A pstar) (cornL A pstar)
  BT s := cond s (winTh A pstar) (winTl A pstar)
  qT s := cond s (cornH A pstar) (cornL A pstar)
  cc b := (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c
  cT b := (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).c
  CJq b := (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ
  CMq b := (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM
  CJt b := (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ
  CMt b := (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CM
  cq s b i := match s with
    | false => botCertC_loCT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b i
    | true => botCertC_hiCT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b i
  ct s b j := match s with
    | false => botCertT_loCT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b j
    | true => botCertT_hiCT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b j
  cq_c s b i := by
    cases s
    · exact (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_c i
    · exact (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_c i
  ct_c s b j := by
    cases s
    · exact (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).lo_c j
    · exact (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).hi_c j
  win_q b hb i := ⟨botCertC_loCT_win (κ := κ) A c0 hA hcan hel htc hcc hup E hN hb i,
    botCertC_hiCT_win (κ := κ) A c0 hA hcan hel htc hcc hup E hN hb i⟩
  win_t b hb j := ⟨botCertT_loCT_win (κ := κ) A c0 hA hcan hel htc hcc hup E hN hb j,
    botCertT_hiCT_win (κ := κ) A c0 hA hcan hel htc hcc hup E hN hb j⟩


end CS

include hcan hel htc hcc hup hA in
/-- **The gate level of the carrier-side couple of a good index and the window cases.** -/
theorem botGateSel_cpl {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    ∃ qg : ℕ, (qg = zpQ4 A pstar ∨ qg = zpQh A pstar) ∧
      IsCoherentCoupleAt p qg (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar) ∧
      ∀ W : ℕ, (W = zpQ4 A pstar ∨ W = zpQh A pstar) → (W = qg ∨ qg + 1 ≤ W ∨ (W + 1 ≤ qg ∧ W < botLq pstar b)) := by
  have hG := mem_canon_of_botbs A c0 hb
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar
  · refine ⟨zpQ4 A pstar, Or.inl rfl, botg_coh_lowC A c0 hA hcan hel htc hcc hup hb hr, ?_⟩
    rintro W (rfl | rfl)
    · exact Or.inl rfl
    · omega
  · have hhi := botg_high_C A c0 hA hcan hel htc hcc hup b hG (not_le.1 hr)
    have hle := (botg_cplRoot_le_nat A c0 hA hcan hel htc hcc hup b hG).2
    refine ⟨(zpQQ b.1 pstar).1, Or.inr hhi, botg_nat_cohC A c0 hA hcan hel htc hcc hup b hG, ?_⟩
    have hlq : botLq pstar b = cplRootLayer (zpObjC b.1 pstar) := rfl
    rintro W (rfl | rfl)
    · right; right; refine ⟨by omega, by omega⟩
    · exact Or.inl hhi.symm

include hcan hel htc hcc hup hA in
/-- **The gate level of the carrier-side tree of a good index and the window cases.** -/
theorem botGateSel_tree {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) :
    ∃ qg : ℕ, (qg = zpQ4 A pstar ∨ qg = zpQh A pstar) ∧
      IsCoherentTreeAt p qg (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar) ∧
      ∀ W : ℕ, (W = zpQ4 A pstar ∨ W = zpQh A pstar) → (W = qg ∨ qg + 1 ≤ W ∨ (W + 1 ≤ qg ∧ W < botLt pstar b)) := by
  have hG := mem_canon_of_botbs A c0 hb
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar
  · refine ⟨zpQ4 A pstar, Or.inl rfl, botg_coh_lowT A c0 hA hcan hel htc hcc hup hb hr, ?_⟩
    rintro W (rfl | rfl)
    · exact Or.inl rfl
    · omega
  · have hhi := botg_high_T A c0 hA hcan hel htc hcc hup b hG (not_le.1 hr)
    have hle := (botg_treeRoot_le_nat A c0 hA hcan hel htc hcc hup b hG).2
    refine ⟨(zpBranchQ b.1 pstar).1, Or.inr hhi, botg_nat_cohT A c0 hA hcan hel htc hcc hup b hG, ?_⟩
    have hlq : botLt pstar b = treeRootLayer (zpObjT b.1 pstar) := rfl
    rintro W (rfl | rfl)
    · right; right; refine ⟨by omega, by omega⟩
    · exact Or.inl hhi.symm


include hcan hel htc hcc hup hA in
/-- **`RemC` of the carrier-side couple of a good index on the window `s` (`false`: `L₄`, `true`: `Lₕ`).** -/
theorem botRemCplWin (R : RemEnv P κ) (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)
    {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) {CR : ℝ} (hCR0 : 0 < CR)
    (hCR : P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
      layerCost Bh (zpObjC b.1 pstar) < CR) (s : Bool) :
    ∃ Rc : RemC P (30 * P.d) (cond s (winCh A pstar) (winCl A pstar)) (cond s (cornH A pstar) (cornL A pstar))
        (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = cond s (pairBc (zpQh A pstar : ℝ) (zpQ2 A pstar)) (pairBc (zpQ4 A pstar : ℝ) (zpQ2 A pstar)) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, botRemQ pstar κ (botQfam pstar κ A) b (ts 0) (ts 1) k = Rc.f ts k := by
  obtain ⟨qg, hq, hcoh, hwc⟩ := botGateSel_cpl A c0 hA hcan hel htc hcc hup hb
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have hhp := zpQh_le_p A hcan hel htc hcc
  have hqq : zpQ2 A pstar ≤ qg := by rcases hq with rfl | rfl <;> omega
  have hqp : qg ≤ p := by rcases hq with rfl | rfl <;> omega
  have hn : (zpCodeC b.1 pstar).size / 2 ≤ P.N (p + 1) ^ 4 :=
    (botNC_le A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb)).trans hN
  cases s
  · show ∃ Rc : RemC P (30 * P.d) (winCl A pstar) (cornL A pstar) (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = pairBc (zpQ4 A pstar : ℝ) (zpQ2 A pstar) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, botRemQ pstar κ (botQfam pstar κ A) b (ts 0) (ts 1) k = Rc.f ts k
    obtain ⟨Rc, h1, h2⟩ := botRemC_cpl_at A b E R.hd R.hL1 R.hδ0 R.hθ6 R.hκL R.hκγ hqq hqp hcoh hn (size_half_cpl _) hCR0 hCR h24
      (hwc _ (Or.inl rfl))
    exact ⟨Rc, h1, fun ts hts => h2 ts (h1 ▸ hts)⟩
  · show ∃ Rc : RemC P (30 * P.d) (winCh A pstar) (cornH A pstar) (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = pairBc (zpQh A pstar : ℝ) (zpQ2 A pstar) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, botRemQ pstar κ (botQfam pstar κ A) b (ts 0) (ts 1) k = Rc.f ts k
    obtain ⟨Rc, h1, h2⟩ := botRemC_cpl_at A b E R.hd R.hL1 R.hδ0 R.hθ6 R.hκL R.hκγ hqq hqp hcoh hn (size_half_cpl _) hCR0 hCR (h24.trans h4h)
      (hwc _ (Or.inr rfl))
    exact ⟨Rc, h1, fun ts hts => h2 ts (h1 ▸ hts)⟩

include hcan hel htc hcc hup hA in
/-- **`RemC` of the carrier-side tree of a good index on the window `s`.** -/
theorem botRemTreeWin (R : RemEnv P κ) (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)
    {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) {CR : ℝ} (hCR0 : 0 < CR)
    (hCR : P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
      layerCost Bh (zpObjT b.1 pstar) < CR) (s : Bool) :
    ∃ Rc : RemC P 0 (cond s (winTh A pstar) (winTl A pstar)) (cond s (cornH A pstar) (cornL A pstar))
        (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = cond s (pairBcGt (zpQh A pstar : ℝ) (zpQ2 A pstar)) (pairBcGt (zpQ4 A pstar : ℝ) (zpQ2 A pstar)) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, botRemT pstar κ (botTfam pstar κ A) b (ts 0) (ts 1) k = Rc.f ts k := by
  obtain ⟨qg, hq, hcoh, hwc⟩ := botGateSel_tree A c0 hA hcan hel htc hcc hup hb
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have hhp := zpQh_le_p A hcan hel htc hcc
  have hqq : zpQ2 A pstar ≤ qg := by rcases hq with rfl | rfl <;> omega
  have hqp : qg ≤ p := by rcases hq with rfl | rfl <;> omega
  have hn : (zpCodeT b.1 pstar).size / 2 ≤ P.N (p + 1) ^ 4 :=
    (botNT_le A c0 hA hcan hel htc hcc hup b (mem_canon_of_botbs A c0 hb)).trans hN
  cases s
  · show ∃ Rc : RemC P 0 (winTl A pstar) (cornL A pstar) (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = pairBcGt (zpQ4 A pstar : ℝ) (zpQ2 A pstar) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, botRemT pstar κ (botTfam pstar κ A) b (ts 0) (ts 1) k = Rc.f ts k
    obtain ⟨Rc, h1, h2⟩ := botRemC_tree_at A b E R.hd R.hL1 R.hδ0 R.hθ6 R.hκL R.hκγ hqq hqp hcoh hn (size_half_chain _) hCR0 hCR h24
      (hwc _ (Or.inl rfl))
    exact ⟨Rc, h1, fun ts hts => h2 ts (h1 ▸ hts)⟩
  · show ∃ Rc : RemC P 0 (winTh A pstar) (cornH A pstar) (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = pairBcGt (zpQh A pstar : ℝ) (zpQ2 A pstar) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, botRemT pstar κ (botTfam pstar κ A) b (ts 0) (ts 1) k = Rc.f ts k
    obtain ⟨Rc, h1, h2⟩ := botRemC_tree_at A b E R.hd R.hL1 R.hδ0 R.hθ6 R.hκL R.hκγ hqq hqp hcoh hn (size_half_chain _) hCR0 hCR (h24.trans h4h)
      (hwc _ (Or.inr rfl))
    exact ⟨Rc, h1, fun ts hts => h2 ts (h1 ▸ hts)⟩


variable (R : RemEnv P κ) (CRq CRt : BT w ι → ℝ)

include hcan hel htc hcc hup hA in
open Classical in
/-- The couple remainder `RemC` of the index `b` on the window `s` (empty continuity set off `bsA ∪ bsB`). -/
noncomputable def botRqOf (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4) (hq0 : ∀ b, 0 < CRq b)
    (hgq : ∀ b, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjC b.1 pstar) < CRq b) (s : Bool) (b : BT w ι) :
    RemC P (30 * P.d) (cond s (winCh A pstar) (winCl A pstar)) (cond s (cornH A pstar) (cornL A pstar))
      (trC (6 * P.η ^ 6) * CRq b) :=
  if hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0 then
    Classical.choose (botRemCplWin A c0 hA hcan hel htc hcc hup R E hN hb (hq0 b) (hgq b hb) s)
  else Classical.choose (remC_empty (P := P) (Λ₂ := 30 * P.d) (B := cond s (winCh A pstar) (winCl A pstar))
      (q := cond s (cornH A pstar) (cornL A pstar))
      (by cases s <;> exact timeBox_subset_cell _ _)
      (by cases s <;> exact timeBox_subset_closure_interior _ _)
      (CR := trC (6 * P.η ^ 6) * CRq b)
      (by have := one_le_trC (θ := 6 * P.η ^ 6) (by have := R.hd; positivity); have := hq0 b; positivity))

include hcan hel htc hcc hup hA in
open Classical in
/-- The tree remainder `RemC` of the index `b` on the window `s`. -/
noncomputable def botRtOf (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4) (hq0 : ∀ b, 0 < CRt b)
    (hgt : ∀ b, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjT b.1 pstar) < CRt b) (s : Bool) (b : BT w ι) :
    RemC P 0 (cond s (winTh A pstar) (winTl A pstar)) (cond s (cornH A pstar) (cornL A pstar))
      (trC (6 * P.η ^ 6) * CRt b) :=
  if hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0 then
    Classical.choose (botRemTreeWin A c0 hA hcan hel htc hcc hup R E hN hb (hq0 b) (hgt b hb) s)
  else Classical.choose (remC_empty (P := P) (Λ₂ := 0) (B := cond s (winTh A pstar) (winTl A pstar))
      (q := cond s (cornH A pstar) (cornL A pstar))
      (by cases s <;> exact timeBoxGt_subset_cell _ _)
      (by cases s
          · exact timeBoxGt_subset_closure_interior (L2_le_L4R A hcan hel htc hcc)
          · exact timeBoxGt_subset_closure_interior (L2_le_LhR A hcan hel htc hcc))
      (CR := trC (6 * P.η ^ 6) * CRt b)
      (by have := one_le_trC (θ := 6 * P.η ^ 6) (by have := R.hd; positivity); have := hq0 b; positivity))

section SrcOf
variable (hq0 : ∀ b, 0 < CRq b) (ht0 : ∀ b, 0 < CRt b)
variable (hgq : ∀ b, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjC b.1 pstar) < CRq b)
variable (hgt : ∀ b, (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjT b.1 pstar) < CRt b)
variable (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc hup hA in
theorem botRqOf_good {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) (s : Bool) :
    (botRqOf A c0 hA hcan hel htc hcc hup R CRq E hN hq0 hgq s b).Bc =
        cond s (pairBc (zpQh A pstar : ℝ) (zpQ2 A pstar)) (pairBc (zpQ4 A pstar : ℝ) (zpQ2 A pstar)) ∧
      ∀ ts ∈ (botRqOf A c0 hA hcan hel htc hcc hup R CRq E hN hq0 hgq s b).Bc, ∀ k,
        botRemQ pstar κ (botQfam pstar κ A) b (ts 0) (ts 1) k = (botRqOf A c0 hA hcan hel htc hcc hup R CRq E hN hq0 hgq s b).f ts k := by
  unfold botRqOf
  rw [dif_pos hb]
  exact Classical.choose_spec (botRemCplWin A c0 hA hcan hel htc hcc hup R E hN hb (hq0 b) (hgq b hb) s)

include hcan hel htc hcc hup hA in
theorem botRqOf_bad {b : BT w ι} (hb : ¬ (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0)) (s : Bool) :
    (botRqOf A c0 hA hcan hel htc hcc hup R CRq E hN hq0 hgq s b).Bc = ∅ := by
  unfold botRqOf
  rw [dif_neg hb]
  exact Classical.choose_spec (remC_empty (P := P) (Λ₂ := 30 * P.d) (B := cond s (winCh A pstar) (winCl A pstar))
      (q := cond s (cornH A pstar) (cornL A pstar))
      (by cases s <;> exact timeBox_subset_cell _ _)
      (by cases s <;> exact timeBox_subset_closure_interior _ _)
      (CR := trC (6 * P.η ^ 6) * CRq b)
      (by have := one_le_trC (θ := 6 * P.η ^ 6) (by have := R.hd; positivity); have := hq0 b; positivity))

include hcan hel htc hcc hup hA in
theorem botRtOf_good {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) (s : Bool) :
    (botRtOf A c0 hA hcan hel htc hcc hup R CRt E hN ht0 hgt s b).Bc =
        cond s (pairBcGt (zpQh A pstar : ℝ) (zpQ2 A pstar)) (pairBcGt (zpQ4 A pstar : ℝ) (zpQ2 A pstar)) ∧
      ∀ ts ∈ (botRtOf A c0 hA hcan hel htc hcc hup R CRt E hN ht0 hgt s b).Bc, ∀ k,
        botRemT pstar κ (botTfam pstar κ A) b (ts 0) (ts 1) k = (botRtOf A c0 hA hcan hel htc hcc hup R CRt E hN ht0 hgt s b).f ts k := by
  unfold botRtOf
  rw [dif_pos hb]
  exact Classical.choose_spec (botRemTreeWin A c0 hA hcan hel htc hcc hup R E hN hb (ht0 b) (hgt b hb) s)

include hcan hel htc hcc hup hA in
theorem botRtOf_bad {b : BT w ι} (hb : ¬ (b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0)) (s : Bool) :
    (botRtOf A c0 hA hcan hel htc hcc hup R CRt E hN ht0 hgt s b).Bc = ∅ := by
  unfold botRtOf
  rw [dif_neg hb]
  exact Classical.choose_spec (remC_empty (P := P) (Λ₂ := 0) (B := cond s (winTh A pstar) (winTl A pstar))
      (q := cond s (cornH A pstar) (cornL A pstar))
      (by cases s <;> exact timeBoxGt_subset_cell _ _)
      (by cases s
          · exact timeBoxGt_subset_closure_interior (L2_le_L4R A hcan hel htc hcc)
          · exact timeBoxGt_subset_closure_interior (L2_le_LhR A hcan hel htc hcc))
      (CR := trC (6 * P.η ^ 6) * CRt b)
      (by have := one_le_trC (θ := 6 * P.η ^ 6) (by have := R.hd; positivity); have := ht0 b; positivity))

include hcan hel htc hcc hup hA E hN in
open Classical in
/-- **The certified source of a level** (`Src`): the certified terms of `botCertSrcOf` and, for every `s`, the `RemC`s of the remainders `remQ`, `remT` of the approximant families
`zpQfam`, `zpTfam`, with the constants `trC · CRq b`, `trC · CRt b` (`CRq`, `CRt` positive, and above the gate bounds on `bsA ∪ bsB`). -/
noncomputable def botSrcOf : Src P (botSepFamOf (κ := κ) A c0 hA hcan hel htc hcc hup E hN).S (botRemQ pstar κ (botQfam pstar κ A)) (botRemT pstar κ (botTfam pstar κ A))
    (zpQ2 A pstar : ℝ) (zpQ4 A pstar : ℝ) (zpQh A pstar : ℝ) where
  toCertSrc := botCertSrcOf (κ := κ) A c0 hA hcan hel htc hcc hup E hN
  CRq b := trC (6 * P.η ^ 6) * CRq b
  CRt b := trC (6 * P.η ^ 6) * CRt b
  rq := botRqOf A c0 hA hcan hel htc hcc hup R CRq E hN hq0 hgq
  rt := botRtOf A c0 hA hcan hel htc hcc hup R CRt E hN ht0 hgt
  hRQ s b x y hm k := by
    by_cases hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0
    · have := (botRqOf_good A c0 hA hcan hel htc hcc hup R CRq hq0 hgq E hN hb s).2 ![x, y] hm k
      simpa using this
    · rw [botRqOf_bad A c0 hA hcan hel htc hcc hup R CRq hq0 hgq E hN hb s] at hm
      exact absurd hm (Set.notMem_empty _)
  hRT s b x y hm k := by
    by_cases hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0
    · have := (botRtOf_good A c0 hA hcan hel htc hcc hup R CRt ht0 hgt E hN hb s).2 ![x, y] hm k
      simpa using this
    · rw [botRtOf_bad A c0 hA hcan hel htc hcc hup R CRt ht0 hgt E hN hb s] at hm
      exact absurd hm (Set.notMem_empty _)
  win_rq b hb := by
    refine ⟨fun t ht s hs _ => ⟨trivial, ?_⟩, fun t ht s hs _ => ⟨trivial, ?_⟩⟩
    · rw [(botRqOf_good A c0 hA hcan hel htc hcc hup R CRq hq0 hgq E hN hb false).1]
      exact ⟨by simpa using ht, by simpa using hs⟩
    · rw [(botRqOf_good A c0 hA hcan hel htc hcc hup R CRq hq0 hgq E hN hb true).1]
      exact ⟨by simpa using ht, by simpa using hs⟩
  win_rt b hb := by
    refine ⟨fun t ht s hs hg => ⟨trivial, ?_⟩, fun t ht s hs hg => ⟨trivial, ?_⟩⟩
    · rw [(botRtOf_good A c0 hA hcan hel htc hcc hup R CRt ht0 hgt E hN hb false).1]
      exact ⟨⟨by simpa using ht, by simpa using hs⟩, by simpa using hg rfl⟩
    · rw [(botRtOf_good A c0 hA hcan hel htc hcc hup R CRt ht0 hgt E hN hb true).1]
      exact ⟨⟨by simpa using ht, by simpa using hs⟩, by simpa using hg rfl⟩

end SrcOf

end WaveTurbulence.VineEstS5C.P4.W2
