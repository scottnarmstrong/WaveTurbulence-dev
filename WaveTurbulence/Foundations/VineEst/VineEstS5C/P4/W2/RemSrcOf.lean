/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RemFar5
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrc
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcSrcOf


/-! # P4-W2 (session 8, step 2): the certified source `Src` of a level (`sffOf`)

`gateSel_cpl`, `gateSel_tree`: for an index `b ∈ bsA ∪ bsB` the gate level `qg ∈ {L₄, Lₕ}` (`L₄` when the root layer is `≤ L₄`, else the native parent `Lₕ`) with the
coherence at `(qg, L₂)`, and for each window `W ∈ {L₄, Lₕ}` one of the three window cases of `remC_cpl_at` (`W = qg`, `qg + 1 ≤ W`, `W + 1 ≤ qg ∧ W < Lr`).
`remCplWin`, `remTreeWin`: the `RemC` of the remainder on the window `s`.  `rqOf`, `rtOf`: the choice for every index (empty continuity set off `bsA ∪ bsB`).
**`srcOf`**: `Src P (sepFamOf ..).S (remQ κ (zpQfam κ A)) (remT κ (zpTfam κ A)) L₂ L₄ Lₕ`, whose certified part is `certSrcOf` and whose remainders are the `rqOf`, `rtOf`
with constants `trC (6η⁶) · CRq b`, `trC (6η⁶) · CRt b` for any positive `CRq`, `CRt` above the gate bounds (`RemEnv`: the parameter facts `1 ≤ d`, `1 ≤ L`, `0 < δ`, `6η⁶ ≤ η`,
`κ.L = L`, `κ.γ = γ`, all fields of `AmbP`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS3

set_option linter.unusedSectionVars false

variable {w : ℕ} {ι : Type*} {p : ℕ} {kind : Bool} {pstar : ι} {J : Set ι} [Fintype ι] [DecidableEq ι]
variable {P : WTParams} {κ : KPar P.d} {Bh : ℕ → ℝ}

variable (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J) (hA : IsPrimeGarden A.skeleton)
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

include hcan hel htc hcc in
/-- **The gate level of the carrier-side couple of a good index and the window cases.** -/
theorem gateSel_cpl {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    ∃ qg : ℕ, (qg = zpQ4 A pstar ∨ qg = zpQh A pstar) ∧
      IsCoherentCoupleAt p qg (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar) ∧
      ∀ W : ℕ, (W = zpQ4 A pstar ∨ W = zpQh A pstar) → (W = qg ∨ qg + 1 ≤ W ∨ (W + 1 ≤ qg ∧ W < zpLq b)) := by
  have hG := mem_zpFinset_of_bs A sp0 hA hb
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar
  · refine ⟨zpQ4 A pstar, Or.inl rfl, zp_coh_lowC A sp0 hA hcan hel htc hcc hb hr, ?_⟩
    rintro W (rfl | rfl)
    · exact Or.inl rfl
    · omega
  · have hhi := zp_high_C A sp0 hA hcan hel htc hcc b hG (not_le.1 hr)
    have hle := (cplRoot_le_nat A sp0 hA hcan hel htc hcc b hG).2
    refine ⟨(zpQQ b.1 pstar).1, Or.inr hhi, nat_cohC A sp0 hA hcan hel htc hcc b hG, ?_⟩
    have hlq : zpLq b = cplRootLayer (zpObjC b.1 pstar) := rfl
    rintro W (rfl | rfl)
    · right; right; refine ⟨by omega, by omega⟩
    · exact Or.inl hhi.symm

include hcan hel htc hcc in
/-- **The gate level of the carrier-side tree of a good index and the window cases.** -/
theorem gateSel_tree {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) :
    ∃ qg : ℕ, (qg = zpQ4 A pstar ∨ qg = zpQh A pstar) ∧
      IsCoherentTreeAt p qg (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar) ∧
      ∀ W : ℕ, (W = zpQ4 A pstar ∨ W = zpQh A pstar) → (W = qg ∨ qg + 1 ≤ W ∨ (W + 1 ≤ qg ∧ W < zpLt b)) := by
  have hG := mem_zpFinset_of_bs A sp0 hA hb
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar
  · refine ⟨zpQ4 A pstar, Or.inl rfl, zp_coh_lowT A sp0 hA hcan hel htc hcc hb hr, ?_⟩
    rintro W (rfl | rfl)
    · exact Or.inl rfl
    · omega
  · have hhi := zp_high_T A sp0 hA hcan hel htc hcc b hG (not_le.1 hr)
    have hle := (treeRoot_le_nat A sp0 hA hcan hel htc hcc b hG).2
    refine ⟨(zpBranchQ b.1 pstar).1, Or.inr hhi, nat_cohT A sp0 hA hcan hel htc hcc b hG, ?_⟩
    have hlq : zpLt b = treeRootLayer (zpObjT b.1 pstar) := rfl
    rintro W (rfl | rfl)
    · right; right; refine ⟨by omega, by omega⟩
    · exact Or.inl hhi.symm


/-- The parameter facts needed to apply the gate data (all fields of `AmbP`). -/
structure RemEnv (P : WTParams) (κ : KPar P.d) : Prop where
  hd : 1 ≤ P.d
  hL1 : 1 ≤ P.L
  hδ0 : 0 < P.δ
  hθ6 : 6 * P.η ^ 6 ≤ P.η
  hκL : κ.L = P.L
  hκγ : κ.γ = P.γ

include hcan hel htc hcc in
/-- **`RemC` of the carrier-side couple of a good index on the window `s` (`false`: `L₄`, `true`: `Lₕ`).** -/
theorem remCplWin (R : RemEnv P κ) (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)
    {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) {CR : ℝ} (hCR0 : 0 < CR)
    (hCR : P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
      layerCost Bh (zpObjC b.1 pstar) < CR) (s : Bool) :
    ∃ Rc : RemC P (30 * P.d) (cond s (winCh A pstar) (winCl A pstar)) (cond s (cornH A pstar) (cornL A pstar))
        (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = cond s (pairBc (zpQh A pstar : ℝ) (zpQ2 A pstar)) (pairBc (zpQ4 A pstar : ℝ) (zpQ2 A pstar)) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, remQ κ (zpQfam κ A) b (ts 0) (ts 1) k = Rc.f ts k := by
  obtain ⟨qg, hq, hcoh, hwc⟩ := gateSel_cpl A sp0 hA hcan hel htc hcc hb
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have hhp := zpQh_le_p A hcan hel htc hcc
  have hqq : zpQ2 A pstar ≤ qg := by rcases hq with rfl | rfl <;> omega
  have hqp : qg ≤ p := by rcases hq with rfl | rfl <;> omega
  have hn : (zpCodeC b.1 pstar).size / 2 ≤ P.N (p + 1) ^ 4 :=
    (nC_le A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb)).trans hN
  cases s
  · show ∃ Rc : RemC P (30 * P.d) (winCl A pstar) (cornL A pstar) (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = pairBc (zpQ4 A pstar : ℝ) (zpQ2 A pstar) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, remQ κ (zpQfam κ A) b (ts 0) (ts 1) k = Rc.f ts k
    obtain ⟨Rc, h1, h2⟩ := remC_cpl_at A b E R.hd R.hL1 R.hδ0 R.hθ6 R.hκL R.hκγ hqq hqp hcoh hn (size_half_cpl _) hCR0 hCR h24
      (hwc _ (Or.inl rfl))
    exact ⟨Rc, h1, fun ts hts => h2 ts (h1 ▸ hts)⟩
  · show ∃ Rc : RemC P (30 * P.d) (winCh A pstar) (cornH A pstar) (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = pairBc (zpQh A pstar : ℝ) (zpQ2 A pstar) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, remQ κ (zpQfam κ A) b (ts 0) (ts 1) k = Rc.f ts k
    obtain ⟨Rc, h1, h2⟩ := remC_cpl_at A b E R.hd R.hL1 R.hδ0 R.hθ6 R.hκL R.hκγ hqq hqp hcoh hn (size_half_cpl _) hCR0 hCR (h24.trans h4h)
      (hwc _ (Or.inr rfl))
    exact ⟨Rc, h1, fun ts hts => h2 ts (h1 ▸ hts)⟩

include hcan hel htc hcc in
/-- **`RemC` of the carrier-side tree of a good index on the window `s`.** -/
theorem remTreeWin (R : RemEnv P κ) (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)
    {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) {CR : ℝ} (hCR0 : 0 < CR)
    (hCR : P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
      layerCost Bh (zpObjT b.1 pstar) < CR) (s : Bool) :
    ∃ Rc : RemC P 0 (cond s (winTh A pstar) (winTl A pstar)) (cond s (cornH A pstar) (cornL A pstar))
        (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = cond s (pairBcGt (zpQh A pstar : ℝ) (zpQ2 A pstar)) (pairBcGt (zpQ4 A pstar : ℝ) (zpQ2 A pstar)) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, remT κ (zpTfam κ A) b (ts 0) (ts 1) k = Rc.f ts k := by
  obtain ⟨qg, hq, hcoh, hwc⟩ := gateSel_tree A sp0 hA hcan hel htc hcc hb
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have hhp := zpQh_le_p A hcan hel htc hcc
  have hqq : zpQ2 A pstar ≤ qg := by rcases hq with rfl | rfl <;> omega
  have hqp : qg ≤ p := by rcases hq with rfl | rfl <;> omega
  have hn : (zpCodeT b.1 pstar).size / 2 ≤ P.N (p + 1) ^ 4 :=
    (nT_le A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb)).trans hN
  cases s
  · show ∃ Rc : RemC P 0 (winTl A pstar) (cornL A pstar) (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = pairBcGt (zpQ4 A pstar : ℝ) (zpQ2 A pstar) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, remT κ (zpTfam κ A) b (ts 0) (ts 1) k = Rc.f ts k
    obtain ⟨Rc, h1, h2⟩ := remC_tree_at A b E R.hd R.hL1 R.hδ0 R.hθ6 R.hκL R.hκγ hqq hqp hcoh hn (size_half_chain _) hCR0 hCR h24
      (hwc _ (Or.inl rfl))
    exact ⟨Rc, h1, fun ts hts => h2 ts (h1 ▸ hts)⟩
  · show ∃ Rc : RemC P 0 (winTh A pstar) (cornH A pstar) (trC (6 * P.η ^ 6) * CR),
      Rc.Bc = pairBcGt (zpQh A pstar : ℝ) (zpQ2 A pstar) ∧
      ∀ ts ∈ Rc.Bc, ∀ k, remT κ (zpTfam κ A) b (ts 0) (ts 1) k = Rc.f ts k
    obtain ⟨Rc, h1, h2⟩ := remC_tree_at A b E R.hd R.hL1 R.hδ0 R.hθ6 R.hκL R.hκγ hqq hqp hcoh hn (size_half_chain _) hCR0 hCR (h24.trans h4h)
      (hwc _ (Or.inr rfl))
    exact ⟨Rc, h1, fun ts hts => h2 ts (h1 ▸ hts)⟩


/-- An empty-continuity-set remainder (for indices off `bsA ∪ bsB`). -/
theorem remC_empty {Λ₂ : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} (hcell : B ⊆ cell q) (hint : B ⊆ closure (interior B))
    {CR : ℝ} (hCR : 0 < CR) : ∃ R : RemC P Λ₂ B q CR, R.Bc = ∅ :=
  ⟨⟨fun _ _ => 0, ∅, hcell, hint, Set.empty_subset _, Set.empty_subset _, fun _ => continuousOn_const, hCR.le,
    by rw [xnormRestr_zero_fun]; exact ENNReal.ofReal_pos.2 hCR⟩, rfl⟩

variable (R : RemEnv P κ) (CRq CRt : ST w ι pstar J → ℝ)

include hcan hel htc hcc in
open Classical in
/-- The couple remainder `RemC` of the index `b` on the window `s` (empty continuity set off `bsA ∪ bsB`). -/
noncomputable def rqOf (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4) (hq0 : ∀ b, 0 < CRq b)
    (hgq : ∀ b, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjC b.1 pstar) < CRq b) (s : Bool) (b : ST w ι pstar J) :
    RemC P (30 * P.d) (cond s (winCh A pstar) (winCl A pstar)) (cond s (cornH A pstar) (cornL A pstar))
      (trC (6 * P.η ^ 6) * CRq b) :=
  if hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA then
    Classical.choose (remCplWin A sp0 hA hcan hel htc hcc R E hN hb (hq0 b) (hgq b hb) s)
  else Classical.choose (remC_empty (P := P) (Λ₂ := 30 * P.d) (B := cond s (winCh A pstar) (winCl A pstar))
      (q := cond s (cornH A pstar) (cornL A pstar))
      (by cases s <;> exact timeBox_subset_cell _ _)
      (by cases s <;> exact timeBox_subset_closure_interior _ _)
      (CR := trC (6 * P.η ^ 6) * CRq b)
      (by have := one_le_trC (θ := 6 * P.η ^ 6) (by have := R.hd; positivity); have := hq0 b; positivity))

include hcan hel htc hcc in
open Classical in
/-- The tree remainder `RemC` of the index `b` on the window `s`. -/
noncomputable def rtOf (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4) (hq0 : ∀ b, 0 < CRt b)
    (hgt : ∀ b, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjT b.1 pstar) < CRt b) (s : Bool) (b : ST w ι pstar J) :
    RemC P 0 (cond s (winTh A pstar) (winTl A pstar)) (cond s (cornH A pstar) (cornL A pstar))
      (trC (6 * P.η ^ 6) * CRt b) :=
  if hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA then
    Classical.choose (remTreeWin A sp0 hA hcan hel htc hcc R E hN hb (hq0 b) (hgt b hb) s)
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
variable (hgq : ∀ b, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeC b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjC b.1 pstar) < CRq b)
variable (hgt : ∀ b, (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) →
      P.C₁ * (P.C₁ * P.δ) ^ ((zpCodeT b.1 pstar).size / 2) * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * (1 : ℕ)) *
        layerCost Bh (zpObjT b.1 pstar) < CRt b)
variable (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc in
theorem rqOf_good {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) (s : Bool) :
    (rqOf A sp0 hA hcan hel htc hcc R CRq E hN hq0 hgq s b).Bc =
        cond s (pairBc (zpQh A pstar : ℝ) (zpQ2 A pstar)) (pairBc (zpQ4 A pstar : ℝ) (zpQ2 A pstar)) ∧
      ∀ ts ∈ (rqOf A sp0 hA hcan hel htc hcc R CRq E hN hq0 hgq s b).Bc, ∀ k,
        remQ κ (zpQfam κ A) b (ts 0) (ts 1) k = (rqOf A sp0 hA hcan hel htc hcc R CRq E hN hq0 hgq s b).f ts k := by
  unfold rqOf
  rw [dif_pos hb]
  exact Classical.choose_spec (remCplWin A sp0 hA hcan hel htc hcc R E hN hb (hq0 b) (hgq b hb) s)

include hcan hel htc hcc in
theorem rqOf_bad {b : ST w ι pstar J} (hb : ¬ (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)) (s : Bool) :
    (rqOf A sp0 hA hcan hel htc hcc R CRq E hN hq0 hgq s b).Bc = ∅ := by
  unfold rqOf
  rw [dif_neg hb]
  exact Classical.choose_spec (remC_empty (P := P) (Λ₂ := 30 * P.d) (B := cond s (winCh A pstar) (winCl A pstar))
      (q := cond s (cornH A pstar) (cornL A pstar))
      (by cases s <;> exact timeBox_subset_cell _ _)
      (by cases s <;> exact timeBox_subset_closure_interior _ _)
      (CR := trC (6 * P.η ^ 6) * CRq b)
      (by have := one_le_trC (θ := 6 * P.η ^ 6) (by have := R.hd; positivity); have := hq0 b; positivity))

include hcan hel htc hcc in
theorem rtOf_good {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) (s : Bool) :
    (rtOf A sp0 hA hcan hel htc hcc R CRt E hN ht0 hgt s b).Bc =
        cond s (pairBcGt (zpQh A pstar : ℝ) (zpQ2 A pstar)) (pairBcGt (zpQ4 A pstar : ℝ) (zpQ2 A pstar)) ∧
      ∀ ts ∈ (rtOf A sp0 hA hcan hel htc hcc R CRt E hN ht0 hgt s b).Bc, ∀ k,
        remT κ (zpTfam κ A) b (ts 0) (ts 1) k = (rtOf A sp0 hA hcan hel htc hcc R CRt E hN ht0 hgt s b).f ts k := by
  unfold rtOf
  rw [dif_pos hb]
  exact Classical.choose_spec (remTreeWin A sp0 hA hcan hel htc hcc R E hN hb (ht0 b) (hgt b hb) s)

include hcan hel htc hcc in
theorem rtOf_bad {b : ST w ι pstar J} (hb : ¬ (b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)) (s : Bool) :
    (rtOf A sp0 hA hcan hel htc hcc R CRt E hN ht0 hgt s b).Bc = ∅ := by
  unfold rtOf
  rw [dif_neg hb]
  exact Classical.choose_spec (remC_empty (P := P) (Λ₂ := 0) (B := cond s (winTh A pstar) (winTl A pstar))
      (q := cond s (cornH A pstar) (cornL A pstar))
      (by cases s <;> exact timeBoxGt_subset_cell _ _)
      (by cases s
          · exact timeBoxGt_subset_closure_interior (L2_le_L4R A hcan hel htc hcc)
          · exact timeBoxGt_subset_closure_interior (L2_le_LhR A hcan hel htc hcc))
      (CR := trC (6 * P.η ^ 6) * CRt b)
      (by have := one_le_trC (θ := 6 * P.η ^ 6) (by have := R.hd; positivity); have := ht0 b; positivity))

include hcan hel htc hcc E hN in
open Classical in
/-- **The certified source of a level** (`Src`): the certified terms of `certSrcOf` and, for every `s`, the `RemC`s of the remainders `remQ`, `remT` of the approximant families
`zpQfam`, `zpTfam`, with the constants `trC · CRq b`, `trC · CRt b` (`CRq`, `CRt` positive, and above the gate bounds on `bsA ∪ bsB`). -/
noncomputable def srcOf : Src P (sepFamOf (κ := κ) A sp0 hA hcan hel htc hcc E hN).S (remQ κ (zpQfam κ A)) (remT κ (zpTfam κ A))
    (zpQ2 A pstar : ℝ) (zpQ4 A pstar : ℝ) (zpQh A pstar : ℝ) where
  toCertSrc := certSrcOf (κ := κ) A sp0 hA hcan hel htc hcc E hN
  CRq b := trC (6 * P.η ^ 6) * CRq b
  CRt b := trC (6 * P.η ^ 6) * CRt b
  rq := rqOf A sp0 hA hcan hel htc hcc R CRq E hN hq0 hgq
  rt := rtOf A sp0 hA hcan hel htc hcc R CRt E hN ht0 hgt
  hRQ s b x y hm k := by
    by_cases hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA
    · have := (rqOf_good A sp0 hA hcan hel htc hcc R CRq hq0 hgq E hN hb s).2 ![x, y] hm k
      simpa using this
    · rw [rqOf_bad A sp0 hA hcan hel htc hcc R CRq hq0 hgq E hN hb s] at hm
      exact absurd hm (Set.notMem_empty _)
  hRT s b x y hm k := by
    by_cases hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA
    · have := (rtOf_good A sp0 hA hcan hel htc hcc R CRt ht0 hgt E hN hb s).2 ![x, y] hm k
      simpa using this
    · rw [rtOf_bad A sp0 hA hcan hel htc hcc R CRt ht0 hgt E hN hb s] at hm
      exact absurd hm (Set.notMem_empty _)
  win_rq b hb := by
    refine ⟨fun t ht s hs _ => ⟨trivial, ?_⟩, fun t ht s hs _ => ⟨trivial, ?_⟩⟩
    · rw [(rqOf_good A sp0 hA hcan hel htc hcc R CRq hq0 hgq E hN hb false).1]
      exact ⟨by simpa using ht, by simpa using hs⟩
    · rw [(rqOf_good A sp0 hA hcan hel htc hcc R CRq hq0 hgq E hN hb true).1]
      exact ⟨by simpa using ht, by simpa using hs⟩
  win_rt b hb := by
    refine ⟨fun t ht s hs hg => ⟨trivial, ?_⟩, fun t ht s hs hg => ⟨trivial, ?_⟩⟩
    · rw [(rtOf_good A sp0 hA hcan hel htc hcc R CRt ht0 hgt E hN hb false).1]
      exact ⟨⟨by simpa using ht, by simpa using hs⟩, by simpa using hg rfl⟩
    · rw [(rtOf_good A sp0 hA hcan hel htc hcc R CRt ht0 hgt E hN hb true).1]
      exact ⟨⟨by simpa using ht, by simpa using hs⟩, by simpa using hg rfl⟩

end SrcOf

end WaveTurbulence.VineEstS5C.P4.W2
