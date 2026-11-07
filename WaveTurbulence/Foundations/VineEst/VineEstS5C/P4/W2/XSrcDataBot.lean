/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.XSrcData
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotSFF

/-! # P4-W2 (session 20, 6B): the certified time factors of the bottom level as selected clamps (`XSrcData` for `botCertC`, `botCertT`) -/

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
  (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := kind) A j))
  (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc hA hup E hN in
theorem botCertC_at_Jdata (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    (i : Fin (botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).m) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBox (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal (botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).CJ ∧
      (botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).J i =
        K2.clampSel (q ≤ cplRootLayer (zpObjC b.1 pstar)) (q : ℝ) Jc := by
  unfold botCertC_at
  obtain ⟨Jc, h1, h2, h3⟩ := padJ_sel_data _ (q ≤ cplRootLayer (zpObjC b.1 pstar)) (q : ℝ) i
  exact ⟨Jc, h1, lt_of_le_of_lt (h2.trans (ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_left (by have := E.hC; positivity) (one_le_TR E.hη)))) (lt_certCJ E.hC E.hη _), h3⟩

include hcan hel htc hcc hA hup E hN in
theorem botCertT_at_Jdata (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    (i : Fin (botCertT_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).m) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal (botCertT_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).CJ ∧
      (botCertT_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh).J i =
        K2.clampSel (q ≤ treeRootLayer (zpObjT b.1 pstar)) (q : ℝ) Jc := by
  unfold botCertT_at
  obtain ⟨Jc, h1, h2, h3⟩ := padJ_sel_data _ (q ≤ treeRootLayer (zpObjT b.1 pstar)) (q : ℝ) i
  exact ⟨Jc, h1, lt_of_le_of_lt (h2.trans (ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_left (by have := E.hC; positivity) (one_le_TR E.hη)))) (lt_certCJ E.hC E.hη _), h3⟩

include hcan hel htc hcc hA hup E hN in
theorem botCertC_at_Jdata' (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    (O : ObjCert P (30 * P.d) (botQfam pstar κ A b) (winCl A pstar) (winCh A pstar) (cornL A pstar) (cornH A pstar))
    (hO : O = botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh) (i : Fin O.m) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBox (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal O.CJ ∧
      O.J i = K2.clampSel (q ≤ cplRootLayer (zpObjC b.1 pstar)) (q : ℝ) Jc := by
  subst hO
  exact botCertC_at_Jdata A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh i

include hcan hel htc hcc hA hup E hN in
theorem botCertT_at_Jdata' (b : BT w ι) (hb : b ∈ canonFinsetK p kind A c0) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    (O : ObjCert P 0 (botTfam pstar κ A b) (winTl A pstar) (winTh A pstar) (cornL A pstar) (cornH A pstar))
    (hO : O = botCertT_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh) (i : Fin O.m) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal O.CJ ∧
      O.J i = K2.clampSel (q ≤ treeRootLayer (zpObjT b.1 pstar)) (q : ℝ) Jc := by
  subst hO
  exact botCertT_at_Jdata A c0 hA hcan hel htc hcc hup E hN b hb q hq hcoh i

include hcan hel htc hcc hA hup E hN in
/-- **The certified couple time factors of a good index are selected clamps of continuous gate factors.** -/
theorem botCertC_Jdata {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0)
    (i : Fin (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    ∃ (q : ℕ) (fl : Prop) (_ : Decidable fl) (Jc : (Fin 2 → ℝ) → ℂ),
      zpQ2 A pstar ≤ q ∧ q ≤ zpQh A pstar ∧ Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBox (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ ∧
      (botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i = K2.clampSel fl (q : ℝ) Jc ∧
      (fl ∨ q ≤ zpQ4 A pstar ∨ zpQ4 A pstar + 2 ≤ q) := by
  classical
  have hG := mem_canon_of_botbs A c0 hb
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar
  · have he : botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b =
        botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hG (zpQ4 A pstar) (Or.inl rfl)
          (botg_coh_lowC A c0 hA hcan hel htc hcc hup hb hr) := by
      unfold botCertC; rw [dif_pos hb, dif_pos hr]
    obtain ⟨Jc, h1, h2, h3⟩ := botCertC_at_Jdata' A c0 hA hcan hel htc hcc hup E hN b hG (zpQ4 A pstar) (Or.inl rfl)
      (botg_coh_lowC A c0 hA hcan hel htc hcc hup hb hr) _ he i
    exact ⟨zpQ4 A pstar, _, inferInstance, Jc, h24, h4h, h1, h2, h3, Or.inr (Or.inl le_rfl)⟩
  · have hhi := botg_high_C A c0 hA hcan hel htc hcc hup b hG (not_le.1 hr)
    have he : botCertC (κ := κ) A c0 hA hcan hel htc hcc hup E hN b =
        botCertC_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hG (zpQQ b.1 pstar).1 (Or.inr hhi)
          (botg_nat_cohC A c0 hA hcan hel htc hcc hup b hG) := by
      unfold botCertC; rw [dif_pos hb, dif_neg hr]
    obtain ⟨Jc, h1, h2, h3⟩ := botCertC_at_Jdata' A c0 hA hcan hel htc hcc hup E hN b hG (zpQQ b.1 pstar).1 (Or.inr hhi)
      (botg_nat_cohC A c0 hA hcan hel htc hcc hup b hG) _ he i
    refine ⟨(zpQQ b.1 pstar).1, _, inferInstance, Jc, ?_, ?_, h1, h2, h3, ?_⟩
    · rw [hhi]; exact h24.trans h4h
    · rw [hhi]
    · by_cases hf : (zpQQ b.1 pstar).1 ≤ cplRootLayer (zpObjC b.1 pstar)
      · exact Or.inl hf
      · right; right
        have := not_le.1 hr
        omega

include hcan hel htc hcc hA hup E hN in
/-- **The certified tree time factors of a good index are selected clamps of continuous gate factors.** -/
theorem botCertT_Jdata {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0)
    (i : Fin (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).m) :
    ∃ (q : ℕ) (fl : Prop) (_ : Decidable fl) (Jc : (Fin 2 → ℝ) → ℂ),
      zpQ2 A pstar ≤ q ∧ q ≤ zpQh A pstar ∧ Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).CJ ∧
      (botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b).J i = K2.clampSel fl (q : ℝ) Jc ∧
      (fl ∨ q ≤ zpQ4 A pstar ∨ zpQ4 A pstar + 2 ≤ q) := by
  classical
  have hG := mem_canon_of_botbs A c0 hb
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar
  · have he : botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b =
        botCertT_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hG (zpQ4 A pstar) (Or.inl rfl)
          (botg_coh_lowT A c0 hA hcan hel htc hcc hup hb hr) := by
      unfold botCertT; rw [dif_pos hb, dif_pos hr]
    obtain ⟨Jc, h1, h2, h3⟩ := botCertT_at_Jdata' A c0 hA hcan hel htc hcc hup E hN b hG (zpQ4 A pstar) (Or.inl rfl)
      (botg_coh_lowT A c0 hA hcan hel htc hcc hup hb hr) _ he i
    exact ⟨zpQ4 A pstar, _, inferInstance, Jc, h24, h4h, h1, h2, h3, Or.inr (Or.inl le_rfl)⟩
  · have hhi := botg_high_T A c0 hA hcan hel htc hcc hup b hG (not_le.1 hr)
    have he : botCertT (κ := κ) A c0 hA hcan hel htc hcc hup E hN b =
        botCertT_at (κ := κ) A c0 hA hcan hel htc hcc hup E hN b hG (zpBranchQ b.1 pstar).1 (Or.inr hhi)
          (botg_nat_cohT A c0 hA hcan hel htc hcc hup b hG) := by
      unfold botCertT; rw [dif_pos hb, dif_neg hr]
    obtain ⟨Jc, h1, h2, h3⟩ := botCertT_at_Jdata' A c0 hA hcan hel htc hcc hup E hN b hG (zpBranchQ b.1 pstar).1 (Or.inr hhi)
      (botg_nat_cohT A c0 hA hcan hel htc hcc hup b hG) _ he i
    refine ⟨(zpBranchQ b.1 pstar).1, _, inferInstance, Jc, ?_, ?_, h1, h2, h3, ?_⟩
    · rw [hhi]; exact h24.trans h4h
    · rw [hhi]
    · by_cases hf : (zpBranchQ b.1 pstar).1 ≤ treeRootLayer (zpObjT b.1 pstar)
      · exact Or.inl hf
      · right; right
        have := not_le.1 hr
        omega


end WaveTurbulence.VineEstS5C.P4.W2
