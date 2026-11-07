/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Mem
public import WaveTurbulence.Foundations.VineEst.K2.OfContW

/-! # P4-W2 (session 20, 6B): the certified time factors as selected clamps of continuous gate factors

`padJ_sel_data`: every term of the padded selected clamp of a continuous gate expansion is `clampSel fl q Jc` for a continuous `Jc` with the
gate bound (`0` pads).  `certC_Jdata`, `certT_Jdata`: for a good index the certified time factors of `certC`, `certT` are `clampSel fl q Jc`,
with `fl ↔ q ≤ root layer`, and the gate/window side condition that makes the cross bound apply: the two-sided clamp is selected, or
`q = L₄` (the one-sided clamp agrees with it on both windows), or `L₄ + 2 ≤ q ≤ Lₕ` (far windows).
-/

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

section Pad
variable {P : WTParams} {n W : ℕ} {T : Set (Fin 2 → ℝ)} {F : (Fin 2 → ℝ) → Mom P.d → ℂ} {cost : ℝ}

theorem padJ_sel_data (E : ContExp P n W T F cost) (fl : Prop) [Decidable fl] (q : ℝ) (i : Fin (max E.m 1)) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) T Set.univ (fun ts _ => Jc ts) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
      padJ (fun j => K2.clampSel fl q (E.J j)) i = K2.clampSel fl q Jc := by
  unfold padJ
  by_cases h : i.val < E.m
  · rw [dif_pos h]
    exact ⟨E.J ⟨i.val, h⟩, E.hJc _, E.hJ _, rfl⟩
  · rw [dif_neg h]
    refine ⟨fun _ => 0, continuous_const, ?_, ?_⟩
    · rw [VineEstS3.Eng.XNorm00Restr_zero]; exact zero_le
    · funext ts
      by_cases hf : fl
      · rw [K2.clampSel_of_pos hf]; unfold K2.clamp2J; rfl
      · rw [K2.clampSel_of_neg hf]; unfold clampJ; simp

end Pad

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
  (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc E hN in
theorem certC_at_Jdata (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    (i : Fin (certC_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).m) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBox (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal (certC_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).CJ ∧
      (certC_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).J i =
        K2.clampSel (q ≤ cplRootLayer (zpObjC b.1 pstar)) (q : ℝ) Jc := by
  unfold certC_at
  obtain ⟨Jc, h1, h2, h3⟩ := padJ_sel_data _ (q ≤ cplRootLayer (zpObjC b.1 pstar)) (q : ℝ) i
  exact ⟨Jc, h1, lt_of_le_of_lt (h2.trans (ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_left (by have := E.hC; positivity) (one_le_TR E.hη)))) (lt_certCJ E.hC E.hη _), h3⟩

include hcan hel htc hcc E hN in
theorem certT_at_Jdata (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    (i : Fin (certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).m) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal (certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).CJ ∧
      (certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).J i =
        K2.clampSel (q ≤ treeRootLayer (zpObjT b.1 pstar)) (q : ℝ) Jc := by
  unfold certT_at
  obtain ⟨Jc, h1, h2, h3⟩ := padJ_sel_data _ (q ≤ treeRootLayer (zpObjT b.1 pstar)) (q : ℝ) i
  exact ⟨Jc, h1, lt_of_le_of_lt (h2.trans (ENNReal.ofReal_le_ofReal
    (le_mul_of_one_le_left (by have := E.hC; positivity) (one_le_TR E.hη)))) (lt_certCJ E.hC E.hη _), h3⟩

include hcan hel htc hcc E hN in
theorem certC_at_Jdata' (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar))
    (O : ObjCert P (30 * P.d) (zpQfam κ A b) (winCl A pstar) (winCh A pstar) (cornL A pstar) (cornH A pstar))
    (hO : O = certC_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh) (i : Fin O.m) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBox (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal O.CJ ∧
      O.J i = K2.clampSel (q ≤ cplRootLayer (zpObjC b.1 pstar)) (q : ℝ) Jc := by
  subst hO
  exact certC_at_Jdata A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh i

include hcan hel htc hcc E hN in
theorem certT_at_Jdata' (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar))
    (O : ObjCert P 0 (zpTfam κ A b) (winTl A pstar) (winTh A pstar) (cornL A pstar) (cornH A pstar))
    (hO : O = certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh) (i : Fin O.m) :
    ∃ Jc : (Fin 2 → ℝ) → ℂ, Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal O.CJ ∧
      O.J i = K2.clampSel (q ≤ treeRootLayer (zpObjT b.1 pstar)) (q : ℝ) Jc := by
  subst hO
  exact certT_at_Jdata A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh i

include hcan hel htc hcc E hN in
/-- **The certified couple time factors of a good index are selected clamps of continuous gate factors.** -/
theorem certC_Jdata {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)
    (i : Fin (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    ∃ (q : ℕ) (fl : Prop) (_ : Decidable fl) (Jc : (Fin 2 → ℝ) → ℂ),
      zpQ2 A pstar ≤ q ∧ q ≤ zpQh A pstar ∧ Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBox (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ ∧
      (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i = K2.clampSel fl (q : ℝ) Jc ∧
      (fl ∨ q ≤ zpQ4 A pstar ∨ zpQ4 A pstar + 2 ≤ q) := by
  classical
  have hG := mem_zpFinset_of_bs A sp0 hA hb
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar
  · have he : certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b =
        certC_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hG (zpQ4 A pstar) (Or.inl rfl)
          (zp_coh_lowC A sp0 hA hcan hel htc hcc hb hr) := by
      unfold certC; rw [dif_pos hb, dif_pos hr]
    obtain ⟨Jc, h1, h2, h3⟩ := certC_at_Jdata' A sp0 hA hcan hel htc hcc E hN b hG (zpQ4 A pstar) (Or.inl rfl)
      (zp_coh_lowC A sp0 hA hcan hel htc hcc hb hr) _ he i
    exact ⟨zpQ4 A pstar, _, inferInstance, Jc, h24, h4h, h1, h2, h3, Or.inr (Or.inl le_rfl)⟩
  · have hhi := zp_high_C A sp0 hA hcan hel htc hcc b hG (not_le.1 hr)
    have he : certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b =
        certC_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hG (zpQQ b.1 pstar).1 (Or.inr hhi)
          (nat_cohC A sp0 hA hcan hel htc hcc b hG) := by
      unfold certC; rw [dif_pos hb, dif_neg hr]
    obtain ⟨Jc, h1, h2, h3⟩ := certC_at_Jdata' A sp0 hA hcan hel htc hcc E hN b hG (zpQQ b.1 pstar).1 (Or.inr hhi)
      (nat_cohC A sp0 hA hcan hel htc hcc b hG) _ he i
    refine ⟨(zpQQ b.1 pstar).1, _, inferInstance, Jc, ?_, ?_, h1, h2, h3, ?_⟩
    · rw [hhi]; exact h24.trans h4h
    · rw [hhi]
    · by_cases hf : (zpQQ b.1 pstar).1 ≤ cplRootLayer (zpObjC b.1 pstar)
      · exact Or.inl hf
      · right; right
        have := not_le.1 hr
        omega

include hcan hel htc hcc E hN in
/-- **The certified tree time factors of a good index are selected clamps of continuous gate factors.** -/
theorem certT_Jdata {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)
    (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    ∃ (q : ℕ) (fl : Prop) (_ : Decidable fl) (Jc : (Fin 2 → ℝ) → ℂ),
      zpQ2 A pstar ≤ q ∧ q ≤ zpQh A pstar ∧ Continuous Jc ∧
      XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt (q : ℝ) (zpQ2 A pstar : ℝ)) Set.univ (fun ts _ => Jc ts) <
        ENNReal.ofReal (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).CJ ∧
      (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).J i = K2.clampSel fl (q : ℝ) Jc ∧
      (fl ∨ q ≤ zpQ4 A pstar ∨ zpQ4 A pstar + 2 ≤ q) := by
  classical
  have hG := mem_zpFinset_of_bs A sp0 hA hb
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  by_cases hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar
  · have he : certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b =
        certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hG (zpQ4 A pstar) (Or.inl rfl)
          (zp_coh_lowT A sp0 hA hcan hel htc hcc hb hr) := by
      unfold certT; rw [dif_pos hb, dif_pos hr]
    obtain ⟨Jc, h1, h2, h3⟩ := certT_at_Jdata' A sp0 hA hcan hel htc hcc E hN b hG (zpQ4 A pstar) (Or.inl rfl)
      (zp_coh_lowT A sp0 hA hcan hel htc hcc hb hr) _ he i
    exact ⟨zpQ4 A pstar, _, inferInstance, Jc, h24, h4h, h1, h2, h3, Or.inr (Or.inl le_rfl)⟩
  · have hhi := zp_high_T A sp0 hA hcan hel htc hcc b hG (not_le.1 hr)
    have he : certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b =
        certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hG (zpBranchQ b.1 pstar).1 (Or.inr hhi)
          (nat_cohT A sp0 hA hcan hel htc hcc b hG) := by
      unfold certT; rw [dif_pos hb, dif_neg hr]
    obtain ⟨Jc, h1, h2, h3⟩ := certT_at_Jdata' A sp0 hA hcan hel htc hcc E hN b hG (zpBranchQ b.1 pstar).1 (Or.inr hhi)
      (nat_cohT A sp0 hA hcan hel htc hcc b hG) _ he i
    refine ⟨(zpBranchQ b.1 pstar).1, _, inferInstance, Jc, ?_, ?_, h1, h2, h3, ?_⟩
    · rw [hhi]; exact h24.trans h4h
    · rw [hhi]
    · by_cases hf : (zpBranchQ b.1 pstar).1 ≤ treeRootLayer (zpObjT b.1 pstar)
      · exact Or.inl hf
      · right; right
        have := not_le.1 hr
        omega

end WaveTurbulence.VineEstS5C.P4.W2
