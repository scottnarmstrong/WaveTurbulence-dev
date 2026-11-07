/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotSFF
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.BotGeo

/-! # P4-W2 (bottom, session 9): the clocks of the windows lie in the identity sets of `botCertC`, `botCertT` (copy of `W13.Mem`). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj
  WaveTurbulence.Stage1 WaveTurbulence.ConjCoh WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.VineEstS5C.P4.Bot

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

include hcan hel htc hcc hup in
/-- The window points lie in the identity set of the couple expansion. -/
theorem mem_botCertC_V {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) {t s : ℝ}
    (hs1 : (zpQ2 A pstar : ℝ) ≤ s) (hs2 : s ≤ zpQ2 A pstar + 1)
    (ht : ((zpQ4 A pstar : ℝ) < t ∧ t < zpQ4 A pstar + 1) ∨ (zpQh A pstar : ℝ) < t) :
    ![t, s] ∈ (botCertC A c0 hA hcan hel htc hcc hup E hN b).V := by
  classical
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  unfold botCertC
  rw [dif_pos hb]
  split_ifs with hr
  · unfold botCertC_at
    show ![t, s] ∈ VC _ _ _ _
    refine ⟨⟨by simpa using hs1, by simpa using hs2⟩, Or.inl ?_⟩
    simp only [Matrix.cons_val_zero]
    rcases ht with ⟨h1, -⟩ | h1
    · exact h1
    · exact lt_of_le_of_lt (by exact_mod_cast h4h) h1
  · have hG := mem_canon_of_botbs A c0 hb
    have hhi := botg_high_C A c0 hA hcan hel htc hcc hup b hG (not_le.1 hr)
    unfold botCertC_at
    show ![t, s] ∈ VC _ _ _ _
    refine ⟨⟨by simpa using hs1, by simpa using hs2⟩, ?_⟩
    simp only [Matrix.cons_val_zero]
    rw [hhi]
    have hr' : zpQ4 A pstar + 1 ≤ botLq pstar b := not_le.1 hr
    have hLr : botLq pstar b ≤ zpQh A pstar := by
      rw [← hhi]; exact (botg_cplRoot_le_nat A c0 hA hcan hel htc hcc hup b hG).2
    rcases ht with ⟨h1, h2⟩ | h1
    · refine Or.inr ⟨h1, ?_, ?_⟩
      · exact le_trans h2.le (by exact_mod_cast hr')
      · exact lt_of_lt_of_le h2 (by exact_mod_cast hr'.trans hLr)
    · exact Or.inl h1

include hcan hel htc hcc hup in
/-- The window points (with `s < t`) lie in the identity set of the tree expansion. -/
theorem mem_botCertT_V {b : BT w ι} (hb : b ∈ botA p kind pstar A c0 ∨ b ∈ botB p kind pstar A c0) {t s : ℝ}
    (hs1 : (zpQ2 A pstar : ℝ) ≤ s) (hs2 : s < zpQ2 A pstar + 1) (hst : s < t)
    (ht : ((zpQ4 A pstar : ℝ) < t ∧ t < zpQ4 A pstar + 1) ∨ (zpQh A pstar : ℝ) < t) :
    ![t, s] ∈ (botCertT A c0 hA hcan hel htc hcc hup E hN b).V := by
  classical
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  unfold botCertT
  rw [dif_pos hb]
  split_ifs with hr
  · unfold botCertT_at
    show ![t, s] ∈ VT _ _ _ _
    refine ⟨⟨by simpa using hs1, by simpa using hs2⟩, Or.inl ⟨?_, ?_⟩⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    · rcases ht with ⟨h1, -⟩ | h1
      · exact h1
      · exact lt_of_le_of_lt (by exact_mod_cast h4h) h1
    · refine lt_min hst (lt_of_lt_of_le hs2 ?_)
      have : (zpQ2 A pstar : ℝ) ≤ zpQ4 A pstar := by exact_mod_cast h24
      linarith
  · have hG := mem_canon_of_botbs A c0 hb
    have hhi := botg_high_T A c0 hA hcan hel htc hcc hup b hG (not_le.1 hr)
    unfold botCertT_at
    show ![t, s] ∈ VT _ _ _ _
    refine ⟨⟨by simpa using hs1, by simpa using hs2⟩, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hhi]
    have hr' : zpQ4 A pstar + 1 ≤ botLt pstar b := not_le.1 hr
    have hLr : botLt pstar b ≤ zpQh A pstar := by
      rw [← hhi]; exact (botg_treeRoot_le_nat A c0 hA hcan hel htc hcc hup b hG).2
    rcases ht with ⟨h1, h2⟩ | h1
    · refine Or.inr ⟨h1, ?_, ?_⟩
      · exact le_trans h2.le (by exact_mod_cast hr')
      · exact lt_of_lt_of_le h2 (by exact_mod_cast hr'.trans hLr)
    · refine Or.inl ⟨h1, lt_min hst (lt_of_lt_of_le hs2 ?_)⟩
      have : (zpQ2 A pstar : ℝ) ≤ zpQh A pstar := by exact_mod_cast h24.trans h4h
      linarith

end WaveTurbulence.VineEstS5C.P4.W2
