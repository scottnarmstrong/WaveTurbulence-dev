/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam

/-! # P4-W1: the clocks of the windows lie in the identity sets of the certified expansions (for the term certificates)

`mem_certC_V`: for an index `b ∈ bsA ∪ bsB`, every point `(t, s)` with `s ∈ [L₂, L₂+1]` and `t` strictly inside the `L₄` window or
above `Lₕ` lies in the identity set of `certC b`, so the couple terms are the separated terms there (`ObjExp.term_of_mem`).
`mem_certT_V`: the same for trees, with `s < t` and `s < L₂ + 1`.  (The edges `t = L₄`, `t = L₄ + 1`, `s = L₂ + 1` of the closed window
boxes are null sets of times.)  `zp_half_sizes`: the exceptional orders of every state of `Zp(A)` add up to `zpN A` (the invariance of
`n₍₂₎` under the twists: the rows of an operative vine have the start's total order).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj
  WaveTurbulence.Stage1 WaveTurbulence.ConjCoh WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS3

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
  (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

include hcan hel htc hcc in
/-- **Invariance of the exceptional orders** on the twist class. -/
theorem zp_half_sizes (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) :
    (zpCodeC b.1 pstar).size / 2 + (zpCodeT b.1 pstar).size / 2 = zpN A pstar := by
  have h := zp_sizes A sp0 hA hcan hel htc hcc b hb
  have h1 := size_half_cpl (zpCodeC b.1 pstar)
  have h2 := size_half_chain (zpCodeT b.1 pstar)
  omega

include hcan hel htc hcc in
/-- The window points lie in the identity set of the couple expansion. -/
theorem mem_certC_V {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) {t s : ℝ}
    (hs1 : (zpQ2 A pstar : ℝ) ≤ s) (hs2 : s ≤ zpQ2 A pstar + 1)
    (ht : ((zpQ4 A pstar : ℝ) < t ∧ t < zpQ4 A pstar + 1) ∨ (zpQh A pstar : ℝ) < t) :
    ![t, s] ∈ (certC A sp0 hA hcan hel htc hcc E hN b).V := by
  classical
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  unfold certC
  rw [dif_pos hb]
  split_ifs with hr
  · unfold certC_at
    show ![t, s] ∈ VC _ _ _ _
    refine ⟨⟨by simpa using hs1, by simpa using hs2⟩, Or.inl ?_⟩
    simp only [Matrix.cons_val_zero]
    rcases ht with ⟨h1, -⟩ | h1
    · exact h1
    · exact lt_of_le_of_lt (by exact_mod_cast h4h) h1
  · have hG := mem_zpFinset_of_bs A sp0 hA hb
    have hhi := zp_high_C A sp0 hA hcan hel htc hcc b hG (not_le.1 hr)
    unfold certC_at
    show ![t, s] ∈ VC _ _ _ _
    refine ⟨⟨by simpa using hs1, by simpa using hs2⟩, ?_⟩
    simp only [Matrix.cons_val_zero]
    rw [hhi]
    have hr' : zpQ4 A pstar + 1 ≤ zpLq b := not_le.1 hr
    have hLr : zpLq b ≤ zpQh A pstar := by
      rw [← hhi]; exact (cplRoot_le_nat A sp0 hA hcan hel htc hcc b hG).2
    rcases ht with ⟨h1, h2⟩ | h1
    · refine Or.inr ⟨h1, ?_, ?_⟩
      · exact le_trans h2.le (by exact_mod_cast hr')
      · exact lt_of_lt_of_le h2 (by exact_mod_cast hr'.trans hLr)
    · exact Or.inl h1

include hcan hel htc hcc in
/-- The window points (with `s < t`) lie in the identity set of the tree expansion. -/
theorem mem_certT_V {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA) {t s : ℝ}
    (hs1 : (zpQ2 A pstar : ℝ) ≤ s) (hs2 : s < zpQ2 A pstar + 1) (hst : s < t)
    (ht : ((zpQ4 A pstar : ℝ) < t ∧ t < zpQ4 A pstar + 1) ∨ (zpQh A pstar : ℝ) < t) :
    ![t, s] ∈ (certT A sp0 hA hcan hel htc hcc E hN b).V := by
  classical
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have h24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  unfold certT
  rw [dif_pos hb]
  split_ifs with hr
  · unfold certT_at
    show ![t, s] ∈ VT _ _ _ _
    refine ⟨⟨by simpa using hs1, by simpa using hs2⟩, Or.inl ⟨?_, ?_⟩⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    · rcases ht with ⟨h1, -⟩ | h1
      · exact h1
      · exact lt_of_le_of_lt (by exact_mod_cast h4h) h1
    · refine lt_min hst (lt_of_lt_of_le hs2 ?_)
      have : (zpQ2 A pstar : ℝ) ≤ zpQ4 A pstar := by exact_mod_cast h24
      linarith
  · have hG := mem_zpFinset_of_bs A sp0 hA hb
    have hhi := zp_high_T A sp0 hA hcan hel htc hcc b hG (not_le.1 hr)
    unfold certT_at
    show ![t, s] ∈ VT _ _ _ _
    refine ⟨⟨by simpa using hs1, by simpa using hs2⟩, ?_⟩
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hhi]
    have hr' : zpQ4 A pstar + 1 ≤ zpLt b := not_le.1 hr
    have hLr : zpLt b ≤ zpQh A pstar := by
      rw [← hhi]; exact (treeRoot_le_nat A sp0 hA hcan hel htc hcc b hG).2
    rcases ht with ⟨h1, h2⟩ | h1
    · refine Or.inr ⟨h1, ?_, ?_⟩
      · exact le_trans h2.le (by exact_mod_cast hr')
      · exact lt_of_lt_of_le h2 (by exact_mod_cast hr'.trans hLr)
    · refine Or.inl ⟨h1, lt_min hst (lt_of_lt_of_le hs2 ?_)⟩
      have : (zpQ2 A pstar : ℝ) ≤ zpQh A pstar := by exact_mod_cast h24.trans h4h
      linarith

end WaveTurbulence.VineEstS5C.P4.W13
