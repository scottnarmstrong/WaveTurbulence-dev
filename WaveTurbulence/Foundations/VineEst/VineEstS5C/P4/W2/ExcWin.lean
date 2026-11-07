/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxCont3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.PieceAll1
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.CertTerms
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Mem

/-! # P4-W2 (session 7, step 3b): the window facts for the certified terms

`WinOK V Bc I1 I0 gt`: every clock pair `(t, s)` with `t ∈ I1` (the first clock) and `s ∈ I0` (the second clock, `t₀`; and `s < t` for trees, `gt = true`) lies
in the identity set `V` and the continuity set `Bc` of a certified term.  `certC_loCT_win` etc.: the low term has `I1 = (L₄, L₄+1)`, the high term
`I1 = (Lₕ, Lₕ+1)`, with `I0 = (L₂, L₂+1)`; this is what the open windows of `DomX` provide (a.e. off the window boundaries). -/

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
  (E : GateEnv P κ p Bh) (hN : zpN A pstar ≤ P.N (p + 1) ^ 4)

/-- Window facts for a certified term: the clock pairs of the open windows lie in the identity and continuity sets. -/
def WinOK (V Bc : Set (Fin 2 → ℝ)) (I1 I0 : Set ℝ) (gt : Bool) : Prop :=
  ∀ t ∈ I1, ∀ s ∈ I0, (gt = true → s < t) → ![t, s] ∈ V ∧ ![t, s] ∈ Bc

theorem WinOK.mono {V Bc : Set (Fin 2 → ℝ)} {I1 I1' I0 I0' : Set ℝ} {gt : Bool} (h : WinOK V Bc I1 I0 gt)
    (h1 : I1' ⊆ I1) (h0 : I0' ⊆ I0) : WinOK V Bc I1' I0' gt :=
  fun t ht s hs hg => h t (h1 ht) s (h0 hs) hg

include hcan hel htc hcc E hN in
theorem certC_loCT_win {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)
    (i : Fin (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    WinOK (certC_loCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i).V (certC_loCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i).Bc
      (Set.Ioo (zpQ4 A pstar : ℝ) (zpQ4 A pstar + 1)) (Set.Ioo (zpQ2 A pstar : ℝ) (zpQ2 A pstar + 1)) false := by
  intro t ht s hs hg
  refine ⟨?_, ?_⟩
  · exact mem_certC_V A sp0 hA hcan hel htc hcc E hN hb hs.1.le hs.2.le (Or.inl ht)
  · show ![t, s] ∈ _
    simp only [certC_loTC, winCl, timeBox, timeBoxGt, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2.le⟩⟩, ht.2⟩

include hcan hel htc hcc E hN in
theorem certC_hiCT_win {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)
    (i : Fin (certC (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    WinOK (certC_hiCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i).V (certC_hiCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i).Bc
      (Set.Ioo (zpQh A pstar : ℝ) (zpQh A pstar + 1)) (Set.Ioo (zpQ2 A pstar : ℝ) (zpQ2 A pstar + 1)) false := by
  intro t ht s hs hg
  refine ⟨?_, ?_⟩
  · exact mem_certC_V A sp0 hA hcan hel htc hcc E hN hb hs.1.le hs.2.le (Or.inr ht.1)
  · show ![t, s] ∈ _
    simp only [certC_hiTC, winCh, timeBox, timeBoxGt, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2.le⟩⟩

include hcan hel htc hcc E hN in
theorem certT_loCT_win {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)
    (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    WinOK (certT_loCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i).V (certT_loCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i).Bc
      (Set.Ioo (zpQ4 A pstar : ℝ) (zpQ4 A pstar + 1)) (Set.Ioo (zpQ2 A pstar : ℝ) (zpQ2 A pstar + 1)) true := by
  intro t ht s hs hg
  refine ⟨?_, ?_⟩
  · exact mem_certT_V A sp0 hA hcan hel htc hcc E hN hb hs.1.le hs.2 (hg rfl) (Or.inl ht)
  · show ![t, s] ∈ _
    simp only [certT_loTC, winTl, timeBox, timeBoxGt, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨⟨⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2.le⟩⟩, hg rfl⟩, ht.2⟩

include hcan hel htc hcc E hN in
theorem certT_hiCT_win {b : ST w ι pstar J} (hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA)
    (i : Fin (certT (κ := κ) A sp0 hA hcan hel htc hcc E hN b).m) :
    WinOK (certT_hiCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i).V (certT_hiCT (κ := κ) A sp0 hA hcan hel htc hcc E hN b i).Bc
      (Set.Ioo (zpQh A pstar : ℝ) (zpQh A pstar + 1)) (Set.Ioo (zpQ2 A pstar : ℝ) (zpQ2 A pstar + 1)) true := by
  intro t ht s hs hg
  refine ⟨?_, ?_⟩
  · exact mem_certT_V A sp0 hA hcan hel htc hcc E hN hb hs.1.le hs.2 (hg rfl) (Or.inr ht.1)
  · show ![t, s] ∈ _
    simp only [certT_hiTC, winTh, timeBox, timeBoxGt, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Icc,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨⟨⟨ht.1.le, ht.2.le⟩, ⟨hs.1.le, hs.2.le⟩⟩, hg rfl⟩

end WaveTurbulence.VineEstS5C.P4.W2
