/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5B.StateOps

/-! # V5 Step 4d-B: closed form of the exceptional factor (untwisted chart)

`rowVal ν rq rt t0 p p' Lq M`: the exceptional factor of a state whose lower joint has sign `ν`: the condition `t0 < p`, the
couple row `rq` read at the parent clocks of its positive and negative leaf (`(t0, p')` if `ν = 1`, `(p', t0)` otherwise) and
the label `Lq`, and the tree row `rt` read at `(p, t0)` and the label `M`.

`exc_same`: in the chart of the source garden, `spartExc` is `rowVal` with `p = u (parent of lower)`, `p' = u (parent of
partner)`, `Lq = base + lattice (x retained)`, `M = base + lattice (x lower)`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

/-- The exceptional factor of a state, in terms of its two row functions. -/
@[expose] noncomputable def rowVal {d : ℕ} (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ) (t0 p p' : ℝ) (Lq M : Mom d) : ℂ :=
  open Classical in
  (if t0 < p then 1 else 0) * ((if ν = 1 then rq t0 p' Lq else rq p' t0 Lq) * rt p t0 M)

variable {w : ℕ} {G : Garden w} (P : CorePlacement G)

/-- The parent branch of the lower joint. -/
@[expose] noncomputable def qbOf : GBranch G.tree := P.lower.toNode.parent P.nonroot

/-- The parent branch of the partner of the retained leaf. -/
@[expose] noncomputable def qrOf : GBranch G.tree := (G.pair P.retained).toNode.parent P.paired_nonroot

section Same
variable {d : ℕ} (hG : G.IsPlain) (D2 : ReconstructionData G) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer2 : GNode (D2.forest hG) → ℕ) (hLayer2 : IsLayering (D2.garden hG) layer2) (base : Mom d)
  {S : Finset (GBranch G.tree)} {a : GBranch G.tree}

theorem exc_same {b : GBranch G.tree} (hb : b = P.lower) (x : GNode G.tree → (Fin d → ℤ)) (hp : PairedAt P x)
    (u : GBranch G.tree → ℝ) :
    spartExc D2 hG L γ δ F layer2 hLayer2 base S a b (pairOfLeaf G hG P.retained) x u =
      rowVal (G.sign b.toNode) (VineEst.selCoupleRow L γ δ F D2 hG layer2 hLayer2 (pairOfLeaf G hG P.retained))
        (VineEst.selTreeRow L γ δ F D2 hG layer2 hLayer2 b) (u b) (u (qbOf P)) (u (qrOf P))
        (base + latticePoint L (x P.retained.toNode)) (base + latticePoint L (x b.toNode)) := by
  classical
  subst hb
  have hpb : parentClock (u a) u P.lower.toNode = u (qbOf P) := parentClock_nonroot _ _ _ P.nonroot
  have hpr : parentClock (u a) u P.retained.toNode = u P.lower := by
    rw [P.child]; exact parentClock_child _ _ _ _
  have hpp : parentClock (u a) u (G.pair P.retained).toNode = u (qrOf P) := parentClock_nonroot _ _ _ P.paired_nonroot
  have hs : nodeSign G.sig P.retained.1 = G.sign P.lower.toNode := by
    have : G.sign P.retained.toNode = G.sign P.lower.toNode := by
      rw [P.child]; exact Mole.outer_child_sign G P.lower P.keep P.outer
    exact this
  unfold spartExc rowVal qRow tRow
  rw [hpb]
  by_cases hν : G.sign P.lower.toNode = 1
  · obtain ⟨hf, hsec⟩ := pairOfLeaf_sides_pos G hG P.retained (hs.trans hν)
    rw [hf, hsec, hpr, hpp, if_pos hν]
    rfl
  · obtain ⟨hf, hsec⟩ := pairOfLeaf_sides_neg G hG P.retained (fun e => hν (hs.symm.trans e))
    have hlab : x (G.pair P.retained).toNode = x P.retained.toNode := hp.symm
    rw [hf, hsec, hpr, hpp, if_neg hν]
    unfold cosetDecoration
    rw [hlab]

end Same

section Tw

theorem parent_b' : (eB P P.lower).toNode.parent (reversePlacement G P).nonroot = eB P (qrOf P) := by
  apply Subtype.ext
  have h1 : ((eB P P.lower).toNode.parent (reversePlacement G P).nonroot).1 =
      ((G.pair P.retained).1.1, List.dropLast (G.pair P.retained).1.2) := by
    change (((eB P P.lower).1.1, List.dropLast (eB P P.lower).1.2)) = _
    rw [show (eB P P.lower).1 = (G.pair P.retained).1 from coreBranchEquiv_lower_val G P]
  have h2 : (eB P (qrOf P)).1 = (qrOf P).1 := coreBranchEquiv_fixed_val G P _ (paired_parent_outside G P)
  rw [h1, h2]
  rfl

theorem parent_partner' :
    ((unitTwistGarden G P).pair (eL P P.retained)).toNode.parent (reversePlacement G P).paired_nonroot =
      eB P (qbOf P) := by
  apply Subtype.ext
  have e : (unitTwistGarden G P).pair (eL P P.retained) = eL P (G.pair P.retained) := unitTwistGarden_pair G P _
  have h1 : (((unitTwistGarden G P).pair (eL P P.retained)).toNode.parent (reversePlacement G P).paired_nonroot).1 =
      (P.lower.1.1, List.dropLast P.lower.1.2) := by
    change ((((unitTwistGarden G P).pair (eL P P.retained)).toNode.1.1,
      List.dropLast ((unitTwistGarden G P).pair (eL P P.retained)).toNode.1.2)) = _
    rw [e]
    have := coreLeafEquiv_paired_val G P
    change (((eL P (G.pair P.retained)).1.1, List.dropLast (eL P (G.pair P.retained)).1.2)) = _
    rw [show (eL P (G.pair P.retained)).1 = P.lower.1 from this]
  have h2 : (eB P (qbOf P)).1 = (qbOf P).1 := coreBranchEquiv_fixed_val G P _ (lower_parent_outside G P)
  rw [h1, h2]
  rfl

end Tw

theorem tp_p0 (hG : G.IsPlain) : tp P hG (pairOfLeaf G hG P.retained) =
    pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P P.retained) := by
  have hpe : tp P hG (pairOfLeaf G hG P.retained) = pairOfLeaf (unitTwistGarden G P) (unitTwistGarden_plain G P hG)
      (eL P ((pairOfLeaf G hG P.retained).firstLeaf hG)) := rfl
  rw [hpe]
  rcases LFTwist.pairOfLeaf_first_or_partner G hG P.retained with e | e
  · rw [e]
  · have e2 : (unitTwistGarden G P).pair (eL P P.retained) = eL P (G.pair P.retained) :=
      unitTwistGarden_pair G P P.retained
    rw [e, ← e2, pairOfLeaf_partner]

section TwExc
variable {d : ℕ} (hG : G.IsPlain) (D' : ReconstructionData (unitTwistGarden G P)) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer' : GNode (D'.forest (unitTwistGarden_plain G P hG)) → ℕ)
  (hLayer' : IsLayering (D'.garden (unitTwistGarden_plain G P hG)) layer') (base : Mom d)
  (S : Finset (GBranch G.tree)) {a : GBranch G.tree}

theorem exc_tw {b : GBranch G.tree} (hb : b = P.lower) (x : GNode G.tree → (Fin d → ℤ))
    (u' : GBranch (unitTwistGarden G P).tree → ℝ) (u : GBranch G.tree → ℝ)
    (hub : u' (eB P b) = u b) (hqb : u' (eB P (qbOf P)) = u (qbOf P)) (hqr : u' (eB P (qrOf P)) = u (qrOf P)) :
    spartExc D' (unitTwistGarden_plain G P hG) L γ δ F layer' hLayer' base (twistedAtoms G P S) (eB P a) (eB P b)
        (tp P hG (pairOfLeaf G hG P.retained)) (twistNodeLabels G P x) u' =
      rowVal ((unitTwistGarden G P).sign (eB P b).toNode)
        (VineEst.selCoupleRow L γ δ F D' (unitTwistGarden_plain G P hG) layer' hLayer'
          (tp P hG (pairOfLeaf G hG P.retained)))
        (VineEst.selTreeRow L γ δ F D' (unitTwistGarden_plain G P hG) layer' hLayer' (eB P b))
        (u b) (u (qrOf P)) (u (qbOf P))
        (base + latticePoint L (x P.lower.toNode)) (base + latticePoint L (x P.retained.toNode)) := by
  classical
  subst hb
  have hp0 := tp_p0 P hG
  have c_b : parentClock (u' (eB P a)) u' (eB P P.lower).toNode = u (qrOf P) := by
    rw [parentClock_nonroot _ _ _ (reversePlacement G P).nonroot, parent_b', hqr]
  have c_r : parentClock (u' (eB P a)) u' (eL P P.retained).toNode = u P.lower := by
    rw [parentClock_nonroot _ _ _ (retained_nonroot _ (reversePlacement G P))]
    have e : (eL P P.retained).toNode.parent (retained_nonroot _ (reversePlacement G P)) = eB P P.lower :=
      retained_parent _ (reversePlacement G P)
    rw [e]; exact hub
  have c_p : parentClock (u' (eB P a)) u' ((unitTwistGarden G P).pair (eL P P.retained)).toNode = u (qbOf P) := by
    rw [parentClock_nonroot _ _ _ (reversePlacement G P).paired_nonroot, parent_partner', hqb]
  have hc : (eL P P.retained).toNode = (eB P P.lower).child P.keep := (reversePlacement G P).child
  have hs : nodeSign (unitTwistGarden G P).sig (eL P P.retained).1 = (unitTwistGarden G P).sign (eB P P.lower).toNode := by
    have : (unitTwistGarden G P).sign (eL P P.retained).toNode = (unitTwistGarden G P).sign (eB P P.lower).toNode := by
      rw [hc]; exact Mole.outer_child_sign _ _ _ (reversePlacement G P).outer
    exact this
  have k_r : twistNodeLabels G P x (eL P P.retained).toNode = x P.lower.toNode := by
    have h := twistNodeLabels_leaf G P x P.retained
    rw [if_pos (Or.inl rfl)] at h; exact h
  have k_p : twistNodeLabels G P x ((unitTwistGarden G P).pair (eL P P.retained)).toNode = x P.lower.toNode := by
    have e2 : (unitTwistGarden G P).pair (eL P P.retained) = eL P (G.pair P.retained) :=
      unitTwistGarden_pair G P P.retained
    rw [e2]
    have h := twistNodeLabels_leaf G P x (G.pair P.retained)
    rw [if_pos (Or.inr rfl)] at h; exact h
  have k_b : twistNodeLabels G P x (eB P P.lower).toNode = x P.retained.toNode := twistNodeLabels_lower G P x
  unfold spartExc rowVal qRow tRow
  rw [c_b]
  by_cases hν : (unitTwistGarden G P).sign (eB P P.lower).toNode = 1
  · obtain ⟨hf, hsec⟩ := pairOfLeaf_sides_pos (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P P.retained)
      (hs.trans hν)
    rw [hp0, hf, hsec, c_r, c_p, if_pos hν, hub]
    unfold cosetDecoration
    rw [k_r, k_b]
  · obtain ⟨hf, hsec⟩ := pairOfLeaf_sides_neg (unitTwistGarden G P) (unitTwistGarden_plain G P hG) (eL P P.retained)
      (fun e => hν (hs.symm.trans e))
    rw [hp0, hf, hsec, c_r, c_p, if_neg hν, hub]
    unfold cosetDecoration
    rw [k_p, k_b]

end TwExc

section Mem
variable {P} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} {RS : CLRegionData G S a b}

theorem SLow.qb_mem (h : SLow P RS) : qbOf P ∈ S := by
  obtain ⟨hn, hq⟩ := RS.parentPattern.2
  have hb := h.lower
  subst hb
  exact hq

theorem SLow.qr_mem (h : SLow P RS) : qrOf P ∈ S := placement_paired_parent_mem G P h.placement

end Mem

end WaveTurbulence.VineEstS5B
