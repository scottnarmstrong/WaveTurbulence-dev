/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.K2.OfContW
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.Cert
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.ChCount

/-! # P4-W1: the separated expansions of the approximants at an operative member (`SepFam`), and `SepFamFam` with `Bounded`

At an operative member `pstar` of a state `A` (operation preconditions), the index `b` of the bundle (`bsA ∪ bsB`) carries the
approximants `zpQfam κ A b`, `zpTfam κ A b` (P1).  Following the plan of P4 session 3 (HANDOFF "Remaining work", W1):

* **(i) roots `≤ L₄`** (an object with root layer `≤ L₄`): the gate at `(L₄, L₂)` — natively, or through `ZpSurj.carrier` for a II-b
  state with both roots `≤ L₄` (`zp_coh_lowC/T`) — with the clamped factor `clampJ L₄` (constant `J(L₄+1, ·)` above `L₄ + 1`: the trace
  window, TARGET L1913-L1919);
* **(ii) root `> L₄`**: the native gate at `(Lₕ, L₂)`, `Lₕ > L₄` (`zp_high_C/T`); below the root layer the object vanishes and the factor
  `clampJ Lₕ` is `0` there (the empty expansion at the `L₄` window);
* `PtOK := True`: by the fallback of `ObjExp.term`, the expansion identity holds at every point; the terms are separated terms on the
  identity sets `VC`, `VT`.

Exports: `GateEnv` (the analytic inputs), `certC`, `certT` (`ObjCert` of every index, with `SepT` certificates on the windows
`timeBox L₄ L₂`, `timeBox Lₕ L₂` (couples) and `timeBoxGt` (trees), constants `certCJ`, `certCM`), `sepFamOf`, **`sffOf`**
(`SepFamFam`), **`sffOf_bounded`** (`SepFamFam.Bounded`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W13
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine TTree WaveTurbulence.Twist
  WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj
  WaveTurbulence.Stage1 WaveTurbulence.ConjCoh WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS

set_option linter.unusedSectionVars false

/-- The analytic inputs of the gate expansions: the coherent gate (`CoherentGateH`, named input of V5), the profile bound of the
layer family `κ.F`, and the parameter facts. -/
structure GateEnv (P : WTParams) (κ : KPar P.d) (p : ℕ) (Bh : ℕ → ℝ) : Prop where
  hg : CoherentGateH P
  hB : ProfileBound P κ.F Bh p
  hp : p < P.D
  hδ : κ.δ = P.δ
  hθ : 0 ≤ 1 - P.η
  hη : P.η ≤ 1
  hC : 1 ≤ P.C₁

theorem window_case (q w : ℕ) : w = q ∨ q + 1 ≤ w ∨ w + 1 ≤ q := by omega

/-- Half the size of a regular code. -/
theorem size_half_cpl (Q : RegCpl) : Q.size = 2 * (Q.size / 2) := (Nat.two_mul_div_two_of_even (regCpl_size_even Q)).symm

theorem size_half_chain (X : RegChain) : X.size = 2 * (X.size / 2) :=
  (Nat.two_mul_div_two_of_even (regChain_size_even X)).symm

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

/-- The couple windows. -/
noncomputable def winCl (A : FamilyReconstruction w ι) (pstar : ι) : Set (Fin 2 → ℝ) := timeBox (zpQ4 A pstar : ℝ) (zpQ2 A pstar)
noncomputable def winCh (A : FamilyReconstruction w ι) (pstar : ι) : Set (Fin 2 → ℝ) := timeBox (zpQh A pstar : ℝ) (zpQ2 A pstar)
/-- The tree windows. -/
noncomputable def winTl (A : FamilyReconstruction w ι) (pstar : ι) : Set (Fin 2 → ℝ) := timeBoxGt (zpQ4 A pstar : ℝ) (zpQ2 A pstar)
noncomputable def winTh (A : FamilyReconstruction w ι) (pstar : ι) : Set (Fin 2 → ℝ) := timeBoxGt (zpQh A pstar : ℝ) (zpQ2 A pstar)
/-- The cell corners of the windows. -/
noncomputable def cornL (A : FamilyReconstruction w ι) (pstar : ι) : Fin 2 → ℝ := ![(zpQ4 A pstar : ℝ), zpQ2 A pstar]
noncomputable def cornH (A : FamilyReconstruction w ι) (pstar : ι) : Fin 2 → ℝ := ![(zpQh A pstar : ℝ), zpQ2 A pstar]

include hcan hel htc hcc in
theorem L2_le_L4R : (zpQ2 A pstar : ℝ) ≤ zpQ4 A pstar := by exact_mod_cast zpQ2_le_zpQ4 A hcan hel htc hcc

include hcan hel htc hcc in
theorem L2_le_LhR : (zpQ2 A pstar : ℝ) ≤ zpQh A pstar := by
  exact_mod_cast (zpQ2_le_zpQ4 A hcan hel htc hcc).trans (zpQ4_le_zpQh A hcan hel htc hcc)

include hcan hel htc hcc in
/-- `n` of a carrier-side couple is at most `zpN A`. -/
theorem nC_le (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) :
    (zpCodeC b.1 pstar).size / 2 ≤ zpN A pstar := by
  have := zp_sizes A sp0 hA hcan hel htc hcc b hb
  omega

include hcan hel htc hcc in
theorem nT_le (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) :
    (zpCodeT b.1 pstar).size / 2 ≤ zpN A pstar := by
  have := zp_sizes A sp0 hA hcan hel htc hcc b hb
  omega

include hcan hel htc hcc E hN in
/-- The certified couple expansion at a gate level `q ∈ {L₄, Lₕ}`. -/
noncomputable def certC_at (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar)) :
    ObjCert P (30 * P.d) (zpQfam κ A b) (winCl A pstar) (winCh A pstar) (cornL A pstar) (cornH A pstar) :=
  have hL24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have hhp := zpQh_le_p A hcan hel htc hcc
  have hL2q : zpQ2 A pstar ≤ q := by rcases hq with rfl | rfl <;> omega
  have hqp : q ≤ p := by rcases hq with rfl | rfl <;> omega
  have hn : (zpCodeC b.1 pstar).size / 2 ≤ P.N (p + 1) ^ 4 := (nC_le A sp0 hA hcan hel htc hcc b hb).trans hN
  let G := ContExp.gateC (h := κ.F) E.hg E.hB E.hp E.hθ hn hL2q hqp (size_half_cpl _) hcoh
  have hcost : 0 ≤ layerCost Bh (zpObjC b.1 pstar) :=
    layerCost_nonneg _ fun x => (E.hB _ (coherentCouple_layer_le hL2q hqp hcoh x)).1
  W2.K2.ofContW G (fun i => W2.K2.clampSel (q ≤ cplRootLayer (zpObjC b.1 pstar)) (q : ℝ) (G.J i)) (zpQfam κ A b)
    (VC q (zpQ4 A pstar) (zpLq b) (zpQ2 A pstar))
    (fun t s hts k =>
      ((zpQ_expand κ A b (zpQ4 A pstar) hL24 hL2q hqp hcoh (P.δ ^ ((zpCodeC b.1 pstar).size / 2)) G.J G.M
        (fun ts hts k => by rw [E.hδ, G.hexp ts hts k]; push_cast; rfl)) t s hts k).trans
      (W2.K2.sum_clampSel_eq _ _ _ _ t s k (fun hfl htq => by
        obtain ⟨⟨hs1, hs2⟩, hc⟩ := hts
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs2 hc htq
        rcases hc with hc | ⟨h4, -, -⟩
        · exact absurd hc (not_lt.2 htq.le)
        · have hgt : zpQ2 A pstar < q := by
            have : (zpQ2 A pstar : ℝ) < q :=
              lt_of_le_of_lt (by exact_mod_cast hL24) (lt_trans h4 htq)
            exact_mod_cast this
          exact W2.K2.couple_gate_vanish G hL2q hqp hcoh hgt hfl hs1 hs2 k)).symm)
    (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)
    (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _) E.hC E.hη hcost
    (fun i => W2.K2.clampSel_bound_C E.hθ E.hη hL2q (window_case _ _) (G.hJc i)
      (by have := E.hC; positivity) (G.hJ i))
    (fun i => W2.K2.clampSel_bound_C E.hθ E.hη hL2q (window_case _ _) (G.hJc i)
      (by have := E.hC; positivity) (G.hJ i))

include hcan hel htc hcc E hN in
/-- The certified tree expansion at a gate level `q ∈ {L₄, Lₕ}`. -/
noncomputable def certT_at (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar)) :
    ObjCert P 0 (zpTfam κ A b) (winTl A pstar) (winTh A pstar) (cornL A pstar) (cornH A pstar) :=
  have hL24 := zpQ2_le_zpQ4 A hcan hel htc hcc
  have h4h := zpQ4_le_zpQh A hcan hel htc hcc
  have hhp := zpQh_le_p A hcan hel htc hcc
  have hL2q : zpQ2 A pstar ≤ q := by rcases hq with rfl | rfl <;> omega
  have hqp : q ≤ p := by rcases hq with rfl | rfl <;> omega
  have hn : (zpCodeT b.1 pstar).size / 2 ≤ P.N (p + 1) ^ 4 := (nT_le A sp0 hA hcan hel htc hcc b hb).trans hN
  let G := ContExp.gateT (h := κ.F) E.hg E.hB E.hp E.hθ hn hL2q hqp (size_half_chain _) hcoh
  have hcost : 0 ≤ layerCost Bh (zpObjT b.1 pstar) :=
    layerCost_nonneg _ fun x => (E.hB _ ((coherentTree_layer_le hL2q hcoh x).trans hqp)).1
  W2.K2.ofContW G (fun i => W2.K2.clampSel (q ≤ treeRootLayer (zpObjT b.1 pstar)) (q : ℝ) (G.J i)) (zpTfam κ A b)
    (VT q (zpQ4 A pstar) (zpLt b) (zpQ2 A pstar))
    (fun t s hts k =>
      ((zpT_expand κ A b (zpQ4 A pstar) hL24 hL2q hcoh (P.δ ^ ((zpCodeT b.1 pstar).size / 2)) G.J G.M
        (fun ts hts k => by rw [E.hδ, G.hexp ts hts k]; push_cast; rfl)) t s hts k).trans
      (W2.K2.sum_clampSel_eq _ _ _ _ t s k (fun hfl htq => by
        obtain ⟨⟨hs1, hs2⟩, hc⟩ := hts
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hs1 hs2 hc htq
        rcases hc with ⟨hc, -⟩ | ⟨h4, -, -⟩
        · exact absurd hc (not_lt.2 htq.le)
        · have hgt : zpQ2 A pstar < q := by
            have : (zpQ2 A pstar : ℝ) < q :=
              lt_of_le_of_lt (by exact_mod_cast hL24) (lt_trans h4 htq)
            exact_mod_cast this
          exact W2.K2.tree_gate_vanish G hL2q hcoh hgt hfl hs1 hs2 k)).symm)
    (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_L4R A hcan hel htc hcc))
    (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_LhR A hcan hel htc hcc)) E.hC E.hη hcost
    (fun i => W2.K2.clampSel_bound_T E.hθ E.hη hL2q hL24 (window_case _ _) (G.hJc i)
      (by have := E.hC; positivity) (G.hJ i))
    (fun i => W2.K2.clampSel_bound_T E.hθ E.hη hL2q (hL24.trans h4h) (window_case _ _) (G.hJc i)
      (by have := E.hC; positivity) (G.hJ i))

include hcan hel htc hcc E hN in
open Classical in
/-- **The certified couple expansion of every index** (trivial off `bsA ∪ bsB`). -/
noncomputable def certC (b : ST w ι pstar J) :
    ObjCert P (30 * P.d) (zpQfam κ A b) (winCl A pstar) (winCh A pstar) (cornL A pstar) (cornH A pstar) :=
  if hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA then
    if hr : cplRootLayer (zpObjC b.1 pstar) ≤ zpQ4 A pstar then
      certC_at A sp0 hA hcan hel htc hcc E hN b (mem_zpFinset_of_bs A sp0 hA hb) (zpQ4 A pstar) (Or.inl rfl)
        (zp_coh_lowC A sp0 hA hcan hel htc hcc hb hr)
    else
      certC_at A sp0 hA hcan hel htc hcc E hN b (mem_zpFinset_of_bs A sp0 hA hb) (zpQQ b.1 pstar).1
        (Or.inr (zp_high_C A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb) (not_le.1 hr)))
        (nat_cohC A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb))
  else ObjCert.triv _ (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)
    (timeBox_subset_cell _ _) (timeBox_subset_closure_interior _ _)

include hcan hel htc hcc E hN in
open Classical in
/-- **The certified tree expansion of every index** (trivial off `bsA ∪ bsB`). -/
noncomputable def certT (b : ST w ι pstar J) :
    ObjCert P 0 (zpTfam κ A b) (winTl A pstar) (winTh A pstar) (cornL A pstar) (cornH A pstar) :=
  if hb : b ∈ bsA p kind J A sp0 hA ∨ b ∈ bsB p kind J A sp0 hA then
    if hr : treeRootLayer (zpObjT b.1 pstar) ≤ zpQ4 A pstar then
      certT_at A sp0 hA hcan hel htc hcc E hN b (mem_zpFinset_of_bs A sp0 hA hb) (zpQ4 A pstar) (Or.inl rfl)
        (zp_coh_lowT A sp0 hA hcan hel htc hcc hb hr)
    else
      certT_at A sp0 hA hcan hel htc hcc E hN b (mem_zpFinset_of_bs A sp0 hA hb) (zpBranchQ b.1 pstar).1
        (Or.inr (zp_high_T A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb) (not_le.1 hr)))
        (nat_cohT A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb))
  else ObjCert.triv _ (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_L4R A hcan hel htc hcc))
    (timeBoxGt_subset_cell _ _) (timeBoxGt_subset_closure_interior (L2_le_LhR A hcan hel htc hcc))

include hcan hel htc hcc E hN in
/-- **The separated expansions of a level** (`P4.SepFam`), with `PtOK := True`. -/
noncomputable def sepFamOf : SepFam p kind J κ A sp0 hA where
  S := ⟨fun b => (certC A sp0 hA hcan hel htc hcc E hN b).m, fun b => (certT A sp0 hA hcan hel htc hcc E hN b).m,
    fun b => (certC A sp0 hA hcan hel htc hcc E hN b).term, fun b => (certT A sp0 hA hcan hel htc hcc E hN b).term⟩
  PtOK _ _ _ := True
  hQ _ s1 t1 _ b _ := ⟨fun k => (certC A sp0 hA hcan hel htc hcc E hN b).sum_term s1 _ k,
    fun k => (certC A sp0 hA hcan hel htc hcc E hN b).sum_term t1 _ k⟩
  hT _ s1 t1 _ b _ := ⟨fun k => (certT A sp0 hA hcan hel htc hcc E hN b).sum_term s1 _ k,
    fun k => (certT A sp0 hA hcan hel htc hcc E hN b).sum_term t1 _ k⟩
  dom _ _ _ _ _ := trivial

include hcan hel htc hcc E hN in
theorem certC_at_m_le (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentCoupleAt p q (zpQ2 A pstar) (zpCodeC b.1 pstar) (zpObjC b.1 pstar)) :
    (certC_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).m ≤ 2 ^ ((zpCodeC b.1 pstar).size / 2) := by
  unfold certC_at
  exact max_le (ContExp.hm _) Nat.one_le_two_pow

include hcan hel htc hcc E hN in
theorem certT_at_m_le (b : ST w ι pstar J) (hb : b ∈ zpFinset p kind pstar J A sp0 hA) (q : ℕ)
    (hq : q = zpQ4 A pstar ∨ q = zpQh A pstar)
    (hcoh : IsCoherentTreeAt p q (zpQ2 A pstar) (zpCodeT b.1 pstar) (zpObjT b.1 pstar)) :
    (certT_at (κ := κ) A sp0 hA hcan hel htc hcc E hN b hb q hq hcoh).m ≤ 2 ^ ((zpCodeT b.1 pstar).size / 2) := by
  unfold certT_at
  exact max_le (ContExp.hm _) Nat.one_le_two_pow

include hcan hel htc hcc E hN in
theorem certC_m_le (b : ST w ι pstar J) : (certC A sp0 hA hcan hel htc hcc E hN b).m ≤ 2 ^ zpN A pstar := by
  classical
  unfold certC
  split_ifs with hb hr
  · exact (certC_at_m_le A sp0 hA hcan hel htc hcc E hN _ _ _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (nC_le A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb)))
  · exact (certC_at_m_le A sp0 hA hcan hel htc hcc E hN _ _ _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (nC_le A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb)))
  · exact Nat.one_le_two_pow

include hcan hel htc hcc E hN in
theorem certT_m_le (b : ST w ι pstar J) : (certT A sp0 hA hcan hel htc hcc E hN b).m ≤ 2 ^ zpN A pstar := by
  classical
  unfold certT
  split_ifs with hb hr
  · exact (certT_at_m_le A sp0 hA hcan hel htc hcc E hN _ _ _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (nT_le A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb)))
  · exact (certT_at_m_le A sp0 hA hcan hel htc hcc E hN _ _ _ _ _).trans
      (Nat.pow_le_pow_right (by norm_num) (nT_le A sp0 hA hcan hel htc hcc b (mem_zpFinset_of_bs A sp0 hA hb)))
  · exact Nat.one_le_two_pow

end WaveTurbulence.VineEstS5C.P4.W13
