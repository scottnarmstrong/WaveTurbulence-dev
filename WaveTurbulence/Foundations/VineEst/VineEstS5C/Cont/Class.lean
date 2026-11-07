/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Member
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Canon
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement

/-! # V5-CONT, the class kernel: `twistedRecentered` is continuous in the three clocks

`recentered_class_sum`: for a finite set `Z` of members each reached from `(A, c)` by a batch, `twistedRecentered G a Z` is the
sum of the recentered kernels `clRecenteredLocalKernel` of the members (all at the boundary `sumintBoundary` of the START sign).
`twistedRecentered_continuousOn`: for the canonical class `canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)`
(the only place where `kind = true` enters: `mem_canonFinset`; every other step is `member_continuousOn`, generic in `kind`),
`twistedRecentered` is continuous on `cubeSet (step3D …).qOut` for every `E` of `outSet (step3D …)`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.Cont
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
  MeasureTheory
open scoped ENNReal

variable {w : ℕ} {ι : Type*}

/-- The layering of the start state is the given layering (copy of `P4.stateLayer_startState`, without the P4 import). -/
theorem stateLayer_start {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) :
    stateLayer (startState B RD hG layer hLayer) = layer :=
  layeredReconstruction_inj RD hG (l₁ := stateLayer (startState B RD hG layer hLayer)) (l₂ := layer)
    (h₁ := stateLayer_isLayering (startState B RD hG layer hLayer)) (h₂ := hLayer)
    (stateLayer_spec (startState B RD hG layer hLayer))

/-- The recentered class sum is the sum of the recentered kernels of the members. -/
theorem recentered_class_sum {d p : ℕ} {kind : Bool} {A : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family}
    (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family))
    (hZ : ∀ x ∈ Z, ∃ M : List ι, Reach p kind M A c x.1 x.2)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    twistedRecentered A.skeleton c.a Z L γ δ F base t0 t1 t2 e f g k =
      ∑ x ∈ Z, clRecenteredLocalKernel x.1.data x.1.plain (clRegionData x.1.skeleton x.2.block x.2.cl) L γ δ F
        (stateLayer x.1) (stateLayer_isLayering x.1) base t0 t1 t2 e f g k := by
  unfold twistedRecentered
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨M, hM⟩ := hZ x hx
  exact recentered_twisted hM L γ δ F base t0 t1 t2 e f g k

/-- **V5-CONT, class level, generic in the member set** (every member reached by a batch of kind `kind`). -/
theorem classSum_continuousOn {P : WTParams}
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {kind : Bool} {A : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family} {n : ℕ}
    {R0 : CLRegionData A.skeleton c.U c.a c.b} (hM9 : VINEPARAM) (B0 : CLChainAssembly A.skeleton R0 n)
    (lA : GNode (A.data.forest A.plain) → ℕ) (hLA : IsLayering (A.data.garden A.plain) lA) (hlA : stateLayer A = lA)
    (hAlay : ∀ x, lA x ≤ p) (hAord : A.layered.garden.order ≤ P.N (p + 1) ^ 4)
    (bk0 : Fin (assemblyShape hM9 B0).I → Fin 4) (q0 : Fin 3 → ℕ) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (hq0 : q0 0 = lA (A.data.coreBranch A.plain c.a).toNode)
    (hqle1 : (q0 1 : ℝ) ≤ assemblyTimeQ hM9 B0 (fun v => lA (A.data.coreBranch A.plain v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B0⟩, 0⟩))
    (hqle2 : (q0 2 : ℝ) ≤ assemblyTimeQ hM9 B0 (fun v => lA (A.data.coreBranch A.plain v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B0⟩, 0⟩))
    (H : RowCoherent hM9 B0 A.data A.plain lA hLA
      (step3W hM9 B0 A.data A.plain lA hLA bk0 q0 centre wBar) P.L P.γ P.δ h p)
    (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family))
    (hZ : ∀ x ∈ Z, ∃ M : List ι, Reach p kind M A c x.1 x.2) :
    ∀ E ∈ outSet (step3D hM9 B0 A.data A.plain lA hLA bk0 q0 centre wBar) P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => twistedRecentered A.skeleton c.a Z P.L P.γ P.δ h wBar
          (tt 0) (tt 1) (tt 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 1) (sumintBoundary (A.skeleton.sign c.a.toNode) E 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 3)) (cubeSet q0) := by
  intro E hE
  have hsum : (fun tt : Fin 3 → ℝ => twistedRecentered A.skeleton c.a Z P.L P.γ P.δ h wBar
          (tt 0) (tt 1) (tt 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 1) (sumintBoundary (A.skeleton.sign c.a.toNode) E 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 3)) =
      fun tt => ∑ x ∈ Z, clRecenteredLocalKernel x.1.data x.1.plain (clRegionData x.1.skeleton x.2.block x.2.cl)
        P.L P.γ P.δ h (stateLayer x.1) (stateLayer_isLayering x.1) wBar (tt 0) (tt 1) (tt 2)
        (sumintBoundary (A.skeleton.sign c.a.toNode) E 0) (sumintBoundary (A.skeleton.sign c.a.toNode) E 1)
        (sumintBoundary (A.skeleton.sign c.a.toNode) E 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 3) :=
    funext fun tt => recentered_class_sum Z hZ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hsum]
  exact continuousOn_finsetSum _ fun x hx => by
    obtain ⟨M, hM⟩ := hZ x hx
    exact member_continuousOn hgate hinc hd hη0 hη6 hη2 hC hδ hL hw hp hB hBpos hM hM9 B0 lA hLA hlA hAlay hAord
      bk0 q0 centre wBar hq0 hqle1 hqle2 H E hE

/-- **V5-CONT export (kind = true).**  The recentered twisted class kernel of `VineEstCanonLayerC2` is continuous in
`(t₀,t₁,t₂)` on the closed cube `cubeSet (step3D …).qOut`, for every `E` of `outSet (step3D …)`.  The hypotheses besides the
data of `VineEstCanonLayerC2` are the gates and the profile bound for `h`. -/
theorem twistedRecentered_continuousOn {P : WTParams}
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hlay : ∀ x, layer x ≤ p) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (H : RowCoherent hM9 B RD hG layer hLayer
      (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p) :
    ∀ E ∈ outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
        P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => twistedRecentered G a
          (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)) P.L P.γ P.δ h wBar
          (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3))
        (cubeSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R)
          centre wBar).qOut) := by
  have hZ : ∀ x ∈ canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B),
      ∃ M : List _, Reach p kind M (startState B RD hG layer hLayer) (chainStart B) x.1 x.2 := fun x hx => by
    obtain ⟨M, _, hM⟩ := (mem_canonFinset hprime).1 hx
    exact ⟨M, hM⟩
  have hI := assemblyShape_I_pos hM9 B
  exact classSum_continuousOn (A := startState B RD hG layer hLayer) (c := chainStart B) hgate hinc hd hη0 hη6 hη2 hC
    hδ hL hw hp hB hBpos hM9 B layer hLayer (stateLayer_start B RD hG layer hLayer) hlay hord
    (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar rfl
    (qOutOf_one_le hM9 B RD hG layer hLayer hI) (qOutOf_two_le hM9 B RD hG layer hLayer hI)
    H _ hZ

end WaveTurbulence.VineEstS5C.Cont
