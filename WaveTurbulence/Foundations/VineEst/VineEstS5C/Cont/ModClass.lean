/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.ModCore
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Class

/-! # V5-CONT (R58), members and class for the modulated kernel

`twistedRecenteredModC`: `e^{-πiδL^{2γ}t₀Γ} Σ_{G'} K^U_{(G'),λ}` with `K^U_λ = clLocalKernelModC` (the R58 definition:
the factor `e^{πiλτ_b}` in the time integrand of each member, `b` the lower joint of its region).  `λ = 0` is `twistedRecentered`
(`twistedRecenteredModC_zero`).  `twistedRecenteredModC_continuousOn`: continuity on the closed cube, as for `λ = 0`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
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

/-- (vineest1) with the modulation (R58). -/
noncomputable def twistedRecenteredModC {d : ℕ} (G : Garden w) (a : GBranch G.tree)
    (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family))
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (lam : ℝ) (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * tUpper * boundaryEnergyFromMomenta (G.sign a.toNode) e f g h : ℝ) : ℂ) *
    Complex.I) *
    ∑ x ∈ Z, clLocalKernelModC x.1.data x.1.plain (clRegionData x.1.skeleton x.2.block x.2.cl) L γ δ F
      (stateLayer x.1) (stateLayer_isLayering x.1) base lam tUpper tPositive tNegative e f g h

/-- The modulated recentered class sum is the sum of the modulated recentered kernels of the members. -/
theorem recentered_class_sumMod {d p : ℕ} (lam : ℝ) {kind : Bool} {A : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family}
    (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family))
    (hZ : ∀ x ∈ Z, ∃ M : List ι, Reach p kind M A c x.1 x.2)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    twistedRecenteredModC A.skeleton c.a Z L γ δ F base lam t0 t1 t2 e f g k =
      ∑ x ∈ Z, clRecenteredLocalKernelModC x.1.data x.1.plain (clRegionData x.1.skeleton x.2.block x.2.cl) L γ δ F
        (stateLayer x.1) (stateLayer_isLayering x.1) base lam t0 t1 t2 e f g k := by
  unfold twistedRecenteredModC
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨M, hM⟩ := hZ x hx
  unfold clRecenteredLocalKernelModC
  rw [hM.sign_a]

/-- **V5-CONT, one member.**  See the module docstring. -/
theorem memberMod_continuousOn {P : WTParams} (lam : ℝ)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {kind : Bool} {M : List ι} {A Bs : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt Bs.skeleton Bs.family} (hr : Reach p kind M A c Bs c') {n : ℕ}
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
      (step3W hM9 B0 A.data A.plain lA hLA bk0 q0 centre wBar) P.L P.γ P.δ h p) :
    ∀ E ∈ outSet (step3D hM9 B0 A.data A.plain lA hLA bk0 q0 centre wBar)
        P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => clRecenteredLocalKernelModC (rowSel := VineEst.RowSel.plain) Bs.data Bs.plain
          (clRegionData Bs.skeleton c'.block c'.cl) P.L P.γ P.δ h (stateLayer Bs) (stateLayer_isLayering Bs) wBar lam
          (tt 0) (tt 1) (tt 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 1) (sumintBoundary (A.skeleton.sign c.a.toNode) E 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 3))
        (cubeSet q0) := by
  classical
  subst hlA
  obtain rfl := regionData_subsingleton R0 (clRegionData A.skeleton c.block c.cl)
  obtain ⟨e, B1, hc, ha, hb, hU, hl⟩ := hr.exists_asm B0
  have hlayB : ∀ x, stateLayer Bs x ≤ p := reach_stateLayer_le hr hAlay
  have hI1 := assemblyShape_I_pos hM9 B1
  set bk1 : Fin (assemblyShape hM9 B1).I → Fin 4 := canonBadKind hM9 B1 Bs.data Bs.plain (stateLayer Bs) with hbk1
  have hbad2 : ∀ i, bk1 i ≠ 2 := fun i => by
    rcases canonBadKind_cases hM9 B1 Bs.data Bs.plain (stateLayer Bs) i with h0 | h0 <;> rw [hbk1, h0] <;> decide
  have hq1 : q0 0 = stateLayer Bs (Bs.data.coreBranch Bs.plain c'.a).toNode := by
    rw [hq0, ← ha]
    exact (hl c.a).symm
  have hrc := hr.rowCoherent hM9 B0 B1 bk0 q0 bk1 q0 centre wBar hq0 hq1 P.L P.γ P.δ h H
  have hsz : RowSizes hM9 B1 Bs.data Bs.plain (P.N (p + 1) ^ 4) :=
    rowSizes_of_state hM9 Bs B1 (by rw [hr.order_eq]; exact hAord)
  have hel := fun v => eligible_of hM9 B1 Bs.data Bs.plain (stateLayer Bs) (stateLayer_isLayering Bs)
    (step3W hM9 B1 Bs.data Bs.plain (stateLayer Bs) (stateLayer_isLayering Bs) bk1 q0 centre wBar) rfl hq1 P.L P.γ P.δ
    h (P.N (p + 1) ^ 4) p hlayB hsz hrc v
  have hfirst : assemblyTimeQ hM9 B1 (fun v => stateLayer Bs (Bs.data.coreBranch Bs.plain v).toNode)
        (.inl ⟨⟨0, hI1⟩, 0⟩) =
      assemblyTimeQ hM9 B0 (fun v => stateLayer A (A.data.coreBranch A.plain v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B0⟩, 0⟩) := by
    rw [assemblyTimeQ_first hM9 B1 Bs.data Bs.plain (stateLayer Bs) hI1,
      assemblyTimeQ_first hM9 B0 A.data A.plain (stateLayer A) (assemblyShape_I_pos hM9 B0)]
    have := hl c.b
    rw [hb] at this
    exact_mod_cast this
  have key := clRecenteredMod_continuousOn lam hgate hinc hd hη0 hη6 hη2 hC hδ hL hw hp hB hBpos hM9 B1 Bs.data Bs.plain
    (stateLayer Bs) (stateLayer_isLayering Bs) hlayB q0 centre wBar bk1 hbad2 hel
    (Or.inr (hfirst ▸ hqle1)) (Or.inr (hfirst ▸ hqle2))
  intro E hE
  have hsign : Bs.skeleton.sign c'.a.toNode = A.skeleton.sign c.a.toNode := hr.sign_a
  have := key E hE
  rw [hsign] at this
  exact this

/-- **V5-CONT, class level, generic in the member set** (every member reached by a batch of kind `kind`). -/
theorem classSumMod_continuousOn {P : WTParams} (lam : ℝ)
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
      ContinuousOn (fun tt : Fin 3 → ℝ => twistedRecenteredModC (rowSel := VineEst.RowSel.plain) A.skeleton c.a Z P.L P.γ P.δ h wBar lam
          (tt 0) (tt 1) (tt 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 1) (sumintBoundary (A.skeleton.sign c.a.toNode) E 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 3)) (cubeSet q0) := by
  intro E hE
  have hsum : (fun tt : Fin 3 → ℝ => twistedRecenteredModC A.skeleton c.a Z P.L P.γ P.δ h wBar lam
          (tt 0) (tt 1) (tt 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 1) (sumintBoundary (A.skeleton.sign c.a.toNode) E 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 3)) =
      fun tt => ∑ x ∈ Z, clRecenteredLocalKernelModC x.1.data x.1.plain (clRegionData x.1.skeleton x.2.block x.2.cl)
        P.L P.γ P.δ h (stateLayer x.1) (stateLayer_isLayering x.1) wBar lam (tt 0) (tt 1) (tt 2)
        (sumintBoundary (A.skeleton.sign c.a.toNode) E 0) (sumintBoundary (A.skeleton.sign c.a.toNode) E 1)
        (sumintBoundary (A.skeleton.sign c.a.toNode) E 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 3) :=
    funext fun tt => recentered_class_sumMod lam Z hZ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hsum]
  exact continuousOn_finsetSum _ fun x hx => by
    obtain ⟨M, hM⟩ := hZ x hx
    exact memberMod_continuousOn lam hgate hinc hd hη0 hη6 hη2 hC hδ hL hw hp hB hBpos hM hM9 B0 lA hLA hlA hAlay hAord
      bk0 q0 centre wBar hq0 hqle1 hqle2 H E hE

/-- **V5-CONT export (kind = true).**  The recentered twisted class kernel of `VineEstCanonLayerC2` is continuous in
`(t₀,t₁,t₂)` on the closed cube `cubeSet (step3D …).qOut`, for every `E` of `outSet (step3D …)`.  The hypotheses besides the
data of `VineEstCanonLayerC2` are the gates and the profile bound for `h`. -/
theorem twistedRecenteredModC_continuousOn {P : WTParams} (lam : ℝ)
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
      ContinuousOn (fun tt : Fin 3 → ℝ => twistedRecenteredModC (rowSel := VineEst.RowSel.plain) G a
          (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B)) P.L P.γ P.δ h wBar lam
          (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3))
        (cubeSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R)
          centre wBar).qOut) := by
  have hZ : ∀ x ∈ canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B),
      ∃ M : List _, Reach p kind M (startState B RD hG layer hLayer) (chainStart B) x.1 x.2 := fun x hx => by
    obtain ⟨M, _, hM⟩ := (mem_canonFinset hprime).1 hx
    exact ⟨M, hM⟩
  have hI := assemblyShape_I_pos hM9 B
  exact classSumMod_continuousOn lam (A := startState B RD hG layer hLayer) (c := chainStart B) hgate hinc hd hη0 hη6 hη2 hC
    hδ hL hw hp hB hBpos hM9 B layer hLayer (stateLayer_start B RD hG layer hLayer) hlay hord
    (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar rfl
    (qOutOf_one_le hM9 B RD hG layer hLayer hI) (qOutOf_two_le hM9 B RD hG layer hLayer hI)
    H _ hZ

end WaveTurbulence.VineEstS5C.Cont
