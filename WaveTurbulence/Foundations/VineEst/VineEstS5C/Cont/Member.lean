/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.Cont.Core
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowReach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowOrder
public import WaveTurbulence.Foundations.VineEst.VineEstS4.TwistedKernelForm
public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyReach

/-! # V5-CONT, members: continuity of the recentered kernel of a reached state

`reach_stateLayer_le`: the layers of a reached state are at most `p` (start: hypothesis; reached: the state is canonical, so
`CanonCriterion p`).  `member_continuousOn`: for a state `Bs` reached from `(A, c)` by a batch (any `kind`), the recentered
kernel `clRecenteredLocalKernel` of `Bs` at its region is continuous in `(t₀,t₁,t₂)` on the closed cube `cubeSet q₀`, for
every `E` of the output set of the START datum.  The cube and the output set are those of the start: the datum of the member
is `step3W` of the iterated twist `B1` of the start assembly (`Reach.exists_asm`) with the SAME output indices `q₀`
(their compatibility with the member needs only `hqo`: `q₀ 0` is the layer of `a`, and the leaf-child time condition, both
preserved by the batch through `atomLayer`), and the row eligibility of the member is carried from the start
(`Reach.rowCoherent`, `Reach.order_eq`).  Everything here is independent of `kind`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C.Cont
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng WaveTurbulence.VineEstS4
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed
  MeasureTheory
open scoped ENNReal

variable {w : ℕ} {ι : Type*}

/-- The layers `layer`-function of a state is bounded iff the layers of its layered garden are. -/
theorem stateLayer_le_of_layered {p : ℕ} (Bs : FamilyReconstruction w ι) (h : ∀ x, Bs.layered.layer x ≤ p) :
    ∀ x, stateLayer Bs x ≤ p := by
  have key : ∀ X : LayeredGarden w,
      layeredReconstruction Bs.data Bs.plain (stateLayer Bs) (stateLayer_isLayering Bs) = X →
      (∀ x, X.layer x ≤ p) → ∀ x, stateLayer Bs x ≤ p := by
    intro X hX hx
    subst hX
    exact hx
  exact key Bs.layered (stateLayer_spec Bs) h

/-- The layers of every state reached from the start are `≤ p` (the reached state is canonical or is the start). -/
theorem reach_stateLayer_le {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c')
    (hA : ∀ x, stateLayer A x ≤ p) : ∀ x, stateLayer B x ≤ p := by
  rcases h.canonical_or_eq with ⟨hB, _⟩ | hcan
  · subst hB
    exact hA
  · exact stateLayer_le_of_layered B hcan.criterion.1

/-- **V5-CONT, one member.**  See the module docstring. -/
theorem member_continuousOn {P : WTParams}
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
      ContinuousOn (fun tt : Fin 3 → ℝ => clRecenteredLocalKernel (rowSel := VineEst.RowSel.plain) Bs.data Bs.plain
          (clRegionData Bs.skeleton c'.block c'.cl) P.L P.γ P.δ h (stateLayer Bs) (stateLayer_isLayering Bs) wBar
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
  have key := clRecentered_continuousOn hgate hinc hd hη0 hη6 hη2 hC hδ hL hw hp hB hBpos hM9 B1 Bs.data Bs.plain
    (stateLayer Bs) (stateLayer_isLayering Bs) hlayB q0 centre wBar bk1 hbad2 hel
    (Or.inr (hfirst ▸ hqle1)) (Or.inr (hfirst ▸ hqle2))
  intro E hE
  have hsign : Bs.skeleton.sign c'.a.toNode = A.skeleton.sign c.a.toNode := hr.sign_a
  have := key E hE
  rw [hsign] at this
  exact this

end WaveTurbulence.VineEstS5C.Cont
