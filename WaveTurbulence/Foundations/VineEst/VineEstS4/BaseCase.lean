/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Statement
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RowOrder

/-! # Base case: with no twist available, `VineEstFull` is `Step3Statement` (V5 Step 4a)

Under `CoreVinesNoTwist` (TARGET L1841) no core member admits an LF operation, so every batch only skips, the class is
the singleton `{G}`, its only section is the start (state, region), and the twisted kernel at the start is the
single-garden kernel (the CL region data and the layering are unique).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton
  VineParamContract TTree
open scoped ENNReal

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- With the twist assumptions failing at every core member there is no LF operation at the start. -/
theorem startState_noOperation {p : ℕ} {kind : Bool} (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hno : CoreVinesNoTwist B RD hG layer hLayer) (i : (assemblySourceFamily B).CoreIndex) :
    IsEmpty (FamilyOperation (p := p) (kind := kind) (startState B RD hG layer hLayer) i) :=
  ⟨fun op => hno i.1 ((assemblySourceFamily B).corePlacement i) i.2 ((assemblySourceFamily B).corePlacement_at i)
    ⟨op.eligible, op.treeCoherent, op.coupleCoherent⟩⟩

section NoOp
variable {ι : Type*} {p : ℕ} {kind : Bool}

theorem batch_eq_of_noOperation {L : List ι} {A B : FamilyReconstruction w ι}
    (h : FamilyBatch p kind L A B) (hno : ∀ i, IsEmpty (FamilyOperation (p := p) (kind := kind) A i)) : B = A := by
  induction h with
  | nil => rfl
  | skip i h ih => exact ih hno
  | apply op h ih => exact (hno _).elim op

theorem reach_skips {A : FamilyReconstruction w ι} (c : ChainAt A.skeleton A.family) (L : List ι) :
    Reach p kind L A c A c := by
  induction L with
  | nil => exact .nil A c
  | cons i L ih => exact .skip i ih

end NoOp

/-- The start is the only section when no operation is available. -/
theorem classSection_start {p : ℕ} {kind : Bool} (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (hno : CoreVinesNoTwist B RD hG layer hLayer) :
    ClassSectionK p kind (startState B RD hG layer hLayer) (chainStart B)
      {⟨startState B RD hG layer hLayer, chainStart B⟩} := by
  have hno' := startState_noOperation (p := p) (kind := kind) B RD hG layer hLayer hno
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨_, List.Perm.refl _, reach_skips _ _⟩
  · intro x hx y hy _
    rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx hy
    rw [hx, hy]
  · ext LH
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
      subst hx
      exact FamilyReconstruction.mem_outputs _ _
    · rintro ⟨M, B', _, hB, rfl⟩
      refine ⟨⟨startState B RD hG layer hLayer, chainStart B⟩, by simp, ?_⟩
      rw [batch_eq_of_noOperation hB hno']

/-- At the start, the twisted kernel is the single-garden kernel. -/
theorem twistedLocalKernel_start {d : ℕ} (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) :
    twistedLocalKernel (startState B RD hG layer hLayer) (chainStart B) L γ δ F base =
      clLocalKernel RD hG R L γ δ F layer hLayer base := by
  have hl : stateLayer (startState B RD hG layer hLayer) = layer :=
    layeredReconstruction_inj RD hG (l₁ := stateLayer (startState B RD hG layer hLayer)) (l₂ := layer)
      (h₁ := stateLayer_isLayering (startState B RD hG layer hLayer)) (h₂ := hLayer) (stateLayer_spec (startState B RD hG layer hLayer))
  have key : ∀ (R' : CLRegionData G U a b) (l : GNode (RD.forest hG) → ℕ) (hl' : IsLayering (RD.garden hG) l),
      R' = R → l = layer →
      clLocalKernel RD hG R' L γ δ F l hl' base = clLocalKernel RD hG R L γ δ F layer hLayer base := by
    intro R' l hl' h1 h2
    subst h1 h2
    rfl
  exact key _ _ _ (regionData_subsingleton _ _) hl

/-- **TARGET vineest Step 3, no-twist case, with TARGET's standing garden-order bound** (`n ≤ N_{p+1}^4`, L806-L810)
in place of `RowSizes`; `step3Ord_of_step3` derives it from `Step3Statement`. -/
@[expose] def Step3StatementOrd (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ {Rin : ℕ → Mom P.d → ℝ}, (∀ r ≤ p, InputRemainder P (Rin r) r) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer), (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    CoreVinesNoTwist B RD hG layer hLayer →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d),
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ (inputsF P Rin) p →
    XNorm00Restr (2 * P.η ^ 8) (outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => clRecenteredLocalKernel (rowSel := VineEst.RowSel.plain) RD hG R P.L P.γ P.δ (inputsF P Rin) layer hLayer wBar
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7))

theorem step3Ord_of_step3 {P : WTParams} (H : Step3Statement P) : Step3StatementOrd P := by
  intro p hp Rin hR w G U a b R n hM9 B RD hG layer hLayer hlay hord hM hno centre wBar hcoh
  exact H hp hR hM9 B RD hG layer hLayer hlay (rowSizes_of_order hM9 B RD hG hord) hM hno centre wBar hcoh

/-- **Base case.**  `VineEstFull` implies `Step3StatementOrd`: the class of a chain with no twistable core vine is the
single garden `G`, and the sum (vineest1) is the single-garden kernel. -/
theorem step3Ord_of_full {P : WTParams} (hF : VineEstFull P) : Step3StatementOrd P := by
  intro p hp Rin hR w G U a b R n hM9 B RD hG layer hLayer hlay hsz hM hno centre wBar hcoh
  have h := hF hp hR hM9 B RD hG layer hLayer hlay hsz hM centre wBar hcoh true _
    (classSection_start (kind := true) B RD hG layer hLayer hno)
  refine le_of_eq_of_le ?_ h
  congr 1
  funext tt E
  simp only [twistedRecentered, Finset.sum_singleton, twistedLocalKernel_start, clRecenteredLocalKernel]

end WaveTurbulence.VineEstS4
