/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.AssemblyReach
public import WaveTurbulence.Foundations.VineEst.VineEstS4.OrderStep
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Class
public import WaveTurbulence.Foundations.VineEst.VineEstS3.LeafChild

/-! # The twisted kernel in sumint form (V5 Step 4b, P2.2)

* `Reach.sign_a`: the sign of the upper joint is the same at every state of a batch (the unit twist flips only the sign of
  the lower joint, `coreBranchEquiv_sign`, and the lower joint of a member differs from `a`).
* `recentered_twisted`: the factor `e^{-πiδL^{2γ}t_{u1}Γ}` of (vineest1), written with the sign of the START garden, times
  `twistedLocalKernel Bs c` is `clRecenteredLocalKernel` of the state (R31(2): the same recentering exponent).
* `twistedKernel_sumintForm`: V4's identity `vineChain_eq_sumintForm'` applied at the twisted state, with the iterated twist
  `B'` of the chain assembly (`Reach.exists_asm`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3
  WaveTurbulence.RegRed VineParamContract TTree
variable {w : ℕ} {ι : Type*}

theorem sign_step (A : FamilyReconstruction w ι) (c : ChainAt A.skeleton A.family) (i : ι) (ε : Bool) :
    (chosenSkeleton A.skeleton (A.family.placement i) ε).sign (ChainAt.nextA A c i ε).a.toNode =
      A.skeleton.sign c.a.toNode := by
  rw [nextA_a]
  cases ε
  · rfl
  · change (unitTwistGarden A.skeleton (A.family.placement i)).sign
      (coreBranchEquiv A.skeleton (A.family.placement i) c.a).toNode = _
    have hne : c.a ≠ (A.family.placement i).lower := (c.lower_ne i).symm
    rw [coreBranchEquiv_sign]
    simp [hne]

theorem Reach.sign_a {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') :
    B.skeleton.sign c'.a.toNode = A.skeleton.sign c.a.toNode := by
  induction h with
  | nil A c => rfl
  | skip i h ih => exact ih
  | apply op h ih => exact ih.trans (sign_step _ _ _ op.choice)

/-- The recentered factor of (vineest1) (with the sign of the start garden `A`) times the twisted kernel is the
recentered kernel `clRecenteredLocalKernel` of the reached state. -/
theorem recentered_twisted {p : ℕ} {kind : Bool} {M : List ι} {A B : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt B.skeleton B.family} (h : Reach p kind M A c B c') {d : ℕ}
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (t0 t1 t2 : ℝ) (e f g k : Mom d) :
    Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * t0 * boundaryEnergyFromMomenta (A.skeleton.sign c.a.toNode) e f g k : ℝ) : ℂ) *
        Complex.I) * twistedLocalKernel B c' L γ δ F base t0 t1 t2 e f g k =
      clRecenteredLocalKernel B.data B.plain (clRegionData B.skeleton c'.block c'.cl) L γ δ F (stateLayer B)
        (stateLayer_isLayering B) base t0 t1 t2 e f g k := by
  unfold clRecenteredLocalKernel twistedLocalKernel
  rw [h.sign_a]

/-- **P2.2.**  At any state reached from the chain of `B0` by an LF batch, the twisted assembly `B1` (iterated
`CLChainAssembly.twist`, pieces corresponding to those of `B0`) satisfies V4's identity: the recentered twisted kernel is
the `sumint` form of `B1` (the shape of the twisted assembly), with the data `(Bs.data, stateLayer Bs)` of the state. -/
theorem twistedKernel_sumintForm {p : ℕ} {kind : Bool} {M : List ι} {A Bs : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt Bs.skeleton Bs.family} (h : Reach p kind M A c Bs c') {n : ℕ}
    (B0 : CLChainAssembly A.skeleton (clRegionData A.skeleton c.block c.cl) n) (hM9 : VINEPARAM) {d : ℕ} :
    ∃ (e : GBranch A.skeleton.tree ≃ GBranch Bs.skeleton.tree)
      (B1 : CLChainAssembly Bs.skeleton (clRegionData Bs.skeleton c'.block c'.cl) n),
      AsmCorr B0 B1 e ∧ e c.a = c'.a ∧ e c.b = c'.b ∧
      (∀ x, atomLayer Bs.data Bs.plain (stateLayer Bs) (e x) = atomLayer A.data A.plain (stateLayer A) x) ∧
      ∀ (W : SumintWeightClockData (assemblyShape hM9 B1) d)
        (_ : ∀ v, W.param v = 0) (_ : ∀ i, W.badKind i ≠ 2) {L : ℝ} (hL : L ≠ 0) (γ δ η : ℝ) (F : ℕ → Mom d → ℝ)
        (_ : W.q = assemblyTimeQ hM9 B1 (fun v => stateLayer Bs (Bs.data.coreBranch Bs.plain v).toNode))
        (_ : ConstraintsOK hM9 B1 W) (base : Mom d) (β : Fin 4 → (Fin d → ℤ))
        (hβ : ((Bs.skeleton.sign c'.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) (t : Fin 3 → ℝ)
        (_ : (c'.b.child (clRegionData Bs.skeleton c'.block c'.cl).positive).1.2 ∈
            (Bs.skeleton.tree (c'.b.child (clRegionData Bs.skeleton c'.block c'.cl).positive).1.1).branching ∨
          t 1 ≤ assemblyTimeQ hM9 B1 (fun v => stateLayer Bs (Bs.data.coreBranch Bs.plain v).toNode)
            (.inl ⟨⟨0, assemblyShape_I_pos hM9 B1⟩, 0⟩))
        (_ : (c'.b.child (clRegionData Bs.skeleton c'.block c'.cl).negative).1.2 ∈
            (Bs.skeleton.tree (c'.b.child (clRegionData Bs.skeleton c'.block c'.cl).negative).1.1).branching ∨
          t 2 ≤ assemblyTimeQ hM9 B1 (fun v => stateLayer Bs (Bs.data.coreBranch Bs.plain v).toNode)
            (.inl ⟨⟨0, assemblyShape_I_pos hM9 B1⟩, 0⟩)),
        Complex.exp (((-(Real.pi * δ * L ^ (2 * γ)) * t 0 * boundaryEnergyFromMomenta (A.skeleton.sign c.a.toNode)
            (base + latticePoint L (β 0)) (base + latticePoint L (β 1)) (base + latticePoint L (β 2))
            (base + latticePoint L (β 3)) : ℝ) : ℂ) * Complex.I) *
          twistedLocalKernel Bs c' L γ δ F base (t 0) (t 1) (t 2) (base + latticePoint L (β 0))
            (base + latticePoint L (β 1)) (base + latticePoint L (β 2)) (base + latticePoint L (β 3)) =
        (coupling d L γ δ : ℂ) ^ clLocalOrder1 (clRegionData Bs.skeleton c'.block c'.cl) *
          clLocalZeta (clRegionData Bs.skeleton c'.block c'.cl) *
        ∑' x : (assemblyShape hM9 B1).VIdx → (Fin d → ℤ),
          (clRegionalEpsilon Bs.skeleton c'.U
              (clExtendIndices (clRegionData Bs.skeleton c'.block c'.cl)
                ((clNormalizedChainEquiv hL B1 base β hβ hM9).symm x).1) : ℂ) *
          ∫ τ in (sourceSumintDatum hM9 B1 Bs.plain W).timeDom (assemblyShape_I_pos hM9 B1) (t 0) (t 1) (t 2),
            signedPhase (sourceSumintDatum hM9 B1 Bs.plain W)
                (assemblyCoreFirstSign hM9 B1) (assemblyCoreSign hM9 B1) L γ (2 * δ) η x
                (sumintBoundary (Bs.skeleton.sign c'.a.toNode) (fun j => base + latticePoint L (β j)) 0 -
                  sumintBoundary (Bs.skeleton.sign c'.a.toNode) (fun j => base + latticePoint L (β j)) 1) (t 0) τ *
              ∏ v, (assemblyWK hM9 B1 Bs.data Bs.plain L γ δ F (stateLayer Bs) (stateLayer_isLayering Bs) t
                    (assemblyClockEquiv hM9 B1 τ) v
                  ((sourceSumintDatum hM9 B1 Bs.plain W).kVec L x
                    (sumintBoundary (Bs.skeleton.sign c'.a.toNode) (fun j => base + latticePoint L (β j))) v) *
                assemblyWL hM9 B1 Bs.data Bs.plain L γ δ F (stateLayer Bs) (stateLayer_isLayering Bs) t
                  (assemblyClockEquiv hM9 B1 τ) v
                  ((sourceSumintDatum hM9 B1 Bs.plain W).ℓVec L x
                    (sumintBoundary (Bs.skeleton.sign c'.a.toNode) (fun j => base + latticePoint L (β j))) v)) := by
  obtain ⟨e, B1, hc, ha, hb, hU, hl⟩ := h.exists_asm B0
  refine ⟨e, B1, hc, ha, hb, hl, fun W hpar hbad {L} hL γ δ η F hq hok base β hβ t hp hn => ?_⟩
  rw [recentered_twisted h]
  exact vineChain_eq_sumintForm' hM9 B1 Bs.data Bs.plain W hpar hbad hL γ δ η F (stateLayer Bs)
    (stateLayer_isLayering Bs) hq hok base β hβ t hp hn

end WaveTurbulence.VineEstS4
