/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.MolecularSpineAt
public import WaveTurbulence.Foundations.Spine.SpliceGateMonotone
public import WaveTurbulence.Foundations.FlowerTop.Port.Stage1InterfaceST
/-! AMEND-ST (R61 X4): the stub-pendant premise in `CoarseSplicedAt` and `LadderFourierAt`.

`CoarseSplicedAtST` and `LadderFourierAtST` are the coarse spliced estimate (finalsbest1) and the ladder Fourier
estimate (ladderl1old) for spliced kernel data WITH STUBS (`SplicedKernelDataST`), under the premise that the stubs
are pendant (`StubPendant`, `StubPendantLadder`: not hinges, not in selected objects, not in ladders, no gap
specification). With no stubs the premise is vacuous and the estimates are the current ones
(`coarseSplicedAt_of_ST`, `ladderFourierAt_of_ST`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical ENNReal

/-- `SplicedSourcePremises` for data with stubs: the same source geometry and support, with the selected-object
choice `C` also making the stubs pendant. -/
structure SplicedSourcePremisesST {R : ℕ} (P : WTParams) (G : Garden (2 * R))
    (D : SplicedKernelDataST G P.d) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop where
  molecule : G.molecule.IsMolecule
  connected : G.molecule.IsConnected
  atom_count : G.molecule.atoms.card = G.order
  bond_count : G.molecule.bonds.card + R = 2 * G.order
  subpro : ∃ C : SourceVine.SubproChoices G,
    C.Structural ∧ D.hinges = C.hinges ∧
    (∀ z : GenDecoration G P.d roots 0,
      splicedEpsilon G D.hinges z.1 ≠ 0 → splicedGapIndicator G D.toSplicedKernelData P.L P.γ P.η base z.1 ≠ 0 →
      SourceVine.SubproSupport G C P.L P.γ P.η base
        (univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex G z.1)) ∧
    StubPendant G C D.gapSpecification D.stubs

theorem SplicedSourcePremisesST.ofOld {R : ℕ} {P : WTParams} {G : Garden (2 * R)}
    {D : SplicedKernelDataST G P.d} (hs : D.stubs = ∅) {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    (h : SplicedSourcePremises P G D.toSplicedKernelData base roots) :
    SplicedSourcePremisesST P G D base roots := by
  obtain ⟨C, hC, hh, hsup⟩ := h.subpro
  exact ⟨h.molecule, h.connected, h.atom_count, h.bond_count,
    ⟨C, hC, hh, hsup, by rw [hs]; exact stubPendant_empty _ _ _⟩⟩

/-- TARGET finalsbest1 (L2075-L2077) for spliced kernels with pendant stubs (AMEND-ST). -/
abbrev CoarseSplicedAtST (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelDataST G P.d, SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ v, D.layer v ≤ p) →
  ∀ (A : SourceMaximalLadderData G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedSourcePremisesST P G D base roots →
    ‖splicedKernelST G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (P.C₁ * Real.sqrt P.δ) ^ G.order *
        P.L ^ (-P.η * A.totalIncoherency D.layer +
          80 * P.d * (G.molecule.rho + D.hinges.card))

/-- **Bridge**: the coarse estimate with stubs implies the current coarse estimate. -/
theorem coarseSplicedAt_of_ST (P : WTParams) (h : CoarseSplicedAtST P) : CoarseSplicedAt P := by
  intro p hp R hR hRmax G hpl hir hbal hn hnmax D hD hlay A base roots hprem
  have := h p hp R hR hRmax G hpl hir hbal hn hnmax D.noStubs hD hlay A base roots
    (SplicedSourcePremisesST.ofOld (D := D.noStubs) rfl hprem)
  rw [← splicedKernel_eq_splicedKernelST_noStubs] at this
  exact this

/-- The literal time integral `B(α)` with designated (stub) branches. -/
noncomputable def splicedFourierBST {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) (α : GBranch G.tree → ℝ) : ℂ :=
  ∫ τ : {b : GBranch G.tree // fix b = none} → ℝ,
    (splicedTimeDomainFix G layer rootTime fix).indicator
      (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I))
      (G.extendFix fix τ)

theorem splicedFourierB_eq_ST {w d : ℕ} {G : Garden w} (D : SplicedKernelDataST G d) (hs : D.stubs = ∅)
    (α : GBranch G.tree → ℝ) :
    splicedFourierB G D.layer D.rootTime α = splicedFourierBST G D.layer D.rootTime D.fix α := by
  unfold splicedFourierB splicedFourierBST
  have hfix := D.fix_eq_none hs
  have hdom : splicedTimeDomainFix G D.layer D.rootTime D.fix =
      splicedTimeDomain G D.layer D.rootTime := by
    ext t
    simp only [splicedTimeDomainFix, splicedTimeDomain, hfix, true_or, forall_const, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v => (h1 v).1, h2, fun v => (h1 v).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun v => ⟨h1 v, h3 v⟩, h2⟩
  have key := integral_pi_subtype_univ (Q := fun b : GBranch G.tree => D.fix b = none) hfix
    (fun t => (splicedTimeDomain G D.layer D.rootTime).indicator
      (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I)) t)
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [extendFix_of_none G D.fix hfix τ, hdom]

end WaveTurbulence.LGSpine
