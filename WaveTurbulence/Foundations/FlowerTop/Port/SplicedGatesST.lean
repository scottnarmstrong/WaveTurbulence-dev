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

theorem SplicedSourcePremisesST.toOld {R : ℕ} {P : WTParams} {G : Garden (2 * R)}
    {D : SplicedKernelDataST G P.d} {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    (h : SplicedSourcePremisesST P G D base roots) :
    SplicedSourcePremises P G D.toSplicedKernelData base roots := by
  obtain ⟨C, hC, hh, hs, _⟩ := h.subpro
  exact ⟨h.molecule, h.connected, h.atom_count, h.bond_count, ⟨C, hC, hh, hs⟩⟩

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

noncomputable def splicedFourierBoxSumST {w : ℕ} (G : Garden w)
    (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (A : Set (GBranch G.tree → ℝ)) : ℝ≥0∞ :=
  ∑' σ : sourceFrequencyBoxes G A,
    ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ A) (_ : ∀ v, |α v - σ.1 v| ≤ 1),
      ‖splicedFourierBST G layer rootTime fix α‖ₑ

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

theorem splicedFourierBoxSum_eq_ST {w d : ℕ} {G : Garden w} (D : SplicedKernelDataST G d) (hs : D.stubs = ∅)
    (A : Set (GBranch G.tree → ℝ)) :
    splicedFourierBoxSum G D.layer D.rootTime A = splicedFourierBoxSumST G D.layer D.rootTime D.fix A := by
  unfold splicedFourierBoxSum splicedFourierBoxSumST
  simp only [splicedFourierB_eq_ST D hs]

/-- TARGET ladderl1old (L1994-L2001) for spliced kernels with pendant stubs (AMEND-ST): the Fourier box sum of the
time integral over the free branches.

DEPRECATED (R77, AMEND-SX2): this statement is FALSE as written for stub data (its box sum ranges over ALL branch
frequencies, including the fixed stub clocks, which have no Fourier decay; see spliced-x/SPLICED-X2-OBSTRUCTION.md).
Use `FlowerP5.LadderFourierAtST'` (module `LadderFourierSTFree`; box sum over the free-clock frequencies). Nothing
in the AMEND-SX2 chain routes through this statement; the stub-free case is recovered by `ladderFourierAt_of_ST'`. -/
abbrev LadderFourierAtST (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelDataST G P.d) (scales : Finset (GBranch G.tree) → ℝ),
    (∀ v, D.layer v ≤ p) → SplicedAmplitudeBounds G D.toSplicedKernelData →
    StubPendantLadder G D.hinges D.gapSpecification D.stubs →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    splicedFourierBoxSumST G D.layer D.rootTime D.fix
      (splicedFrequencySpectrum G D.toSplicedKernelData scales P.L P.γ P.η P.δ base roots) ≤
    ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) *
      ∏ S ∈ G.molecule.maximalLadders,
        Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S)

/-- **Bridge**: the ladder Fourier estimate with stubs implies the current one. -/
theorem ladderFourierAt_of_ST (P : WTParams) (h : LadderFourierAtST P) : LadderFourierAt P := by
  intro p hp R hR hRmax G hpl hir hbal hn hnmax D scales hlay hD base roots
  have := h p hp R hR hRmax G hpl hir hbal hn hnmax D.noStubs scales hlay hD
    (stubPendantLadder_empty _ _ _) base roots
  rw [← splicedFourierBoxSum_eq_ST D.noStubs rfl] at this
  exact this

end WaveTurbulence.LGSpine
