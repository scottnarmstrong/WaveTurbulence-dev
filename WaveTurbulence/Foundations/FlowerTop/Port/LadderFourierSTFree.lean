/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedGatesST
/-! FLOWER-P5: the corrected ladder Fourier gate with stubs (free-clock box sum). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine MeasureTheory Set Finset
open scoped Classical ENNReal

/-- Integer frequency boxes indexed by the FREE (non-designated) branches only. -/
def sourceFrequencyBoxesFree {w : ℕ} (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (A : Set (GBranch G.tree → ℝ)) : Set ({b : GBranch G.tree // fix b = none} → ℤ) :=
  {σ | ∃ α ∈ A, ∀ v : {b : GBranch G.tree // fix b = none}, ⌊α v.1⌋ = σ v}

/-- The Fourier box sum with stubs: boxes and suprema range over the free-clock frequencies only. -/
noncomputable def splicedFourierBoxSumSTFree {w : ℕ} (G : Garden w)
    (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (A : Set (GBranch G.tree → ℝ)) : ℝ≥0∞ :=
  ∑' σ : sourceFrequencyBoxesFree G fix A,
    ⨆ (α : GBranch G.tree → ℝ) (_ : α ∈ A) (_ : ∀ v : {b : GBranch G.tree // fix b = none}, |α v.1 - σ.1 v| ≤ 1),
      ‖splicedFourierBST G layer rootTime fix α‖ₑ

/-- TARGET ladderl1old (L1994-L2001) for spliced kernels with pendant stubs: corrected statement. -/
abbrev LadderFourierAtST' (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelDataST G P.d) (scales : Finset (GBranch G.tree) → ℝ),
    (∀ v, D.layer v ≤ p) → SplicedAmplitudeBounds G D.toSplicedKernelData →
    StubPendantLadder G D.hinges D.gapSpecification D.stubs →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    splicedFourierBoxSumSTFree G D.layer D.rootTime D.fix
      (splicedFrequencySpectrum G D.toSplicedKernelData scales P.L P.γ P.η P.δ base roots) ≤
    ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ ^ (-1 / 2 - 5 * P.ν)) ^ G.order *
      P.L ^ (P.δ ^ (5 * P.ν) * G.molecule.rho) *
      ∏ S ∈ G.molecule.maximalLadders,
        Molecule.ladderWeight P.L P.γ P.δ (scales S) ^ Molecule.ladderLength S)

/-- No stubs: the free box sum is the old box sum. -/
theorem splicedFourierBoxSumSTFree_noStubs {w d : ℕ} {G : Garden w} (D : SplicedKernelDataST G d)
    (hs : D.stubs = ∅) (A : Set (GBranch G.tree → ℝ)) :
    splicedFourierBoxSumSTFree G D.layer D.rootTime D.fix A = splicedFourierBoxSum G D.layer D.rootTime A := by
  have hfix := D.fix_eq_none hs
  have hB : ∀ α, splicedFourierBST G D.layer D.rootTime D.fix α = splicedFourierB G D.layer D.rootTime α :=
    fun α => (splicedFourierB_eq_ST D hs α).symm
  let e : ({b : GBranch G.tree // D.fix b = none} → ℤ) ≃ (GBranch G.tree → ℤ) :=
    { toFun := fun σ b => σ ⟨b, hfix b⟩
      invFun := fun σ v => σ v.1
      left_inv := fun σ => by funext v; rfl
      right_inv := fun σ => by funext b; rfl }
  unfold splicedFourierBoxSumSTFree splicedFourierBoxSum
  simp only [hB]
  have hmem : ∀ σ, σ ∈ sourceFrequencyBoxesFree G D.fix A ↔ e σ ∈ sourceFrequencyBoxes G A := by
    intro σ
    simp only [sourceFrequencyBoxesFree, sourceFrequencyBoxes, Set.mem_ofPred_eq]
    refine exists_congr fun α => and_congr_right fun _ => ⟨fun h b => h ⟨b, hfix b⟩, fun h v => h v.1⟩
  rw [← (Equiv.subtypeEquiv e hmem).tsum_eq]
  refine tsum_congr fun σ => ?_
  refine iSup_congr fun α => iSup_congr fun hα => ?_
  have : (∀ v : {b : GBranch G.tree // D.fix b = none}, |α v.1 - σ.1 v| ≤ 1) ↔
      ∀ v, |α v - (e σ.1) v| ≤ 1 :=
    ⟨fun h b => h ⟨b, hfix b⟩, fun h v => h v.1⟩
  simp only [Equiv.subtypeEquiv_apply, this]

/-- **Bridge**: the corrected gate with stubs implies the current ladder Fourier estimate. -/
theorem ladderFourierAt_of_ST' (P : WTParams) (h : LadderFourierAtST' P) : LadderFourierAt P := by
  intro p hp R hR hRmax G hpl hir hbal hn hnmax D scales hlay hD base roots
  have := h p hp R hR hRmax G hpl hir hbal hn hnmax D.noStubs scales hlay hD
    (stubPendantLadder_empty _ _ _) base roots
  rw [splicedFourierBoxSumSTFree_noStubs D.noStubs rfl] at this
  exact this

end WaveTurbulence.FlowerP5
