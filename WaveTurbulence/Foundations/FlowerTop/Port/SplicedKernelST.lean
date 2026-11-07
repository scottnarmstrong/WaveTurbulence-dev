/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceSplicedKernel
public import WaveTurbulence.Foundations.FlowerTop.Port.FlowerP1Stub
/-! AMEND-ST/SX (R61 X4, R66): the spliced kernel with STUB nodes and an explicit SPATIAL PHASE.

`SplicedKernelDataST` extends `SplicedKernelData` by a stub set `stubs` and a stub time `stubTime`: a stub branch has the
prescribed time `stubTime` and is not integrated (the garden-side analogue is `FlowerP1.kernelLeavesFix`, whose
`stubFix` and designated-node time domain `kDomainFix` it follows). `splicedTimeDomainFix` is the spliced analogue of
`kDomainFix`: the box and root-time constraints are imposed on the free branches, and the parent/child order
constraint whenever at least one of the two is free.

`splicedKernelSX` is the normalized spliced kernel with a decoration weight `φ` (the spatial phase; it sits OUTSIDE
the amplitude data `D`, hence outside the derivative-controlled edge class). With no stubs and the trivial phase it is
`splicedKernel` (`splicedKernel_eq_splicedKernelST`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open MeasureTheory Set Finset

/-- Integrals over `ι → ℝ` and over the product indexed by a full subtype agree. -/
theorem integral_pi_subtype_univ {ι : Type*} [Fintype ι] (Q : ι → Prop) [DecidablePred Q] (hQ : ∀ i, Q i)
    (G : (ι → ℝ) → ℂ) :
    ∫ σ : {i // Q i} → ℝ, G (fun i => σ ⟨i, hQ i⟩) = ∫ τ : ι → ℝ, G τ := by
  let e : {i // Q i} ≃ ι := Equiv.subtypeUnivEquiv hQ
  have hmp := measurePreserving_piCongrLeft (fun _ : ι => (volume : Measure ℝ)) e
  have := hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) G
  convert this using 2 with σ
  funext σ
  congr 1

/-- AMEND-ST: spliced kernel data with stubs: designated branches of prescribed time `stubTime`. -/
structure SplicedKernelDataST {w : ℕ} (G : Garden w) (d : ℕ) extends SplicedKernelData G d where
  /-- The stub branches (pendant: see `StubPendant`). -/
  stubs : Finset (GBranch G.tree)
  /-- The time of every stub (the flower time `s`). -/
  stubTime : ℝ

/-- The stub-free data of a `SplicedKernelData`. -/
def SplicedKernelData.noStubs {w d : ℕ} {G : Garden w} (D : SplicedKernelData G d) :
    SplicedKernelDataST G d := { D with stubs := ∅, stubTime := 0 }

/-- The designated times: every stub has time `stubTime`, the other branches are free. -/
def SplicedKernelDataST.fix {w d : ℕ} {G : Garden w} (D : SplicedKernelDataST G d) :
    GBranch G.tree → Option ℝ := FlowerP1.stubFix D.stubs D.stubTime

/-- The spliced time domain with designated branches (the analogue of `kDomainFix`, TARGET L1969-L1971): the unit
branch-time intervals and the truncation at the root times for the free branches, and the parent/child order for
every pair with at least one free member. -/
def splicedTimeDomainFix {w : ℕ} (G : Garden w) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (fix : GBranch G.tree → Option ℝ) : Set (GBranch G.tree → ℝ) :=
  {t | (∀ v, fix v = none → t v ∈ Icc (layer v : ℝ) (layer v + 1) ∧ t v < rootTime v.1.1) ∧
    ∀ v u, v.IsChildOf u → (fix v = none ∨ fix u = none) → t v < t u}

/-- The time integral over the free branches, stubs held at `stubTime`. -/
noncomputable def splicedTimeIntegralST {w d : ℕ} (G : Garden w) (D : SplicedKernelDataST G d)
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  ∫ τ : {b : GBranch G.tree // D.fix b = none} → ℝ,
    (splicedTimeDomainFix G D.layer D.rootTime D.fix).indicator
      (fun t => phaseProd L γ δ G (cosetDecoration G L base z) t *
        ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I))
      (G.extendFix D.fix τ)

/-- The normalized spliced kernel with stubs and a spatial phase `φ` on the decorations. -/
noncomputable def splicedKernelSX {w d : ℕ} (G : Garden w) (D : SplicedKernelDataST G d)
    {roots : Fin w → (Fin d → ℤ)} (φ : GenDecoration G d roots 0 → ℂ)
    (L γ η δ : ℝ) (base : Mom d) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order *
    ∑' z : GenDecoration G d roots 0,
      φ z * ((splicedEpsilon G D.hinges z.1 : ℂ) * (splicedGapIndicator G D.toSplicedKernelData L γ η base z.1 : ℂ) *
        (∏ x ∈ G.molecule.bonds, D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x))) *
        D.hingeAmplitude (fun x => base + latticePoint L (bondIndex G z.1 x.1)) *
        splicedTimeIntegralST G D L γ δ base z.1)

/-- The normalized spliced kernel with stubs (the trivial phase). -/
noncomputable def splicedKernelST {w d : ℕ} (G : Garden w) (D : SplicedKernelDataST G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) : ℂ :=
  splicedKernelSX G D (roots := roots) (fun _ => 1) L γ η δ base

theorem stubFix_empty {w : ℕ} {tree : Fin w → TTree} (s : ℝ) (b : GBranch tree) :
    FlowerP1.stubFix (∅ : Finset (GBranch tree)) s b = none := by
  simp [FlowerP1.stubFix]

theorem SplicedKernelDataST.fix_eq_none {w d : ℕ} {G : Garden w} (D : SplicedKernelDataST G d)
    (hs : D.stubs = ∅) (b : GBranch G.tree) : D.fix b = none := by
  unfold SplicedKernelDataST.fix
  rw [hs]
  exact stubFix_empty _ b

theorem SplicedKernelData.noStubs_fix {w d : ℕ} {G : Garden w} (D : SplicedKernelData G d)
    (b : GBranch G.tree) : D.noStubs.fix b = none :=
  D.noStubs.fix_eq_none rfl b

theorem extendFix_of_none {w : ℕ} (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (hfix : ∀ b, fix b = none) (τ : {b : GBranch G.tree // fix b = none} → ℝ) :
    G.extendFix fix τ = fun b => τ ⟨b, hfix b⟩ := by
  funext b
  unfold Garden.extendFix
  split
  · rename_i v h
    rw [hfix b] at h
    cases h
  · rfl

/-- **Bridge** (time integral): data without stubs gives the old time integral (the stub time is irrelevant). -/
theorem splicedTimeIntegral_eq_ST {w d : ℕ} {G : Garden w} (D : SplicedKernelDataST G d)
    (hs : D.stubs = ∅)
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    splicedTimeIntegral G D.toSplicedKernelData L γ δ base z = splicedTimeIntegralST G D L γ δ base z := by
  unfold splicedTimeIntegral splicedTimeIntegralST
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
      (fun t => phaseProd L γ δ G (cosetDecoration G L base z) t *
        ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I)) t)
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [extendFix_of_none G D.fix hfix τ, hdom]

/-- **Bridge** (kernel): with no stubs and the trivial phase, `splicedKernelST` is `splicedKernel`. -/
theorem splicedKernel_eq_splicedKernelST {w d : ℕ} {G : Garden w} (D : SplicedKernelDataST G d)
    (hs : D.stubs = ∅)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernel G D.toSplicedKernelData L γ η δ base roots = splicedKernelST G D L γ η δ base roots := by
  unfold splicedKernel splicedKernelST splicedKernelSX
  congr 1
  refine tsum_congr fun z => ?_
  rw [one_mul, splicedTimeIntegral_eq_ST D hs L γ δ base z.1]

/-- The same bridge for the stub-free data `D.noStubs` of a `SplicedKernelData`. -/
theorem splicedKernel_eq_splicedKernelST_noStubs {w d : ℕ} {G : Garden w} (D : SplicedKernelData G d)
    (L γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) :
    splicedKernel G D L γ η δ base roots = splicedKernelST G D.noStubs L γ η δ base roots :=
  splicedKernel_eq_splicedKernelST D.noStubs rfl L γ η δ base roots

end WaveTurbulence.LGSpine
