/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.Defs
public import WaveTurbulence.Foundations.Flower.V5W.Statements

/-! # V5W-2L: V5's frontier class bound with a finite product of top filters (R179, F-B3s-4)

On a clean point a capped stem can pass through the upper joint `u₁` of a spliced unit, where σ's stem filter and a
selection shell may both sit: the unit kernel carries `χ₀(|Ω_{u₁}|/a) · χ₀(|Ω_{u₁}|/b)`, which is not one
`V5W.topFilterWeight`.  This file states the bound for a finite product of `χ₀` dilations.

* `topFilterWeightL S`: `∏_{s ∈ S} χ₀(|Ω|/s)` as a `VineSpaceK.nodeWeight` of `![k_v, k_{v0}, k_{v1}, k_{v2}]`
  (the empty list gives `1`); `topFilterWeightL [] = topFilterWeight none`, `topFilterWeightL [s] = topFilterWeight
  (some s)`.
* `regionWeightFWL`, `twistedLocalKernelFWL`, `twistedRecenteredFWL`, `unitKernelFWL`, `unitRecenteredFWL`: V5W-0's
  `regionWeightFW`, … verbatim with `S : List ℝ` and `topFilterWeightL S` in place of `topFilterWeight S`.
* `V5FrontierClassBoundAtL`: `V5W.V5FrontierClassBoundAt` verbatim, except `S : List ℝ`, `∀ s ∈ S, 0 < s`, the class
  kernel `twistedRecenteredFWL` (top weight `topFilterWeightL S`) and the mass `topFilterMass ^ S.length` in place of
  `topFilterMass`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W2L
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK WaveTurbulence.VineSpaceB WaveTurbulence.VineC WaveTurbulence.Represents
open WaveTurbulence.Flower.Stage1W
open WaveTurbulence.Flower.V5W (topFilterWeight topFilterMass nodeRowIncoh stateCoreLayer clLocalKernelFW
  regionWeightFW twistedLocalKernelFW twistedRecenteredFW unitKernelFW unitRecenteredFW V5FrontierClassBoundAt)
open scoped ENNReal FourierTransform
open Set
open VineEstS5C.P4.Final LGSpine Cut2A

/-! ## §1 A finite product of region-top stem filters -/

/-- **The product of low-pass resonance filters at one branch**, as a `VineSpaceK.nodeWeight` of
`![k_v, k_{v0}, k_{v1}, k_{v2}]`: `∏_{s ∈ S} χ₀(|Ω_v|/s)` (`S = []`: no filter).
`omegaNode G k v = resFactor (k v0) (k v1) (k v2) (k v)`. -/
def topFilterWeightL {d : ℕ} (S : List ℝ) : (Fin 4 → Mom d) → ℂ :=
  fun q => (((S.map fun s => WaveTurbulence.chi0 (|resFactor (q 1) (q 2) (q 3) (q 0)| / s)).prod : ℝ) : ℂ)

@[simp] theorem topFilterWeightL_nil {d : ℕ} : (topFilterWeightL [] : (Fin 4 → Mom d) → ℂ) = topFilterWeight none :=
  rfl

theorem topFilterWeightL_cons {d : ℕ} (s : ℝ) (S : List ℝ) (q : Fin 4 → Mom d) :
    topFilterWeightL (s :: S) q = topFilterWeight (some s) q * topFilterWeightL S q := by
  simp [topFilterWeightL, topFilterWeight]

/-! ## §2 The kernels (V5W-0's, verbatim with `topFilterWeightL S`) -/

/-- **The region multiplier of a state on a block `(U, a)`** with a product of top filters: V5W-0's `regionWeightFW`
verbatim with `topFilterWeightL S` in place of `topFilterWeight S`. -/
def regionWeightFWL {w d : ℕ} {ι : Type*} (p : ℕ) (g : Mom d → ℂ) (S : List ℝ) (L : ℝ) (base : Mom d)
    (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) (a : GBranch X.skeleton.tree)
    (x : GNode X.skeleton.tree → Fin d → ℤ) : ℂ :=
  (∏ y ∈ Finset.univ.filter (X.skeleton.molecule.InGroup U),
    if nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) = 0 then
      topPsi p g (stateCoreLayer X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)))
        (stateCoreLayer X (X.skeleton.molecule.atom y))
        (cosetDecoration X.skeleton L base x (Mole.dartNode X.skeleton y))
    else 1) *
  nodeWeight (topFilterWeightL S) L base a x

/-- The weighted kernel of a class member with a product of top filters (V5W-0's `twistedLocalKernelFW`). -/
def twistedLocalKernelFWL {w d : ℕ} {κ : Type*} (p : ℕ) (g : Mom d → ℂ) (S : List ℝ)
    (Bs : FamilyReconstruction w κ) (c : ChainAt Bs.skeleton Bs.family)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) : ℂ :=
  clLocalKernelFW p g Bs.data Bs.plain (clRegionData Bs.skeleton c.block c.cl) L γ δ F (stateLayer Bs)
    (stateLayer_isLayering Bs) base (regionWeightFWL p g S L base Bs c.U c.a) W t0 t1 t2 e f g' h

/-- **The pinned class kernel with a product of top filters** (V5W-0's `twistedRecenteredFW`). -/
def twistedRecenteredFWL {w d : ℕ} {κ : Type*} (p : ℕ) (g : Mom d → ℂ) (S : List ℝ) (G : Garden w)
    (a : GBranch G.tree) (Z : Finset (Σ Bs : FamilyReconstruction w κ, ChainAt Bs.skeleton Bs.family))
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) : ℂ :=
  recPhase (G.sign a.toNode) L γ δ t0 e f g' h *
    ∑ x ∈ Z, twistedLocalKernelFWL p g S x.1 x.2 L γ δ F base W t0 t1 t2 e f g' h

/-- The weighted unit kernel of a state with a product of top filters (V5W-0's `unitKernelFW`). -/
def unitKernelFWL {w d : ℕ} {ι : Type*} {Q : ι → Prop} (p : ℕ) (g : Mom d → ℂ) (S : List ℝ)
    (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) : ℂ :=
  clLocalKernelFW p g X.data X.plain (clRegionData X.skeleton u.blk.block u.cl) L γ δ F (stateLayer X)
    (stateLayer_isLayering X) base (regionWeightFWL p g S L base X u.blk.U u.blk.a) W t0 t1 t2 e f g' h

/-- The recentered weighted unit kernel with a product of top filters (V5W-0's `unitRecenteredFW`). -/
def unitRecenteredFWL {w d : ℕ} {ι : Type*} {Q : ι → Prop} (p : ℕ) (g : Mom d → ℂ) (S : List ℝ)
    (X : FamilyReconstruction w ι) (u : UnitAt X.skeleton X.family Q)
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' h : Mom d) : ℂ :=
  recPhase (X.skeleton.sign u.blk.a.toNode) L γ δ t0 e f g' h *
    unitKernelFWL p g S X u L γ δ F base W t0 t1 t2 e f g' h

/-! ## §3 The bound -/

/-- **`V5FrontierClassBoundAtL`** — V5's frontier class bound with a finite product of region-top stem filters:
`V5W.V5FrontierClassBoundAt` verbatim, except the filter binder `S : List ℝ` with `∀ s ∈ S, 0 < s`, the class kernel
`twistedRecenteredFWL p (g a.1.1) S …` (top weight `topFilterWeightL S`), and the mass `topFilterMass ^ S.length` in
place of `topFilterMass`. -/
def V5FrontierClassBoundAtL (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (g : Fin w → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
      (∀ j x, (g j x).im = 0) →
    ∀ (S : List ℝ), (∀ s ∈ S, 0 < s) →
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecenteredFWL p (g a.1.1) S G a
        (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        P.L P.γ P.δ h wBar (modW lam)
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal (cψ ^ (9 * U.card + 4 * clLocalOrder2 RD hG R) * topFilterMass ^ S.length) *
      ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

/-- **`V5FrontierClassBoundL`** (gate form, frozen `WTPrefix`). -/
def V5FrontierClassBoundL : Prop := WTPrefix V5FrontierClassBoundAtL

/-! ## §4 The single-filter kernels are the `S.toList` instances -/

end WaveTurbulence.Flower.V5W2L
