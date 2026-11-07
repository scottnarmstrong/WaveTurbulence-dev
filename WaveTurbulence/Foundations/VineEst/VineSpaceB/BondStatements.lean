/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineSpaceK.WeightedStatements
public import WaveTurbulence.Foundations.Molecule.GardenLabelExtension
public import WaveTurbulence.Foundations.IncohInst.Links.Coherence
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.InflatedCoreBranches

/-! # `V5BondClassBound` (R132/R133/R135): the V5 class-sum bound with a bond multiplier — definitions only

This module states the export and proves nothing; it is the batch 4b-1c port unit. The proof is
`VineSpaceB.Final.v5BondClassBound_of_uniformCert` (V5-SPACE-EXT, uni-space); main-world port of `VineSpaceB.Statement`.

**The multiplier** (`regionBondWeight`, R135). For a class member `z` with CL region `z.2.U`, the product over the
darts `y` of the molecule of `z`'s skeleton with both ends in `z.2.U` (`Molecule.InGroup`) of
`ψ (core layer at the far end) (core layer at the near end) k_y`. Core layers are the layers of the member's
layered garden at the core position of a branch (the lone leaf of its regular tree, T Remark sublayer L1464);
`k_y` is the coset momentum of the bond. For a top-supported `ψ` (`ψ q q' ≡ 1` unless `q < p = q'`) exactly one dart
of each top bond (layer-`p` end above a lower-layer end) carries a factor.

**Why class-common.** Every family operation preserves the core layers (`LFConstruction.coreLayers`) and carries the
region along (`ChainAt.next`, `twistedAtoms`); a unit twist is a directed-molecule isomorphism preserving every bond
label (`unitTwistMoleculeIso`, `twist_bond_labels`, T Remark twistexplain (a),(d)). The multiplier does not read the
layers at the roots of the regular objects, which vary over the coherent replacements the class sums over (T Def
lftwist L1472–L1477, the exact zero of T L1907): R135, refuting the earlier `regionTopWeight`.

**The bound.** Verbatim `VineEstCanonLayerHalfMXK` with the multiplier `regionBondWeight (ψ a.1.1)` (the tree of the
region's top branch; a CL region lies in one tree) and the mass `cψ ^ (3 * U.card)`. Gate form
`V5BondClassBound := WTPrefix V5BondClassBoundAt`, every constant before the record `P`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.VineSpaceB
open WaveTurbulence WaveTurbulence.Fourier WaveTurbulence.VineEstS3.FS WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B WaveTurbulence.Links
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory VineParamContract
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P1 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P2
  WaveTurbulence.VineEstS5C.P4
  WaveTurbulence.VineEstS5C.FlatMod
open WaveTurbulence.VineSpaceK
open scoped ENNReal
open VineEstS5C.P4.Final LGSpine Cut2A

/-- The skeleton (core) layer of a branch of a class member: the layer of its regular tree's core. -/
def memberCoreLayer {w : ℕ} {ι : Type*} (z : ClassMember w ι) (v : GBranch z.1.skeleton.tree) : ℕ :=
  layerAt z.1.layered (z.1.data.corePosition v)

/-- **The class-common bond multiplier** of a class member (R135). -/
def regionBondWeight {w d : ℕ} {ι : Type*} (ψ : ℕ → ℕ → Mom d → ℂ) (L : ℝ) (base : Mom d)
    (z : ClassMember w ι) (x : GNode z.1.skeleton.tree → Fin d → ℤ) : ℂ :=
  ∏ y ∈ Finset.univ.filter (z.1.skeleton.molecule.InGroup z.2.U),
    ψ (memberCoreLayer z (z.1.skeleton.molecule.atom (z.1.skeleton.molecule.mate y)))
      (memberCoreLayer z (z.1.skeleton.molecule.atom y))
      (cosetDecoration z.1.skeleton L base x (Mole.dartNode z.1.skeleton y))

/-- A label weight is TOP-SUPPORTED at level `p` when it is `1` off the top labels (far layer `< p`, near
layer `= p`). (FC23's definition, verbatim.) -/
def TopSupported {w d : ℕ} (p : ℕ) (ψ : Fin w → ℕ → ℕ → Mom d → ℂ) : Prop :=
  ∀ j q q', ¬ (q < p ∧ q' = p) → ψ j q q' = fun _ => 1

/-- Every label weight has a Fourier presentation of mass at most `c`. (FC23's definition, verbatim.) -/
def SpatialPresented {w d : ℕ} (ψ : Fin w → ℕ → ℕ → Mom d → ℂ) (c : ℝ) : Prop :=
  ∀ j q q', ∃ (α : Type) (_ : MeasurableSpace α) (M : SpatialMeasure (Mom d) α),
    M.mass ≤ c ∧ ∀ x, M.value x = ψ j q q' x

/-- **The body of `V5BondClassBound`** (owner: V5-SPACE extension, R132/R135). -/
def V5BondClassBoundAt (P : WTParams) : Prop :=
  ∀ {p : ℕ}, p < P.D → ∀ (h : ℕ → Mom P.d → ℝ) (B₀ : ℝ), 0 ≤ B₀ →
    (∀ r ≤ p, SNormR (40 * P.d) (40 * P.d) (h r) ≤ ENNReal.ofReal B₀) →
    ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
      {n : ℕ} (_hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
      (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (kind : Bool),
      CanonicalObject p kind (layeredReconstruction RD hG layer hLayer) → (∀ x, layer x ≤ p) →
    (RD.garden hG).order ≤ P.N (p + 1) ^ 4 → clLocalOrder1 R ≤ P.N 1 ^ 4 →
    ∀ (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (ψ : Fin w → ℕ → ℕ → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → TopSupported p ψ → SpatialPresented ψ cψ →
    RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
      P.L P.γ P.δ h p →
    XNorm00Restr (2 * P.η ^ 8) (Eng.outBox (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar))
      (Eng.outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η)
      (fun tt E => twistedRecenteredModCX G a
        (canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B))
        (fun z => regionBondWeight (ψ a.1.1) P.L wBar z) P.L P.γ P.δ h wBar lam
        (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
        (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3)) ≤
    ENNReal.ofReal (cψ ^ (3 * U.card)) * ENNReal.ofReal ((1 + |lam|) ^ (6 * P.η ^ 6) * ((P.C₁ * Real.sqrt P.δ) ^ clLocalOrder2 RD hG R *
      P.L ^ (-(P.η ^ 8 * ((cohmolIndex B RD hG layer +
        (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).M₁ : ℕ) : ℝ)) -
        P.η ^ 2 / 2 * ((Finset.univ.filter fun i => (assemblyShape hM9 B).nor i = false).card : ℝ) + P.η ^ 7) *
      regionLeafSize RD hG R layer hLayer (fun _ => B₀)))

/-- **`V5BondClassBound`** (gate form: thresholds and constants precede the record `P`, frozen `WTPrefix`). -/
def V5BondClassBound : Prop := WTPrefix V5BondClassBoundAt

end WaveTurbulence.VineSpaceB
