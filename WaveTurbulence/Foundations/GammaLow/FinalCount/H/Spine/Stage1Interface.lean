/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1Interface
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.CoverFineBound
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SplicedSourceInterpolation
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.Stage1Interface`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The Stage 1 interface of the layergarden assembly (TARGET L1927-L1976, L2040-L2051, L2236-L2255),
RULINGS R7. A `Stage1Piece` is the data of one piece `K^eqc` of the Stage 1 decomposition (a congruence
class with its SG/LG/ZG prescription and LF refinement): the spliced garden `G_sb`, the choice data `C_1`
and the hinges (`SubproChoices`), the ladder presentation, and the stage-one parameters `g_sk`, `b_sk`.
All of this is DATA of S2a (REDSPLICE-DEF); the propositions `Represents` (redvine2/3, S2) and
`Sound` (subpro, S4, with the C1 half of L2116, S2a) are the statements about it. Nothing here
replaces the construction by an existential: the choice data is a field. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

/-- Data of one Stage 1 piece, for width `2R`, over momentum dimension `d` (the only parameter it depends on,
so that the piece types of parameter records differing only in the large constants agree definitionally). -/
structure Stage1PieceD (d R : ℕ) where
  Gsb : Garden (2 * R)
  Cs : Src.SubproChoices Src.γL Gsb
  ladders : SourceMaximalLadderData Gsb
  layer : GBranch Gsb.tree → ℕ
  gapSpecification : (v : GBranch Gsb.tree) → Option (LocalGapSpecification Gsb v)
  /-- `g_sk` (TARGET L1962): incoherency of the attached regular parts and of the vines in `V_0`. -/
  gsk : ℕ
  /-- `b_sk`: the number of bad vines in `V_0`. -/
  bsk : ℕ

/-- Data of one Stage 1 piece, for width `2R` (the S2a record; fields as in `Stage1PieceD`). -/
abbrev Stage1Piece (P : WTParams) (R : ℕ) := Stage1PieceD P.d R

/-- The spliced kernel data of a piece for given analytic functions `K_(l)`, `K^dagger`, `xi_v`. -/
def Stage1Piece.data {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (tt : Fin (2 * R) → ℝ)
    (center : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : GBranch π.Gsb.tree → ℝ) : SplicedKernelData π.Gsb P.d where
  layer := π.layer
  hinges := π.Cs.hinges
  center := center
  edgeAmplitude := edge
  hingeAmplitude := hinge
  gapSpecification := π.gapSpecification
  frequency := freq
  rootTime := tt

/-- `g_sb`: total incoherency index of the maximal ladders of the piece. -/
noncomputable def Stage1PieceD.gsb {d R : ℕ} (π : Stage1PieceD d R) : ℕ :=
  π.ladders.totalIncoherency π.layer

/-- The integral conjunct of `Stage1Piece.Represents` (R23 (2), R24 D3): the piece value `val` is an average,
against a weight of total mass at most the prefactor
`(C_1 sqrt delta)^{n - n_sb} C_1^{n_sb + 2R} L^{-eta^8 g_sk - eta^2 b_sk + eta^7 q_sk}` times the leaf size `s`,
of the normalized spliced kernels `K_{G_sb}` (with `q_sk` the number of hinges). The factor `C_1^{n_sb}`
is the loss of the node-centre sum (Lemma `treelemma`, TARGET L1959 "a loss of at most `C_0^n`"), and `C_1^{2R}`
is one constant per root (REP-ANALYTIC: the centre decomposition loses `C^{3 n_sb + w}`, `w = 2R` roots; `C_1` absorbs
the 3); R24 D3:
TARGET writes `C_0^n` there and then omits it in (redvine2), L1962. F-TT (R33): the spliced time domain is truncated at the root times `tt` (`SplicedKernelData.rootTime`),
TARGET `sumint` domain clause (ii). The unit-ball centres `k^0`
(L1962-L1963, summed term by term in redvine2) are part of the integration variable: `ctr xi` is the centre of
the term `xi`. It mentions neither the garden family nor the decoration restriction, so it is the part of
`Represents` that the flower pieces share (`stage1_piece_bound_int`). -/
def Stage1Piece.RepresentsInt {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (val : ℂ) : Prop :=
  ∃ (Ξ : Type) (_ : MeasurableSpace Ξ) (μ : Measure Ξ) (w : Ξ → ℂ)
    (ctr : Ξ → GardenDart π.Gsb → Mom P.d)
    (edge : Ξ → GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : Ξ → (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ)
    (freq : Ξ → GBranch π.Gsb.tree → ℝ),
    Integrable (fun ξ => w ξ * splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots) μ ∧
    val = ∫ ξ, w ξ * splicedKernel π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))
      P.L P.γ P.η P.δ base roots ∂μ ∧
    Integrable (fun ξ => ‖w ξ‖) μ ∧
    (∫ ξ, ‖w ξ‖ ∂μ ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
      P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * s) ∧
    ∀ ξ, SplicedAmplitudeBounds π.Gsb (π.data tt (ctr ξ) (edge ξ) (hinge ξ) (freq ξ))

def Stage1Piece.Represents {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (s : ℝ) (val : ℂ) : Prop :=
  val = ∑ LG ∈ members, F.valueSel tt base roots LG (sel LG) ∧ π.RepresentsInt n tt base roots s val

/-- The structural and decorated properties of a piece: `G_sb` is a plain irreducible balanced garden
of admissible order whose pre-layering is below `p` (S2a), the conclusions (1)-(6) of TARGET `subpro`
(S4) on the support of the piece's epsilon/gap factors, and the C1 half of TARGET L2116 (S2a). -/
structure Stage1Piece.Sound {P : WTParams} {R : ℕ} (π : Stage1Piece P R) (p : ℕ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop where
  plain : π.Gsb.IsPlain
  irreducible : π.Gsb.Irreducible
  balanced : IsBalancedSig π.Gsb.sig
  order_pos : 1 ≤ π.Gsb.order
  order_le : π.Gsb.order ≤ P.N (p + 1) ^ 4
  layer_le : ∀ v, π.layer v ≤ p
  molecule : π.Gsb.molecule.IsMolecule
  connected : π.Gsb.molecule.IsConnected
  atom_count : π.Gsb.molecule.atoms.card = π.Gsb.order
  bond_count : π.Gsb.molecule.bonds.card + R = 2 * π.Gsb.order
  structural : π.Cs.Structural
  support : ∀ z : GenDecoration π.Gsb P.d roots 0,
    splicedEpsilon π.Gsb π.Cs.hinges z.1 ≠ 0 →
    splicedGapIndicator π.Gsb (π.data (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0)) P.L P.γ P.η base z.1 ≠ 0 →
    Src.SubproSupport Src.γL π.Gsb π.Cs P.L P.γ P.η base
      (univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex π.Gsb z.1)
  /-- TARGET L2116, C1 half. -/
  hingeOutsideFirst : ∀ v ∈ π.Cs.hinges, ∀ i, ¬ (π.Cs.collection i).IsInterior v
  /-- AMEND7 (R48). -/
  tripleDesignated : π.Cs.TripleDesignated
  /-- AMEND7 (R48). -/
  hingeNoLoop : π.Cs.HingeNoLoop

end WaveTurbulence.GammaLow.FinalCount.H
