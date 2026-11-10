/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoverFineBound
public import WaveTurbulence.Foundations.Spine.SplicedScaleInterpolation
public import WaveTurbulence.Foundations.Spine.PieceArithmetic
public import WaveTurbulence.Foundations.Spine.ClassSumBound
public import WaveTurbulence.Foundations.Spine.LeafwiseKernel
/-! The Stage 1 interface of the layergarden assembly (TARGET L1927-L1976, L2040-L2051, L2236-L2255),
RULINGS R7. A `Stage1Piece` is the data of one piece `K^eqc` of the Stage 1 decomposition (a congruence
class with its SG/LG/ZG prescription and LF refinement): the spliced garden `G_sb`, the choice data `C_1`
and the hinges (`SubproChoices`), the ladder presentation, and the stage-one parameters `g_sk`, `b_sk`.
All of this is DATA of S2a (REDSPLICE-DEF); the propositions `Represents` (redvine2/3, S2) and
`Sound` (subpro, S4, with the C1 half of L2116, S2a) are the statements about it. Nothing here
replaces the construction by an existential: the choice data is a field. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

/-- Data of one Stage 1 piece, for width `2R`, over momentum dimension `d` (the only parameter it depends on,
so that the piece types of parameter records differing only in the large constants agree definitionally). -/
structure Stage1PieceD (d R : ℕ) where
  Gsb : Garden (2 * R)
  Cs : SourceVine.SubproChoices Gsb
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

/-- The leaf-modified kernel families of TARGET L2065-L2067: for each layered garden `LG` a finite
family of real leaf profiles `H_i` with leaf bounds `B_i` and signs. The root-weight redistribution and
the Leibniz rule for derivatives turn the weighted derivatives of a garden sum into a sum of such
families (WeightedLeafKernel, WeightedDerivativeCouple); the plain sum is the one-element family. -/
structure LeafFamilyD (d w : ℕ) where
  ι : LayeredGarden w → Type
  fin : ∀ LG, Fintype (ι LG)
  sign : ∀ LG, ι LG → ℝ
  H : ∀ LG, ι LG → LeafProfiles w d
  B : ∀ LG, ι LG → (Fin w × TTree.Path) → NNReal
  /-- AMEND4 (R40): the signs are products of ζ = ±1 and ε-coefficients, all of absolute value at most 1
  (zero on the zero family of non-plain gardens), so the sign factors never enlarge the mass bound. -/
  sign_abs_le : ∀ LG i, |sign LG i| ≤ 1

/-- The leaf-modified kernel families over the dimension of `P` (so that they agree for parameter records
differing only in the large constants). -/
abbrev LeafFamily (P : WTParams) (w : ℕ) := LeafFamilyD P.d w

/-- The family value at `LG`: the signed sum of the leaf-modified kernels `kernelLeaves` with times `tt`,
coset base `base` and root labels `roots`. -/
noncomputable def LeafFamily.value {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w) : ℂ :=
  @Finset.sum (F.ι LG) ℂ _ (@Finset.univ _ (F.fin LG)) fun i =>
    ((F.sign LG i : ℝ) : ℂ) * kernelLeaves P.L P.γ P.δ LG (F.H LG i) (fun b => tt b.1.1) 0 base roots 0

/-- Every profile of the family at `LG` is leafwise controlled by its bounds. -/
def LeafFamily.Controlled {P : WTParams} {w : ℕ} (F : LeafFamily P w) (LG : LayeredGarden w) : Prop :=
  ∀ i, LeafwiseControlled LG (F.H LG i) (F.B LG i)

/-- The total leaf size `sum_i prod_leaves B_i` of the family at `LG` (`leafSizeProduct`). -/
noncomputable def LeafFamily.size {P : WTParams} {w : ℕ} (F : LeafFamily P w) (LG : LayeredGarden w) : ℝ :=
  @Finset.sum (F.ι LG) ℝ _ (@Finset.univ _ (F.fin LG)) fun i => leafSizeProduct LG (F.B LG i)

/-- The summand of the decoration sum of `kernelLeaves` (LeafwiseKernel), without the prefactor
`coupling ^ order * zeta`. -/
noncomputable def kernelLeavesTerm {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)}
    {nfl : Fin d → ℤ} (κ : GenDecoration LG.garden d nroot nfl) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

/-- `kernelLeaves` with the decoration sum RESTRICTED to the decorations satisfying `sel`
(TARGET L1950: the SG/LG/ZG prescription `sigma` is "an extra restriction on the decoration", the factor
`Z`; R19 (1)). -/
noncomputable def kernelLeavesSel {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (sel : GenDecoration LG.garden d nroot nfl → Prop) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      if sel κ then kernelLeavesTerm L γ δ LG H up s k₀ κ else 0

/-- The family value at `LG` with the decoration sum restricted to `sel`. -/
noncomputable def LeafFamily.valueSel {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w)
    (sel : GenDecoration LG.garden P.d roots 0 → Prop) : ℂ :=
  @Finset.sum (F.ι LG) ℂ _ (@Finset.univ _ (F.fin LG)) fun i =>
    ((F.sign LG i : ℝ) : ℂ) *
      kernelLeavesSel P.L P.γ P.δ LG (F.H LG i) (fun b => tt b.1.1) 0 base roots 0 sel

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

/-- (redvine2)-(redvine3), L1950-L1976, LEAFWISE (RULINGS R9a, R19, R24): a piece is indexed by a congruence
class, the prescription `sigma` on the groups (SG/LG/ZG, L1950) and the finer class `tau` (the at most `2^n`
classes of twists at `V_0` only, L1950); `Stage1Data.Pc` is an arbitrary finite type, so a producer indexes
by whatever it likes (R24 D1, D2). `members` are the gardens of the coarse class and `sel` is the decoration
restriction `Z` of `sigma` together with the membership `LG in tau` (a predicate on the decorations of each
garden, which may depend on `LG`): the value of the piece is the sum, over the gardens of the class, of the
leaf-modified kernel family `F` with the decoration sum restricted to `sel` (`LeafFamily.valueSel`). The
split partitions the DECORATION sum, not the gardens (`Stage1Partition`). The second conjunct is
`RepresentsInt`. TARGET counts classes, not centres: the class count (L2241-L2252) is separate from the
reduction at a fixed centre. The functions `K_(l)`, `K^dagger` and the frequencies `xi_v` are the parameters
of the time-Fourier decomposition. -/
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
    SourceVine.SubproSupport π.Gsb π.Cs P.L P.γ P.η base
      (univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex π.Gsb z.1)
  /-- TARGET L2116, C1 half. -/
  hingeOutsideFirst : ∀ v ∈ π.Cs.hinges, ∀ i, ¬ (π.Cs.collection i).IsInterior v
  /-- AMEND7 (R48). -/
  tripleDesignated : π.Cs.TripleDesignated
  /-- AMEND7 (R48). -/
  hingeNoLoop : π.Cs.HingeNoLoop

end WaveTurbulence.LGSpine
