/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.Spine.Stage1GateMonotone
/-! # The Stage 1 reduction gate over `𝒱_γ` (packet L5a, FAMILY-γ: Stage1′)

TARGET stage 1 (L1926–L1977, redvine/redvine2/redvine3), subpro (L2040–L2053) and the class count
(finalprooffin, L2236–L2252) with the vine family `𝒱_γ` of ruling D11 (`Molecule.IsVineGamma`, `TVine/Defs.lean`).

Main's `LGSpine.Stage1ReductionAt` is family-specific only through the piece data: the subpro choices
`LGSpine.SourceVine.SubproChoices` of a piece and the decorated conclusions `LGSpine.SourceVine.SubproSupport` of
`Stage1Piece.Sound` are stated over main's source objects `SourceVine.Object` (family `∃ X : VineType, IsVine X`),
which cannot represent a T-vine. This module is a literal copy of main's `Stage1PieceD`, `Stage1Piece.data`,
`RepresentsInt`, `Represents`, `Sound` (`Spine/Stage1Interface.lean`), `Stage1Data`, `gbar`, `rbar`
(`Spine/Stage1SumBound.lean`), `Stage1Counts`, `Stage1ReductionAt` (`Spine/Stage1Gate.lean`) and their large-constant
monotonicity (`Spine/Stage1GateMonotone.lean`), sha256 in `COPIED-SHA256SUMS`, with exactly one change: the subpro
choices and their support are L6's `𝒱_γ` source carrier `FinalCount.Src.{SubproChoices γ, SubproSupport γ}` at
`γ = P.γ` (PLAN-L6 §1, binding for L5a by the L5 brief). Everything else (gardens, decorations, leaf families,
`TwistClosed`, the spliced kernel, ladders) is main's, by import.

`Stage1ReductionGateLow` is the low half, in the form glued by `wtPrefix_of_halves`; its consumer (L7) uses it where
main's `nonregular_prefix` uses `Stage1ReductionGate`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open MeasureTheory Set Finset
open scoped Classical

/-! ## The piece (main `Spine/Stage1Interface.lean`, with the `𝒱_γ` subpro choices) -/

/-- Data of one Stage 1 piece over `𝒱_γ`, for width `2R`, over momentum dimension `d` (main's `Stage1PieceD` with
`Cs : Src.SubproChoices γ Gsb`). -/
structure Stage1PieceGD (γ : ℝ) (d R : ℕ) where
  Gsb : Garden (2 * R)
  Cs : FinalCount.Src.SubproChoices γ Gsb
  ladders : SourceMaximalLadderData Gsb
  layer : GBranch Gsb.tree → ℕ
  gapSpecification : (v : GBranch Gsb.tree) → Option (LocalGapSpecification Gsb v)
  /-- `g_sk` (TARGET L1962): incoherency of the attached regular parts and of the vines in `V_0`. -/
  gsk : ℕ
  /-- `b_sk`: the number of bad vines in `V_0`. -/
  bsk : ℕ

/-- A Stage 1 piece over `𝒱_γ` at `γ = P.γ` (it depends on `P` only through `γ, d`, so the piece types of parameter
records differing only in the large constants agree definitionally). -/
abbrev Stage1PieceG (P : WTParams) (R : ℕ) := Stage1PieceGD P.γ P.d R

/-- The spliced kernel data of a piece for given analytic functions `K_(l)`, `K^dagger`, `xi_v` (main's
`Stage1Piece.data`). -/
def Stage1PieceG.data {P : WTParams} {R : ℕ} (π : Stage1PieceG P R) (tt : Fin (2 * R) → ℝ)
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
noncomputable def Stage1PieceGD.gsb {γ : ℝ} {d R : ℕ} (π : Stage1PieceGD γ d R) : ℕ :=
  π.ladders.totalIncoherency π.layer

/-- `bar-g` (TARGET L2237): `g_sk + g_sb`. -/
noncomputable def Stage1PieceGD.gbar {γ : ℝ} {d R : ℕ} (π : Stage1PieceGD γ d R) : ℕ :=
  π.gsk + π.gsb

/-- `bar-rho` (TARGET L2237): `rho_sb + q_sk`. -/
noncomputable def Stage1PieceGD.rbar {γ : ℝ} {d R : ℕ} (π : Stage1PieceGD γ d R) : ℕ :=
  π.Gsb.molecule.rho + π.Cs.hinges.card

/-- The integral conjunct of `Represents` (main's `Stage1Piece.RepresentsInt`, verbatim). -/
def Stage1PieceG.RepresentsInt {P : WTParams} {R : ℕ} (π : Stage1PieceG P R) (n : ℕ)
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

/-- (redvine2)–(redvine3), L1950–L1976, leafwise (main's `Stage1Piece.Represents`, verbatim). -/
def Stage1PieceG.Represents {P : WTParams} {R : ℕ} (π : Stage1PieceG P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (s : ℝ) (val : ℂ) : Prop :=
  val = ∑ LG ∈ members, F.valueSel tt base roots LG (sel LG) ∧ π.RepresentsInt n tt base roots s val

/-- The structural and decorated properties of a piece (main's `Stage1Piece.Sound`), with the conclusions
(1)–(6) of TARGET `subpro` over `𝒱_γ` (`Src.SubproSupport P.γ`, `DV` read as `DV′`). -/
structure Stage1PieceG.Sound {P : WTParams} {R : ℕ} (π : Stage1PieceG P R) (p : ℕ)
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
    splicedGapIndicator π.Gsb (π.data (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ => 0) (fun _ => 0))
      P.L P.γ P.η base z.1 ≠ 0 →
    FinalCount.Src.SubproSupport P.γ π.Gsb π.Cs P.L P.γ P.η base
      (univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex π.Gsb z.1)
  /-- TARGET L2116, C1 half. -/
  hingeOutsideFirst : ∀ v ∈ π.Cs.hinges, ∀ i, ¬ (π.Cs.collection i).IsInterior v
  /-- AMEND7 (R48). -/
  tripleDesignated : π.Cs.TripleDesignated
  /-- AMEND7 (R48). -/
  hingeNoLoop : π.Cs.HingeNoLoop

/-! ## The data, the counts and the gate (main `Spine/Stage1SumBound.lean`, `Spine/Stage1Gate.lean`) -/

/-- All pieces of one instance of the sum (a)/(b), with their values (main's `Stage1Data`). -/
structure Stage1DataG (P : WTParams) (R : ℕ) where
  Pc : Type
  fin : Fintype Pc
  piece : Pc → Stage1PieceG P R
  val : Pc → ℂ

set_option linter.unusedVariables false in
/-- Row 10 (AMEND10, R56): the piece counts of TARGET (finalprooffin), L2241–L2252 (main's `Stage1Counts`; the
classes `Cl`, `cls` are kept only for `Stage1Partition`). -/
def Stage1CountsG (C₀ : ℕ) (P : WTParams) (R N : ℕ) (S : Stage1DataG P R) (Cl : Type) (hCl : Fintype Cl)
    (cls : S.Pc → Cl) : Prop :=
  (∀ π, 1 ≤ (S.piece π).rbar ∧ (S.piece π).rbar ≤ N) ∧ (∀ π, (S.piece π).gbar ≤ N) ∧
  ∀ g r, ((((@univ S.Pc S.fin).filter fun π => (S.piece π).gbar = g ∧ (S.piece π).rbar = r).card : ℕ) : ℝ) ≤
      (3 : ℝ) ^ N * (C₀ : ℝ) ^ N * (((C₀ * r).factorial : ℕ) : ℝ) * (((C₀ * R).factorial : ℕ) : ℝ) * P.C₂ ^ (g + r)

/-- **The Stage 1 reduction at `P` over `𝒱_γ`** (main's `Stage1ReductionAt` verbatim, with the pieces
`Stage1PieceG P R`). -/
def Stage1ReductionGammaAt (C₀ : ℕ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A : Finset (LayeredGarden (2 * R)), (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →
  ∀ tt : Fin (2 * R) → ℝ, (∀ j, tt j ∈ Icc (p : ℝ) (p + 1)) →
  ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∃ (S : Stage1DataG P R) (Cl : Type) (hCl : Fintype Cl) (cls : S.Pc → Cl)
    (members : Cl → Finset (LayeredGarden (2 * R)))
    (sel : S.Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop),
    Stage1Partition roots A members cls sel ∧
    (∀ π, (S.piece π).Represents N tt base roots (members (cls π)) (sel π) U.toLF s (S.val π)) ∧
    (∀ π, (S.piece π).Sound p base roots) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧
    Stage1CountsG C₀ P R N S Cl hCl cls

/-- **The Stage 1 reduction gate for `0 < γ ≤ 1/2`** over `𝒱_γ` (rows 7–10 of the spine; main's
`Stage1ReductionGate` in the low-half form), with a class-count constant `C₀ ≥ 2` depending only on `(d, γ)`. -/
abbrev Stage1ReductionGateLow : Prop :=
  ∃ C₀ : ℕ → ℝ → ℕ, (∀ d γ, 2 ≤ C₀ d γ) ∧
    WTPrefix (fun P => P.γ ≤ 1 / 2 → Stage1ReductionGammaAt (C₀ P.d P.γ) P)

/-! ## Large-constant monotonicity (main `Spine/Stage1GateMonotone.lean`) -/

theorem RepresentsInt_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hL : 0 ≤ P.L) (π : Stage1PieceG P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : 0 ≤ s)
    (val : ℂ) (h : π.RepresentsInt n tt base roots s val) :
    Stage1PieceG.RepresentsInt (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π n tt base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, ?_, hD⟩
  refine hwb.trans ?_
  have hsq : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hLp : 0 ≤ P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) := Real.rpow_nonneg hL _
  have hpow : (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) :=
    pow_le_pow_left₀ (mul_nonneg h0 hsq) (mul_le_mul_of_nonneg_right hc hsq) _
  have hpow2 : P.C₁ ^ (π.Gsb.order + 2 * R) ≤ c₁ ^ (π.Gsb.order + 2 * R) := pow_le_pow_left₀ h0 hc _
  have hB : 0 ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) := pow_nonneg (mul_nonneg (h0.trans hc) hsq) _
  have hC : 0 ≤ P.C₁ ^ (π.Gsb.order + 2 * R) := pow_nonneg h0 _
  have hAC := mul_le_mul hpow hpow2 hC hB
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hLp) hs

theorem Represents_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hL : 0 ≤ P.L) (π : Stage1PieceG P R) (n : ℕ) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (s : ℝ) (hs : 0 ≤ s)
    (val : ℂ) (h : π.Represents n tt base roots members sel F s val) :
    Stage1PieceG.Represents (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π n tt base roots members sel F s
      val :=
  ⟨h.1, RepresentsInt_largeConstants c₁ c₂ hc h0 hL π n tt base roots s hs val h.2⟩

theorem Sound_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (π : Stage1PieceG P R) (p : ℕ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : π.Sound p base roots) :
    Stage1PieceG.Sound (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π p base roots :=
  { plain := h.plain, irreducible := h.irreducible, balanced := h.balanced, order_pos := h.order_pos,
    order_le := by rw [N_largeConstants]; exact h.order_le, layer_le := h.layer_le,
    molecule := h.molecule, connected := h.connected, atom_count := h.atom_count,
    bond_count := h.bond_count, structural := h.structural, support := h.support,
    hingeOutsideFirst := h.hingeOutsideFirst,
    tripleDesignated := h.tripleDesignated,
    hingeNoLoop := h.hingeNoLoop }

/-- Large-constant monotonicity of `Stage1ReductionGammaAt` (as main's `stage1ReductionAt_largeConstantMonotone`). -/
theorem stage1ReductionGammaAt_largeConstantMonotone (C₀ : ℕ) :
    LargeConstantMonotone (Stage1ReductionGammaAt C₀) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hb hsize
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hN
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcounts⟩ := h p hp R hR hRmax N hN1 hN A
    (fun LG hLG => stage1Carries_largeConstants c₁ c₂ LG (hA LG hLG)) hcl tt htt base roots U s hs0 hb hsize
  refine ⟨⟨S.Pc, S.fin, S.piece, S.val⟩, Cl, hCl, cls, members, sel, hpart, ?_, ?_, hord, ?_⟩
  · intro π
    exact Represents_largeConstants c₁ c₂ h₁ (by linarith) (by linarith) (S.piece π) N tt base roots
      (members (cls π)) (sel π) U.toLF s hs0.le (S.val π) (hrep π)
  · intro π
    exact Sound_largeConstants c₁ c₂ (S.piece π) p base roots (hsound π)
  · obtain ⟨hr, hg, hcnt⟩ := hcounts
    refine ⟨hr, hg, ?_⟩
    intro g r
    refine (hcnt g r).trans ?_
    have hC₂0 : 0 ≤ P.C₂ := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC₂0 h₂ _) (by positivity)

/-- Large-constant monotonicity of the low-half body (as L6's `finalCountLow_largeConstantMonotone`). -/
theorem stage1ReductionLow_largeConstantMonotone (C₀ : ℕ → ℝ → ℕ) :
    LargeConstantMonotone (fun P => P.γ ≤ 1 / 2 → Stage1ReductionGammaAt (C₀ P.d P.γ) P) :=
  fun P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ =>
    stage1ReductionGammaAt_largeConstantMonotone (C₀ P.d P.γ) P c₁ c₂ hC hC₂ hδ hL h₁ h₂ (h hγ)

end WaveTurbulence.GammaLow.Fama
