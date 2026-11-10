/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Gate
public import WaveTurbulence.Foundations.Spine.SourceSplicedBounds
public import WaveTurbulence.Foundations.LayerCnt.Unconditional
/-! # Exported statements of packet L5c (FAMILY-γ: SourceVine objects, CoarseSpliced′, layervine′, subpro′)

All statements are over the vine family `𝒱_γ` of ruling D11 (`Molecule.IsVineGamma`, `TVine/Defs.lean`), through
L6's `𝒱_γ` source carrier `FinalCount.Src` (binding: no second carrier is defined here).

* **CoarseSpliced′** (TARGET finalsbest1, L2075–L2077). Main's `LGSpine.CoarseSplicedAt` is family-specific only
  through the premise `SplicedSourcePremises.subpro` (main's `SourceVine.SubproChoices`); main's proof
  (`CoarseSpliced.coarse_fixed`) never uses that field. `CoarseSplicedCoreAt` is the statement with the family-free
  premises subpro(1) only; `CoarseSplicedGammaAt` is main's statement with the `𝒱_γ` premises
  (`Src.SubproChoices P.γ`, `Src.SubproSupport P.γ`). The core implies both main's and the `𝒱_γ` statement.
* **The counting cover over `𝒱_γ`** (TARGET finalsbest2, L2078, from finalcount1 and ladderl1old through the counting
  cover of L2097–L2116). `SubproConclusionsGamma` is main's `Cover.SubproConclusions` over `Src`;
  `FineSplicedChoicesGammaAt` is the conclusion of main's `Cover.fine_spliced_of_subpro_choices` for `𝒱_γ` choice
  data. Its proof produces the counting choices in `Src.CountingChoices P.γ G P.d` (with `Src.CountingGeometry` and
  `Src.splicedCountingAdmissible`) and consumes L6's `FinalCountGammaAt`.
* **layervine′** (TARGET Prop `layervine`, L1513–L1532) for T-vines, with the groups of TARGET Def `cohmol` read as
  the non-joint pieces (`Molecule.tvineGroups`, D11; N3 §1.3, Theorem 6). Bad vines (I), (II) are the same in both
  families and keep main's `LayerCnt.layervine_bound` / `layervine_improved`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.Induct WaveTurbulence.LGSpine
open Set Finset
open scoped ENNReal

/-! ## CoarseSpliced′ (TARGET finalsbest1, L2075–L2077) -/

/-- TARGET finalsbest1 with only the family-free premises subpro(1) (connected molecule, `n_sb` atoms,
`2 n_sb − R` bonds). The vine family plays no role in TARGET's proof of (finalsbest1) (L2079–L2083). -/
abbrev CoarseSplicedCoreAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (A : SourceMaximalLadderData G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    G.molecule.IsMolecule → G.molecule.IsConnected → G.molecule.atoms.card = G.order →
    G.molecule.bonds.card + R = 2 * G.order →
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (P.C₁ * Real.sqrt P.δ) ^ G.order *
        P.L ^ (-P.η * A.totalIncoherency D.layer +
          80 * P.d * (G.molecule.rho + D.hinges.card))

/-- Main's `SplicedSourcePremises` over `𝒱_γ`: subpro(1)–(6) with L6's carrier `Src.SubproChoices P.γ`,
`Src.SubproSupport P.γ` (`DV` read as `DV′`). -/
structure SplicedSourcePremisesGamma {R : ℕ} (P : WTParams) (G : Garden (2 * R))
    (D : SplicedKernelData G P.d) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) : Prop where
  molecule : G.molecule.IsMolecule
  connected : G.molecule.IsConnected
  atom_count : G.molecule.atoms.card = G.order
  bond_count : G.molecule.bonds.card + R = 2 * G.order
  subpro : ∃ C : FinalCount.Src.SubproChoices P.γ G,
    C.Structural ∧ D.hinges = C.hinges ∧
    ∀ z : GenDecoration G P.d roots 0,
      splicedEpsilon G D.hinges z.1 ≠ 0 → splicedGapIndicator G D P.L P.γ P.η base z.1 ≠ 0 →
      FinalCount.Src.SubproSupport P.γ G C P.L P.γ P.η base
        (univ.image (fun i => base + latticePoint P.L (roots i))) (bondIndex G z.1)

/-- **TARGET finalsbest1 over `𝒱_γ`** (L2075–L2077): main's `LGSpine.CoarseSplicedAt` verbatim, with the premises
`SplicedSourcePremisesGamma`. -/
abbrev CoarseSplicedGammaAt (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
  ∀ (A : SourceMaximalLadderData G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedSourcePremisesGamma P G D base roots →
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (P.C₁ * Real.sqrt P.δ) ^ G.order *
        P.L ^ (-P.η * A.totalIncoherency D.layer +
          80 * P.d * (G.molecule.rho + D.hinges.card))

/-- **The coarse gate for `0 < γ ≤ 1/2`** (the low-half form glued by `wtPrefix_of_halves`; L7 uses it where main's
`nonregular_prefix` uses `CoarseSplicedGate`). -/
abbrev CoarseSplicedGateLow : Prop := WTPrefix fun P => P.γ ≤ 1 / 2 → CoarseSplicedGammaAt P

/-! ## The counting cover over `𝒱_γ` (TARGET finalsbest2, L2078, via L2097–L2116) -/

/-- The decorated conclusions of TARGET subpro (L2040–L2051) for given `𝒱_γ` choice data `Cs` (main's
`Cover.SubproConclusions` over `Src`), together with the C1 half of the hinge assertion at L2116. -/
structure SubproConclusionsGamma {d R : ℕ} (γ : ℝ) (G : Garden (2 * R)) (D : SplicedKernelData G d)
    (Cs : FinalCount.Src.SubproChoices γ G) (L γ' η : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) : Prop where
  structural : Cs.Structural
  hinges : D.hinges = Cs.hinges
  support : ∀ z : GenDecoration G d roots 0,
    splicedEpsilon G D.hinges z.1 ≠ 0 → splicedGapIndicator G D L γ' η base z.1 ≠ 0 →
    FinalCount.Src.SubproSupport γ G Cs L γ' η base (univ.image (fun i => base + latticePoint L (roots i)))
      (bondIndex G z.1)
  /-- TARGET L2116, C1 half: no hinge is an interior atom of an object of `C_1`. -/
  hingeOutsideFirst : ∀ v ∈ Cs.hinges, ∀ i, ¬ (Cs.collection i).IsInterior v
  /-- AMEND7 (R48). -/
  tripleDesignated : Cs.TripleDesignated
  /-- AMEND7 (R48). -/
  hingeNoLoop : Cs.HingeNoLoop

/-- **TARGET finalsbest2 (L2078) for the spliced kernel of `𝒱_γ` choice data**: the conclusion of main's
`Cover.fine_spliced_of_subpro_choices`, with `Cs : Src.SubproChoices P.γ G` and `SubproConclusionsGamma`. -/
def FineSplicedChoicesGammaAt (P : WTParams) : Prop :=
  ∀ {p R : ℕ}, p < P.D → 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ D : SplicedKernelData G P.d, SplicedAmplitudeBounds G D → (∀ v, D.layer v ≤ p) →
    G.molecule.IsMolecule → G.molecule.IsConnected → G.molecule.atoms.card = G.order →
    G.molecule.bonds.card + R = 2 * G.order →
  ∀ (Cs : FinalCount.Src.SubproChoices P.γ G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SubproConclusionsGamma P.γ G D Cs P.L P.γ P.η base roots →
    ‖splicedKernel G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))

/-- The numerical side conditions of main's `Cover.fine_spliced_of_subpro_choices`, collected. -/
structure CoverSmall (P : WTParams) : Prop where
  L_ge : 2 ≤ P.L
  delta_pos : 0 < P.δ
  c1_ge : 1 ≤ P.C₁
  delta_le : P.δ ≤ 1
  cap : 2 * P.L⁻¹ ≤ P.L ^ (-P.γ + P.η)
  cap_le : P.L ^ (-P.γ + P.η) ≤ 1
  delta_exp : P.δ ^ (5 * P.ν) ≤ P.η ^ 6
  scale_log : Real.log (Real.log P.L / Real.log 2 + 2) ≤ P.η ^ 6 * Real.log P.L
  count_const : Real.log P.C₁ + Real.log (((3 ^ 16 * 17 : ℕ) : ℝ)) + 5 * P.ν * Real.log P.δ ≤ 0

/-! ## layervine′ (TARGET Prop `layervine`, L1513–L1532) for T-vines -/

section layervine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- TARGET Def `cohmol` (L1489–L1499) for a T-vine, with groups := the non-joint pieces (`Molecule.tvineGroups`, D11;
N3 §1.3): the number of groups whose atoms do not all lie in one layer. -/
noncomputable def tvineIncoherency (M : Molecule V D) (S : Finset V) (a b : V) (layer : V → ℕ) : ℕ := by
  classical
  exact ((M.tvineGroups S a b).filter fun g => ¬ ∀ x ∈ g, ∀ y ∈ g, layer x = layer y).card

end layervine

/-- **TARGET `layervine`, first bound (L1513–L1521), for T-vines** (as main's `LayerCnt.layervine_bound`; N3 Theorem
6(iv): at most three maximal ladders and at most `13` atoms outside them). For a T-vine `(S, a, b)` with `2m + 5` atoms
and incoherency index `g ≤ m + 1`, the weighted layering sum over a family of pre-layerings with values `≤ 𝔇`, pairwise
distinct on `S`, is at most `C_0^m C_2^{g+1}`. -/
def LayervineTVineFirst : Prop :=
  ∀ B : ℝ, 1 ≤ B → ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ {w : ℕ} (G : Garden w) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree),
      G.molecule.IsTVine S a b → ∀ m : ℕ, S.card = 2 * m + 5 →
      ∀ (𝔇 : ℕ) (C₂ : ℝ), C₀ ^ (𝔇 + 1) ≤ C₂ → ∀ g : ℕ, g ≤ m + 1 →
      ∀ 𝓕 : Finset (GBranch G.tree → ℕ),
        (∀ f ∈ 𝓕, LFTwist.IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇) →
        (∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, f x = f' x) → f = f') →
        ∑ f ∈ 𝓕.filter (fun f => tvineIncoherency G.molecule S a b f = g),
            ∏ x ∈ LayerCnt.bondsIn G.molecule S,
              B ^ LayerCnt.dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) ≤
          C₀ ^ m * C₂ ^ (g + 1)

/-- **TARGET `layervine`, improved bound (L1517, L1523–L1531), for (CL) T-vines** (as main's
`LayerCnt.layervine_improved`; N3 Theorem 6(ii),(iii): spine and pendant). For coherent pre-layerings (index `0`)
satisfying the criterion `canonequiv` on the vine region, with `f a = q`, `f b = q'`, the sum is at most
`C_0^{m + (q − q')}`. -/
def LayervineTVineImproved : Prop :=
  ∀ B : ℝ, 1 ≤ B → ∃ C₀ : ℝ, 1 ≤ C₀ ∧
    ∀ {w : ℕ} (G : Garden w) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree),
      G.molecule.IsTVine S a b → Mole.CLParentPattern G S a b → ∀ m : ℕ, S.card = 2 * m + 5 →
      ∀ (p q q' : ℕ) (𝓕 : Finset (GBranch G.tree → ℕ)),
        (∀ f ∈ 𝓕, LFTwist.IsBranchPrelayering G f) →
        (∀ f ∈ 𝓕, tvineIncoherency G.molecule S a b f = 0) →
        (∀ f ∈ 𝓕, f a = q ∧ f b = q') →
        (∀ f ∈ 𝓕, LayerCnt.CanonPairs G f p (LayerCnt.RegV G S a)) →
        (∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, f x = f' x) → f = f') →
        ∑ f ∈ 𝓕, ∏ x ∈ LayerCnt.bondsIn G.molecule S,
            B ^ LayerCnt.dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) ≤
          C₀ ^ (m + (q - q'))

end WaveTurbulence.GammaLow.Famc
