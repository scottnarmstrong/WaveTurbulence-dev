/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Defs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Bridge
public import WaveTurbulence.Foundations.GammaLow.Flower.Carrier.Gates
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Inputs
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P1
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P2
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P3
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P4
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P6
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P7
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P8
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P9
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P10
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Iface
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P11
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P12
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P13
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P14
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P15
public import WaveTurbulence.Foundations.Flower.MkMark.SigmaCrown
public import WaveTurbulence.Foundations.Flower.MkMarkX.TreeSep
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.FlSepApp
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.ZeroFinal
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr1
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepPr2
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedGroupGap
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VineNormalizedRepSel
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Vine.A.VinePrescribedPoints
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.MkUnits.Ingr
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.Tail.T3A

/-! # FLOWER-LOW (packet L8), item I (wave 16): the marked class-count statement and the zero-vanishing layer

Main's `ClassCount.{MarkAdm, HasPieceDataMk, ClassCountStmtMk}` (`Stage1/Shared/ClassCountStmt`, the marked class count
consumed by I-ORPHANS' `classCount_of_legsMkLow`), `MkMark.SigmaCrown`, `MkMarkX.TreeSep`, `Stage1MKGate.{FlSepApp,
ZeroFinal}` declarations over `𝒱_γ`, copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- The crown gap at the lower joint of any CL block presentation `(U, a, b)` of an ingredient `U` of a group `S ∈ 𝒞`
has the gap kind of `S`. -/
theorem crown_gapKind_of_ingredientLow (hM : G.molecule.IsMolecule) {d : ℕ} (L γ η : ℝ) (base : Mom d)
    (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (LGSpine.bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hz : IsDecoration G z)
    {S U : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) {kind : Molecule.GapKind}
    (hk : Fama.VineA.NormalizedSplice.groupGapKind γF G L γ η base (LGSpine.bondIndex G z) S = kind)
    (hI : Fama.IsIngredientG γF G.molecule S U) {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b)
    (R : RegRed.CLRegionData G U a b) (k₀ : Mom d) :
    Molecule.gapKind L γ η
      (cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative)) = kind := by
  obtain ⟨r, hr, hkr⟩ := ingredient_blockGap_of_groupGapKindLow hM L γ η base c _ hκ hc0 hS hk hI (isBlock_swap hB)
  rcases crown_eq_blockGap R L base k₀ z hz hr with e | e
  · rw [e, hkr]
  · rw [e, Vine.gapKind_neg, hkr]

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **σ-bridge, dart-label form.** Under main's σ-restriction `selDarts σ` on the labels `bondIndex G z`, the crown
gap at the lower joint of every CL block presentation of an ingredient of an SG group is SG. -/
theorem crown_gapKind_SG_of_selDartsLow (hM : G.molecule.IsMolecule) {d : ℕ} (L γ η : ℝ) (base : Mom d)
    (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (LGSpine.bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hz : IsDecoration G z)
    (σ : Fama.VineA.NormalizedSplice.GroupPrescription γF G)
    (hsel : Fama.VineA.NormalizedSplice.selDarts γF σ L γ η base (LGSpine.bondIndex G z))
    {S U : Finset (GBranch G.tree)} (hS : S ∈ Fama.maximalGroupsG γF G.molecule) (hσ : σ ⟨S, hS⟩ = .SG)
    (hI : Fama.IsIngredientG γF G.molecule S U) {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b)
    (R : RegRed.CLRegionData G U a b) (k₀ : Mom d) :
    Molecule.gapKind L γ η
      (cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative)) = .SG :=
  crown_gapKind_of_ingredientLow hM L γ η base c z hκ hc0 hz hS ((hsel ⟨S, hS⟩).trans hσ) hI hB R k₀

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **σ-bridge, `𝒱₀(σ)` form.** Under main's σ-restriction `selOf (ofPrescription σ)` (Stage-1 form), every vine
`𝕍 ∈ vinesV0 G σ` has an SG crown gap at the lower joint of any CL block presentation of its atoms. -/
theorem crown_gapKind_SG_of_vinesV0Low (hM : G.molecule.IsMolecule) {d : ℕ} (L γ η : ℝ) (base : Mom d)
    (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (LGSpine.bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hz : IsDecoration G z)
    (σ : RedSplice.Prescription G)
    (hsel : Fama.VineA.NormalizedSplice.selOf γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base z)
    {V : Fama.CLVineG γF G} (hV : V ∈ Fama.vinesV0 γF G σ) {U : Finset (GBranch G.tree)} (hVU : V.atoms = U)
    {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b) (R : RegRed.CLRegionData G U a b) (k₀ : Mom d) :
    Molecule.gapKind L γ η
      (cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative)) = .SG := by
  obtain ⟨-, S, hS, hI, hσ, -⟩ := hV
  exact crown_gapKind_SG_of_selDartsLow hM L γ η base c z hκ hc0 hz _ hsel hS hσ (hVU ▸ hI) hB R k₀

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMark
open scoped Classical
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}

/-- **σ-bridge, plain-garden form (the export).** For a plain garden `G`, an integer decoration `z` satisfying main's
σ-restriction `selOf (ofPrescription σ) L γ η base z`, and `𝕍 ∈ vinesV0 G σ`: at the lower joint `b` of any CL block
presentation `(U, a, b)` of the atoms of `𝕍`, the crown gap of `k = k₀ + z/L` is SG,
`0 < ‖k(b.child pos) − k(b.child neg)‖ ≤ L^{-γ+η}`. -/
theorem crown_gap_le_of_vinesV0Low (hp : G.IsPlain) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) (σ : RedSplice.Prescription G)
    (hsel : Fama.VineA.NormalizedSplice.selOf γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base z)
    {V : Fama.CLVineG γF G} (hV : V ∈ Fama.vinesV0 γF G σ) {U : Finset (GBranch G.tree)} (hVU : V.atoms = U)
    {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b) (R : RegRed.CLRegionData G U a b) (k₀ : Mom d) :
    cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative) ≠ 0 ∧
      ‖cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative)‖ ≤
        L ^ (-γ + η) := by
  obtain ⟨c, hκ, hc0⟩ := moleculeDecoration_bondIndex hp hL base z hz
  exact norm_le_of_gapKind_SG (crown_gapKind_SG_of_vinesV0Low (Mole.garden_isMolecule G) L γ η base c z hκ hc0 hz σ
    hsel hV hVU hB R k₀)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Flower.FlSep WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.RedSplice
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **Per-tree zero weight under the σ-restriction** (`weight_zero_of_unclean_vinesV0`, `hW` at tree `j₀`). -/
theorem weight_zero_of_unclean_vinesV0_treeLow {LG : LayeredGarden w} (A : VineA.PrimeData LG) (J : Finset (Fin w))
    (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : LG.topOrder p (inflatedBranch A u.lower).1.1 ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 →
      (∀ a : GNode LG.garden.tree, a.1.1 = (inflatedBranch A u.lower).1.1 → LG.IsTopLeaf p a →
        ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (σ : Prescription A.skeleton)
    (hu : ∃ V ∈ Fama.vinesV0 γF A.skeleton σ, V.atoms = u.atoms)
    (hSel : ∀ k, Sel k → ∃ (z : GNode A.skeleton.tree → (Fin d → ℤ)) (k₀ : Mom d), IsDecoration A.skeleton z ∧
      Fama.VineA.NormalizedSplice.selOf γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base z ∧
      skDec A k = cosetDecoration A.skeleton L k₀ z)
    (hθ : ∀ k, Sel k → L ^ (-γ + η) < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  refine weight_zero_of_unclean_tree A J u hun p N r hr0 hU hlay hfl hN W Sel hW ?_
  intro k hk
  obtain ⟨z, k₀, hz, hsel, he⟩ := hSel k hk
  obtain ⟨V, hV, hVU⟩ := hu
  rw [crown_gap_skDec, he]
  exact lt_of_le_of_lt (crown_gap_le_of_vinesV0Low A.prime.1 hL γ η base z hz σ hsel hV hVU u.isBlock
    (VineB.regionOf u) k₀).2 (hθ k hk)

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.MkMarkX
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Flower.FlSep WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.RedSplice
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **Per-tree zero weight, collapsed form** (`weight_zero_of_unclean_collapsed`, `hW` at tree `j₀`). -/
theorem weight_zero_of_unclean_collapsed_treeLow {LG : LayeredGarden w} (A : VineA.PrimeData LG)
    (J : Finset (Fin w)) (u : CLBlock A.skeleton) (hun : ¬ StemCleanAt J A u.atoms u.upper)
    (p N : ℕ) {d : ℕ} (r : ℝ) (hr0 : 0 ≤ r)
    (hU : ∀ ℓ ℓ' : GLeaf LG.garden.tree, ℓ.1.1 = ℓ'.1.1 → IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ = ℓ')
    (hlay : ∀ a, LG.layer a ≤ p) (hfl : ∀ a, IsFlowerNodeF LG (IsCapFlower LG J) a → ¬ LG.layer a < p)
    (hN : LG.topOrder p (inflatedBranch A u.lower).1.1 ≤ N)
    (W : (GNode LG.garden.tree → Mom d) → ℝ) (Sel : (GNode LG.garden.tree → Mom d) → Prop)
    (hW : ∀ k, W k ≠ 0 →
      (∀ a : GNode LG.garden.tree, a.1.1 = (inflatedBranch A u.lower).1.1 → LG.IsTopLeaf p a →
        ¬ IsFlowerNodeF LG (IsCapFlower LG J) a → ‖k a‖ ≤ r) ∧
      (2 * (N : ℝ) + 2) * r ≤ ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 4)
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (σ : Prescription A.skeleton)
    (hu : ∃ V ∈ Fama.vinesV0 γF A.skeleton σ, V.atoms = u.atoms) {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (hSel : ∀ k, Sel k → ∃ (κ : GenDecoration (A.data.garden A.prime.1) d n nfl) (k₀ : Mom d),
      Fama.VineA.NormalizedSplice.selOf γF (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription γF σ) L γ η base
        (collapseGenDecoration A.data A.prime.1 κ).1 ∧
      ∀ x, k x = k₀ + latticePoint L (ofForest A κ.1 x))
    (hθ : ∀ k, Sel k → L ^ (-γ + η) < ‖k (GNode.root LG.garden.tree (inflatedBranch A u.lower).1.1)‖ / 2) :
    ∀ k, IsBranchConsistent k → Sel k → W k = 0 := by
  refine weight_zero_of_unclean_vinesV0_treeLow A J u hun p N r hr0 hU hlay hfl hN W Sel hW hL γ η base σ hu ?_ hθ
  intro k hk
  obtain ⟨κ, k₀, hsel, he⟩ := hSel k hk
  exact ⟨(collapseGenDecoration A.data A.prime.1 κ).1, k₀, (collapseGenDecoration A.data A.prime.1 κ).2.1, hsel,
    skDec_coset_collapse A κ L k₀ k he⟩

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents WaveTurbulence.Stage1
open WaveTurbulence.RedSplice (Prescription vinesV0 mem_vinesV0)
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ}

/-- **The weight vanishes at a stem-unclean point on its selected decorations** (FL-SEP, per tree). -/
theorem markedWt_zero_of_uncleanLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] {R p N : ℕ} {J : Finset (Fin (2 * R))}
    {pat : Fin (2 * R) → FixPat} {kSel : Fin (2 * R) → Option ℕ} (b : Fama.VineA.PrescribedPrimeGarden P.γ (2 * R))
    (hcar : MkCarries P p N b.layered ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ b.layered.garden : Garden 2)) ∧
      b.layered.garden.Irreducible ∧ (∀ j ∈ J, b.layered.garden.tree j = TTree.leaf) ∧ CapGeo b.layered J p ∧
      CapPatValid b.layered J pat p)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ)
    (Rf : Fin (2 * R) → Option ℝ) (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r)
    (hhigh : ((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖)
    (hS : StemDep σ kSel) (hun : ¬ CleanPtLow J b) (hL4 : 4 ≤ P.L) (hηγ : P.η ≤ P.γ)
    (hbig : 8 * ((P.N (p + 1) ^ 4 : ℕ) : ℝ) + 8 ≤ P.L)
    (κ : GenDecoration b.layered.garden P.d roots 0) (hsel : Fama.Represents.selAt P.γ P 0 b.prime b.sigma κ) :
    markedWt P J p kSel h Rf σ Rs dag b.layered (cosetDecoration b.layered.garden P.L 0 κ.1) = 0 := by
  obtain ⟨c, hc, -, hcun⟩ := (not_cleanPt_iffLow J b).mp hun
  have hcap := hcar.2.2.2.2.1
  have hplain : b.layered.garden.IsPlain := hcar.1.1.1
  set u := clBlockOfLow c with hu
  set j₀ := (MkMark.inflatedBranch b.prime u.lower).1.1 with hj₀def
  have hj₀ : j₀ ∉ J := by
    intro hj
    have hb : (MkMark.inflatedBranch b.prime u.lower).1.2 ∈ (b.layered.garden.tree j₀).branching :=
      (MkMark.inflatedBranch b.prime u.lower).2
    rw [hcar.2.2.2.1 j₀ hj] at hb
    exact absurd hb (by simp [TTree.branching])
  obtain ⟨r, hRfr, hhp, hr10⟩ := hhigh hS j₀ hj₀
  have hrL : P.L / 2 ≤ r := hRf j₀ r hRfr
  have hr2 : 2 ≤ r := by linarith
  have hr0 : 0 < r := by linarith
  set N' : ℕ := P.N (p + 1) ^ 4 with hN'
  have hr9 : 8 * (N' : ℝ) + 8 ≤ r ^ 9 := by
    have h8 : (2 : ℝ) ^ 8 ≤ (P.L / 2) ^ 8 := pow_le_pow_left₀ (by norm_num) (by linarith) 8
    have h9 : (P.L / 2) ^ 9 ≤ r ^ 9 := pow_le_pow_left₀ (by linarith) hrL 9
    have hL9 : P.L ≤ (P.L / 2) ^ 9 := by
      rw [pow_succ]
      nlinarith
    linarith
  set k := cosetDecoration b.layered.garden P.L 0 κ.1 with hkdef
  have hdec := isDecoration_cosetDecoration b.layered.garden P.L 0 κ.1 κ.2.1
  have hroot : k (GNode.root b.layered.garden.tree j₀) = latticePoint P.L (roots j₀) := by
    show 0 + latticePoint P.L (κ.1 (GNode.root b.layered.garden.tree j₀)) = _
    rw [zero_add, κ.2.2.1 j₀]
  let W : (GNode b.layered.garden.tree → Mom P.d) → ℝ := fun k' =>
    if k' (GNode.root b.layered.garden.tree j₀) = latticePoint P.L (roots j₀) ∧
        ∀ ℓ : GLeaf b.layered.garden.tree, k' ℓ.toNode = k' (b.layered.garden.pair ℓ).toNode
    then markedWt P J p kSel h Rf σ Rs dag b.layered k' else 0
  have hWk : W k = markedWt P J p kSel h Rf σ Rs dag b.layered k := if_pos ⟨hroot, hdec.2⟩
  rw [← hWk]
  have hN : b.layered.topOrder p j₀ ≤ N' := by
    have := hcar.1.2.1.1 j₀
    simpa using this
  refine weight_zero_of_unclean_collapsed_treeLow b.prime J u hcun p N' r hr0.le
    (fun ℓ ℓ' he h1 h2 => hcap.one_flower ℓ ℓ' h1 h2 he) hcap.layer_le ?_ hN W (fun k' => k' = k) ?_
    (L := P.L) (by linarith) P.γ P.η 0 b.totalSigma ⟨c, hc, rfl⟩ (n := roots) (nfl := 0) ?_ ?_ k hdec.1 rfl
  · -- capped flowers are in layer `p`
    rintro a ⟨ℓ, hℓ, rfl⟩
    have := hcap.stem_layer ℓ.toNode ⟨ℓ, hℓ, rfl, List.prefix_refl _⟩
    omega
  · -- `hW`
    intro k' hk'
    have hcond : k' (GNode.root b.layered.garden.tree j₀) = latticePoint P.L (roots j₀) ∧
        ∀ ℓ : GLeaf b.layered.garden.tree, k' ℓ.toNode = k' (b.layered.garden.pair ℓ).toNode := by
      by_contra hc'
      exact hk' (if_neg hc')
    have hmw : markedWt P J p kSel h Rf σ Rs dag b.layered k' ≠ 0 := by
      have e : W k' = markedWt P J p kSel h Rf σ Rs dag b.layered k' := if_pos hcond
      rwa [e] at hk'
    refine ⟨fun a ha htl hnf => frontier_le_of_markedWt_ne_zero P J p kSel h Rf σ Rs dag k' hplain hcap.layer_le hj₀
      hr0 hRfr hhp hcond.2 hmw a ha htl hnf, ?_⟩
    rw [hcond.1]
    have h10 : r ^ 10 = r * r ^ 9 := by ring
    nlinarith
  · -- `hSel`
    rintro k' rfl
    refine ⟨decCast b.prime κ, 0, ?_, fun x => ?_⟩
    · have e : Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription P.γ b.totalSigma = b.sigma := by
        funext S
        exact dite_eq_left S.2
      have hs' : Fama.VineA.NormalizedSplice.selOf P.γ (Fama.VineA.NormalizedSplice.GroupPrescription.ofPrescription P.γ b.totalSigma) P.L P.γ P.η 0
          (RegRed.collapseGenDecoration b.prime.data b.prime.prime.1 (decCast b.prime κ)).1 := by
        rw [e]
        exact hsel
      exact hs'
    · rw [ofForest_decCast]
      rfl
  · -- `hθ`
    rintro k' rfl
    rw [hroot]
    have h1 : P.L ^ (-P.γ + P.η) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    have h2 : (2 : ℝ) ^ 10 ≤ r ^ 10 := pow_le_pow_left₀ (by norm_num) hr2 10
    linarith

end

section
open WaveTurbulence.Flower
open WaveTurbulence.Flower.Stage1MKGate
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents Set Finset
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- **Zero classes vanish** at parameters with `L ≥ 4`, `η ≤ γ` and `8 N_{p+1}^4 + 8 ≤ L`. -/
theorem zeroVanishAtLow (P : WTParams) [Fact (P.γ ≤ 1 / 2)] (hL4 : 4 ≤ P.L) (hηγ : P.η ≤ P.γ)
    (hbig : ∀ p, p < P.D → 8 * ((P.N (p + 1) ^ 4 : ℕ) : ℝ) + 8 ≤ P.L) : ZeroVanishLow P := by
  intro p hp R hR hRmax N hN1 hNb J pat kSel t ht s hs A hA roots h b Rf σ Rs dag hRf hhigh π hS ⟨a, hra, hna⟩
  unfold classValueLow
  refine Finset.sum_eq_zero fun LG hLG => ?_
  have hLGA : LG ∈ A := (Finset.mem_filter.1 hLG).1
  have hterm : ∀ κ : GenDecoration LG.garden P.d roots 0,
      Fama.Represents.selPMk P.γ p (objKind (2 * R)) A P 0 roots (fineMkLow (γF := P.γ) J pat t s kSel σ) π LG κ →
      markedWt P J p kSel h Rf σ Rs dag LG (cosetDecoration LG.garden P.L 0 κ.1) = 0 := by
    rintro κ ⟨b', hb', hrb', hsel⟩
    subst hb'
    have hrel : Fama.VineA.PrescribedPrimeGarden.Related P.γ (p := p) (kind := objKind (2 * R)) a b' (fineMkLow (γF := P.γ) J pat t s kSel σ) :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hra) hrb'
    have hun' : ¬ CleanPtLow J b' := (notClean_iff_of_relatedLow J pat t s kSel σ hS hrel).mp hna
    exact markedWt_zero_of_uncleanLow P b' (hA _ hLGA) roots h Rf σ Rs dag hRf hhigh hS hun' hL4 hηγ (hbig p hp) κ hsel
  have hz : (∑' κ : GenDecoration LG.garden P.d roots 0,
      if Fama.Represents.selPMk P.γ p (objKind (2 * R)) A P 0 roots (fineMkLow (γF := P.γ) J pat t s kSel σ) π LG κ then
        (epsDec LG.garden κ.1 : ℂ) *
          (markedWt P J p kSel h Rf σ Rs dag LG (cosetDecoration LG.garden P.L 0 κ.1) : ℂ) *
          (∫ τ : {b : GBranch LG.garden.tree // fixCap LG J pat t s b = none} → ℝ,
            (kDomainFix LG (fun _ => t) (fixCap LG J pat t s)).indicator
              (phaseProdOff P.L P.γ P.δ LG.garden (offCap LG J dag.isSome)
                (cosetDecoration LG.garden P.L 0 κ.1))
              (LG.garden.extendFix (fixCap LG J pat t s) τ)) else 0) = 0 := by
    refine (tsum_congr fun κ => ?_).trans tsum_zero
    split_ifs with hk
    · rw [hterm κ hk, Complex.ofReal_zero, mul_zero, zero_mul]
    · rfl
  unfold kernelKgenSel
  rw [hz, mul_zero]

end

end WaveTurbulence.GammaLow.Flower
