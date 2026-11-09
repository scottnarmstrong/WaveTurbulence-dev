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
public import WaveTurbulence.Foundations.GammaLow.Flower.Stage1MK.P16
public import WaveTurbulence.Foundations.FinalCount.AsmVN13
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.FinalCount.RedSpliceSkipMK
public import WaveTurbulence.Foundations.FinalCount.SubproGap2
public import WaveTurbulence.Foundations.FinalCount.SubproObjMap
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.SubproGap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Pairs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Low
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-! # FLOWER-LOW (packet L8), item I (wave 17): the B4 layer of the marked Stage 1′ over `𝒱_γ`

The declarations on the path of main's `Stage1MKGate.stage1ReductionAtMKFull_of_B3s` (B4) not yet ported: L8's own (Stage1MKGate, MkSubpro,
Geometry *MK, Vine.A *MK) and the Stage-1 helpers that L6's H port has only at `Src.γL` (`FinalCount.S1Exists`,
`S1Overlap`, `S1Vinechain`, `S1Erase`, `S1Split`, `SubproObjMap`, `SubproGap2`, `AsmVN13`, `RedSpliceGapKind`), here
at the family `P.γ`/`γF`; copied by source (sha256 in COPIED-SHA256SUMS) by `tools/itool/gen_i_spec.py`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false

namespace WaveTurbulence.GammaLow.Flower

section
open WaveTurbulence.FinalCountAsm
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
open Finset Classical
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- The molecule-level single-vine classification of an object: an ordinary vine, resp. the adjoint of the designated bond is a vine. -/
def ObjVineLow {V : Type} [DecidableEq V] {D : Type} [Fintype D] [DecidableEq D] (M : Molecule V D) (U : Src.Object γF M) : Prop :=
  match U.shape with
  | .vc _ => Src.IsSomeVine γF M U.atoms U.upper U.lower
  | .hyper R => Src.IsSomeVine γF (Molecule.eraseBond M R.added) U.atoms U.upper U.lower

end

section
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]
variable {w : ℕ} {G : Garden w}
variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **Case 1.** An out/in pair of darts inside an object, at one of its joints, has the gap kind of the object. -/
theorem obj_pair_gapKindLow (M : Molecule V D) (hM : M.IsMolecule) (L γ η : ℝ) (w : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    (O : Src.Object γF M) {k : Molecule.GapKind} (hk : O.HasGapKind L γ η w κ k) {j : V}
    (hj : j = O.upper ∨ j = O.lower) {x y : D} (hx : M.atom x = j) (hy : M.atom y = j)
    (hcx : O.ContainsDart x) (hcy : O.ContainsDart y) (hne : M.out x ≠ M.out y) :
    Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = k := by
  obtain ⟨r, hr, rfl⟩ := hk
  obtain ⟨hk1, hc1⟩ := RedSplice.kvec_cons L w c κ hκ hc0
  unfold Src.VineLikeObject.IsGap at hr
  unfold Src.Object.ContainsDart at hcx hcy
  cases hs : O.shape with
  | vc hv =>
    rw [hs] at hr hcx hcy
    have hn := pair_norm_block' M hM hv.1 hj (Molecule.kvec L w κ) hk1 hc1 hx hy hcx hcy hne
    exact kind_of_flow_norm M hv.1 L γ η w κ hr hn
  | hyper R =>
    rw [hs] at hr hcx hcy
    obtain ⟨e, he, hadj⟩ := R
    have hne' := Vine.ends_distinct_of_pair M e he hadj.1.2.2.2.1
    have hN := Vine.eraseBond_isMolecule M hM e hne'
    obtain ⟨cN, hκN, hcN⟩ := Vine.eraseBond_decoration_exists M hM e hne' L w c κ hκ hc0
    obtain ⟨hk2, hc2⟩ := RedSplice.kvec_cons L w cN (fun z => κ z.1) hκN hcN
    have hn := pair_norm_block' (Mole.eraseBond M e) hN hadj.1 hj (Molecule.kvec L w (fun z => κ z.1)) hk2 hc2
      (x := ⟨x, hcx.1, hcx.2.1⟩) (y := ⟨y, hcy.1, hcy.2.1⟩) hx hy hcx.2.2 hcy.2.2 hne
    exact kind_of_flow_norm (Mole.eraseBond M e) hadj.1 L γ η w (fun z => κ z.1) hr hn

end

section
open WaveTurbulence.Subpro
open WaveTurbulence.Induct
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
open WaveTurbulence.GammaLow.FinalCount
variable {γF : ℝ} [Fact (γF ≤ 1 / 2)] [Fact Fama.TVineF1Input] [Fact Fama.VinechainlemPrimeInput] [Fact Fama.TVineIsoInvariant]

/-- An object with an opposite pair of darts inside it at one of its joints whose gap has kind `k` has gap kind `k`
(needs conservation of the decoration at the atoms of degree four). -/
theorem hasGapKind_of_pair_jointLow {w d : ℕ} (G' : Garden w) (L γ η : ℝ) (base : Mom d)
    (c : GBranch G'.tree → Mom d) (κ : GardenDart G' → (Fin d → ℤ))
    (hκ : G'.molecule.IsDecoration L base c κ) (hc0 : ∀ v ∈ G'.molecule.atoms, G'.molecule.deg v = 4 → c v = 0)
    (O : Src.Object γF G'.molecule) {j : GBranch G'.tree} (hj : j = O.upper ∨ j = O.lower)
    {x y : GardenDart G'} (hx : G'.molecule.atom x = j) (hy : G'.molecule.atom y = j)
    (hcx : O.ContainsDart x) (hcy : O.ContainsDart y) (hxy : G'.molecule.out x ≠ G'.molecule.out y)
    {k : Molecule.GapKind} (hk : Molecule.gapKind L γ η (Molecule.gapAt L base κ x y) = k) :
    O.HasGapKind L γ η base κ k := by
  obtain ⟨p, q, hT, hp, hq⟩ := Fama.objectJoint_pair O (Or.inl rfl : O.upper = O.upper ∨ O.upper = O.lower)
  have h0 := Fama.hasGapKind_of_pair O L γ η base κ p q hT.1 hT.2.1 hT.2.2.2 hp hq _ rfl
  have := obj_pair_gapKindLow G'.molecule (WaveTurbulence.Mole.garden_isMolecule G') L γ η base c κ hκ hc0 O h0 hj hx hy hcx hcy hxy
  rw [← hk, this]
  exact h0

end

end WaveTurbulence.GammaLow.Flower
