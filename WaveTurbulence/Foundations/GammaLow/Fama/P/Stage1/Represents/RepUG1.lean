/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Represents.RepUG1` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.FinalCount.RedSpliceGapKind
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.UnitBlocks
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Represents.RepUG1
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CL
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.CN
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Coll2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Cover
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Desig
public import WaveTurbulence.Foundations.GammaLow.Fama.P.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Gap
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Group
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVC
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HVCTop2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.HingePair
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.IP
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Ingr
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Marked
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Obj3
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Rev
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Runs
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Skip
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Spine
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Split
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Stage
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.SurvData
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Top
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Units2
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.V0
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.VC
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainFlows
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects


/-!
# S2 REPRESENTS, UnitGap (1): every unit of a group has an external pair of the gap kind of the designated object

`HingeSpec γ G S a p` gives the external pair only for the unit containing the designated joint `a`.  `UnitSpec γ G S u p` is its
inner clause for an arbitrary unit `u`; `exists_unitSpec` produces it for every unit (units are disjoint, so the unit of
`HingeSpec` for `a := u.upper` is `u`), and `unitSpec_gapKind` is the proof of `hingeOrig_gapKind` with `u` general (the
designated joint `a` enters only through `IsDesig`): the gap of the pair `p` has the kind of the designated object.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.Represents
open WaveTurbulence.Represents WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount
  WaveTurbulence.LGSpine.SourceVine WaveTurbulence.RedSplice

variable {w : ℕ} {G : Garden w} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- The external pair of a given unit `u` (the inner clause of `HingeSpec`). -/
def UnitSpec (γ : ℝ) [Fact (γ ≤ 1 / 2)] (G : Garden w) (S : Finset (GBranch G.tree)) (u : CLBlock G) (p : GardenDart G × GardenDart G) : Prop :=
  ∃ j ∈ u.atoms,
    TripleAt G j p.1 p.2 ∧ ¬ G.molecule.InGroup u.atoms p.1 ∧ ¬ G.molecule.InGroup u.atoms p.2 ∧
    (∀ sk, (groupUnitsOf γ G S).skip = some sk → (j = sk.x ∨ j = sk.y) ∧
      G.molecule.atom (G.molecule.mate p.1) ∈ sk.A ∧ G.molecule.atom (G.molecule.mate p.2) ∈ sk.A ∧
      ∀ e, sk.bond = some e → p.1 ≠ e ∧ p.1 ≠ G.molecule.mate e ∧ p.2 ≠ e ∧ p.2 ≠ G.molecule.mate e) ∧
    ((groupUnitsOf γ G S).skip = none → u.atoms = S ∧ (j = u.upper ∨ j = u.lower))

theorem unit_eq_of_mem {S : Finset (GBranch G.tree)} {u u' : CLBlock G} (hu : u ∈ (groupUnitsOf γ G S).units)
    (hu' : u' ∈ (groupUnitsOf γ G S).units) {a : GBranch G.tree} (ha : a ∈ u.atoms) (ha' : a ∈ u'.atoms) : u = u' := by
  by_contra hne
  have : Std.Symm (fun u u' : CLBlock G => Disjoint u.atoms u'.atoms) := ⟨fun _ _ h => h.symm⟩
  have := List.Pairwise.forall (groupUnitsOf γ G S).disj hu hu' hne
  exact Finset.disjoint_left.mp this ha ha'

theorem exists_unitSpec {S : Finset (GBranch G.tree)} {u : CLBlock G} (hu : u ∈ (groupUnitsOf γ G S).units) :
    ∃ p, UnitSpec γ G S u p := by
  obtain ⟨p, hp⟩ := exists_hingeSpec (S := S) (a := u.upper) ⟨u, hu, u.isBlock.2.1⟩
  obtain ⟨u', hu', hau, j, hj, rest⟩ := hp
  have he := unit_eq_of_mem hu hu' u.isBlock.2.1 hau
  subst he
  exact ⟨p, j, hj, rest⟩


end WaveTurbulence.GammaLow.Fama.Represents
