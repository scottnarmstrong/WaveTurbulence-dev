/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntMass

/-! # B3s MK-SLOTS (integration): the α piece at an arbitrary marked set

B3's chain runs the units of the piece of `a` at a marking function `mkU` with `mkU a.prime = classMk mkF a` only
propositionally (`MkUnits.fixMark_self`). So the assembly works with the α piece at the marked set `mkU a.prime` and
rewrites at the end. `pieceAt … Mk` is the α piece (`AlphaTop.pieceα`) with the marked set `Mk` explicit (`coreAt`,
`protAt`, `fixAt`, `flwAt`, `sibIndAt`); at `Mk = classMk mkF a` it is `pieceα` by `rfl` (this file does not import
`AlphaTop`, so that the integration does not depend on `Statement.lean`); `representsIntMK_pieceAt_congr` transports
a representation along an equality of marked sets. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)

namespace WaveTurbulence.Flower.MkSlots

variable {w : ℕ}

/-- The splice state of `a` at a marked set `Mk`. -/
abbrev stM (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) :=
  stSt a.prime.skeleton a.totalSigma Mk

/-- The core branch of a branch of the spliced garden at `Mk`. -/
def coreAt (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (c : GBranch (stM a Mk).G.tree) : GBranch a.layered.garden.tree :=
  a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes ((stM a Mk).M.ob c)

/-- Protected atoms at `Mk`. -/
def protAt (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) :
    Finset (GBranch (stM a Mk).G.tree) :=
  univ.filter fun c => (coreAt a Mk c).toNode ∈ protI a.layered J pat t s kSel

/-- Pins at `Mk`. -/
def fixAt (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (a : PrescribedPrimeGarden w)
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (c : GBranch (stM a Mk).G.tree) : Option ℝ :=
  fixCap a.layered J pat t s (coreAt a Mk c)

/-- Flower children at `Mk`. -/
def flwAt (J : Finset (Fin w)) (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) :
    GBranch (stM a Mk).G.tree → Fin 3 → Prop :=
  fun c i => ∃ ℓ : GLeaf (stM a Mk).G.tree, ℓ.toNode = c.child i ∧ ((stM a Mk).G.pair ℓ).1.1 ∈ J

/-- The dagger sibling indicator at `Mk`. -/
def sibIndAt {d : ℕ} (J : Finset (Fin w)) (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (dag : Option (Fin w → Fin 3 → Mom d)) (flw : GBranch (stM a Mk).G.tree → Fin 3 → Prop)
    (k : GNode (stM a Mk).G.tree → Mom d) : ℝ :=
  dag.elim 1 fun cc => ∏ c : GBranch (stM a Mk).G.tree,
    if IsCapFlowerParent a.layered J (coreAt a Mk c) then
      ∏ i : Fin 3, (if flw c i then 1 else if k (c.child i) = cc c.1.1 i then 1 else 0) else 1

end WaveTurbulence.Flower.MkSlots
