/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.PRedLeaves
public import WaveTurbulence.Foundations.Flower.MkSlots.Data
public import WaveTurbulence.Foundations.Flower.MkUnits.WHinge
public import WaveTurbulence.Foundations.Flower.Stage1WVine.WSlotM1
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core2
public import WaveTurbulence.Foundations.Flower.Stage1W.Frontier
public import WaveTurbulence.Foundations.FlowerTop.Port.S2ST.AnchorFamilyB

/-! # B3s MK-SLOTS (integration): the isolated analytic input on the cap-couple slots

The skeleton reduction of a capped member (`kernelLeaves_skeleton_reduction_selNWF`) attaches to every skeleton leaf
pair `q` a pinned weighted slot kernel `slotFnNWF … (.inl q)`. When one leaf of `q` is the root of a cap tree
(`IsCapPair`), the native object of `q` is the cap couple (trivial, or D2b's type-2 couple `(X.plug 1 leaf, leaf)`
whose lone leaf is the capped flower), its profile at the cap pair is `1` (anchored, `S2ST.typeProfilesAnchB`), it
may carry the pin of the capped flower parent (`fixCap … plain`) and the dagger weights of that parent (sibling
indicators and the node-local pieces of the removed phase, `dagNodeW`). Such a slot is evaluated at ONE momentum only
(the label of the cap root), so only its value at that momentum matters; in the chain the anchored profile `1` is
replaced by the indicator of that momentum (`anchProfiles`; summable over the lattice, equal on every decoration).

`CapSlotObligation` is the single analytic input of the integration on these slots: for every cap pair slot of the
reconstruction of a prescribed point, the function `ts ↦ capSlotKer … ts x₀` (`x₀` the label of the cap root) has,
on the slot box, a superposition of Fourier modes with `SlotFam`-compatible amplitudes (bounded by `1`,
`SNorm (30 d) 0 ≤ 1`, centred within distance `1` of a lattice point), whose mass is the B3 slot mass
(`K · (C√δ)^{size} · L^{-η⁸·incoh} · c_F^{nr} · leaf`, the leaf factor without the anchored cap pair,
`b⁻¹ · slotLeaf`) times the protected loss `L^{31d+6}`, uniformly in the parameters, on the parameter prefix.

It is to be proved from D3's `ProtPin.protBoundNTGate` (`ProtPin/NTGate.lean`; the `θ = η` bound with the loss
`L^{31d+6}`, configuration `none` for a trivial cap couple and `term` for a type-2 cap couple), D2c's
`ProtCut.CapData.kernelProt_cap` (a cap couple kernel is the paired-tree kernel times one profile), D6b's
`ProtWhole.CapG` (the frozen kernel of a width-2 cap component), D2b's `ProtGeo` (`embeds_stem_cap`,
`protShape_objTree`, `protAmbient_objTree`, `objCfg`: the native object at a cap pair is `objCpl`, its pins are
`fixCap`), main's `LFTwist.reconstruction_coupleEmb` (the native couple of a skeleton pair is embedded in the
reconstruction), and `MkSlots.protSlotSupM` (an X-norm bounded continuous slot function is a superposition).

* `IsCapPair`, `capTreeOf`, `anchProfiles`, `dagNodeW` (node-local dagger weight), `capNodeW` (frontier × dagger
  node weight), `capSlotKer` (the pinned cap slot kernel of the reconstruction of a prescribed point);
* **`CapSlotObligationAt Kc P`**, **`CapSlotObligation`** (`∃ Kc ≥ 1, WTPrefix (CapSlotObligationAt Kc)`);
* `capSlotObligationAt_mono`: large-constant monotonicity (for `prefix_and`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ}

/-- A cap pair: a leaf pair of a skeleton one of whose leaves lies in a cap tree (a cap tree is a single leaf, so that
leaf is the cap root). -/
def IsCapPair (S : Garden w) (hS : S.IsPlain) (J : Finset (Fin w)) (q : SourcePair S) : Prop :=
  (q.firstLeaf hS).1.1 ∈ J ∨ (q.secondLeaf hS).1.1 ∈ J

/-- The phase scale of a capped flower parent `b` in the removed phase `offFactor`
(`exp(-i θ_b ω_b)`, `θ_b = π·sign(b)·δ·L^{2γ}·s`). -/
def capTheta (L γ δ s : ℝ) (G : Garden w) (b : GBranch G.tree) : ℝ :=
  Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * s

/-- The sign of child `i` in the resonance factor `‖k₀‖² - ‖k₁‖² + ‖k₂‖² - ‖k‖²`. -/
def childSign (i : Fin 3) : ℝ := if i = 1 then -1 else 1

/-- **The node-local dagger weight** at a node `z` (momentum `x`), for the prescribed sibling momenta `cc`:
* if `z` is a capped flower parent `b`: the factor `exp(+i θ_b ‖x‖²)` of its removed phase;
* if `z` is child `i` of a capped flower parent `b`: the factor `exp(-i θ_b ε_i ‖x‖²)` of the removed phase of `b`,
  times the sibling indicator `[x = cc b.1.1 i]` unless `z` is the capped flower.
The product over all nodes is `offCap`'s removed-phase factor times `sibWeightCap` (pointwise). -/
def dagNodeW (L γ δ s : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w))
    (dag : Option (Fin w → Fin 3 → Mom d)) (z : GNode LG.garden.tree) (x : Mom d) : ℂ :=
  dag.elim 1 fun cc =>
    (if hb : ∃ b : GBranch LG.garden.tree, b.toNode = z ∧ IsCapFlowerParent LG J b then
      Complex.exp (((capTheta L γ δ s LG.garden hb.choose * ‖x‖ ^ 2 : ℝ) : ℂ) * Complex.I) else 1) *
    (if hc : ∃ (b : GBranch LG.garden.tree) (i : Fin 3), b.child i = z ∧ IsCapFlowerParent LG J b then
      Complex.exp (((-(capTheta L γ δ s LG.garden hc.choose * childSign hc.choose_spec.choose * ‖x‖ ^ 2) : ℝ) : ℂ) *
          Complex.I) *
        (if (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = z) then 1 else
          if x = cc hc.choose.1.1 hc.choose_spec.choose then 1 else 0)
    else 1)

/-- The node weight of the capped integrand on a garden: the frontier weight (`fwNode`, scales `Rf`) times the
node-local dagger weight. -/
def capNodeW (L γ δ : ℝ) (p : ℕ) (s : ℝ) (LG : LayeredGarden w) (J : Finset (Fin w)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (z : GNode LG.garden.tree) (x : Mom d) : ℂ :=
  fwNode LG p (fun j => frontierG (Rf j)) z x * dagNodeW L γ δ s LG J dag z x

/-- **The anchored leaf profiles** used in the chain: S2-ST's `typeProfilesAnchB` with the anchored profile `1` replaced
by the indicator of the cap momentum `latticePoint L (roots j)` (`j` the cap tree of the pair). On every decoration
at coset base `0` an anchored input leaf carries exactly that momentum (the cap tree is a single leaf, paired leaves
carry equal labels, the root label is `roots j`), so the class value is unchanged; unlike `1`, the indicator is
summable over the lattice. -/
def anchProfiles (J : Finset (Fin w)) (LG : LayeredGarden w) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (L : ℝ)
    (roots : Fin w → (Fin d → ℤ)) : LeafProfiles w d := fun a =>
  if (pairTrees LG.garden a).1 ∈ J then
    (fun x => if x = latticePoint L (roots (pairTrees LG.garden a).1) then 1 else 0)
  else if (pairTrees LG.garden a).2 ∈ J then
    (fun x => if x = latticePoint L (roots (pairTrees LG.garden a).2) then 1 else 0)
  else typeProfiles LG h a

/-- The cap tree of a cap pair (the tree of its first leaf if that is a cap tree, else of its second leaf). -/
def capTreeOf (S : Garden w) (hS : S.IsPlain) (J : Finset (Fin w)) (q : SourcePair S) : Fin w :=
  if (q.firstLeaf hS).1.1 ∈ J then (q.firstLeaf hS).1.1 else (q.secondLeaf hS).1.1

/-- The reconstruction of a prescribed point at its source layering (it is `a.layered`, `sourceLayer_reconstructs`). -/
abbrev recLG (a : PrescribedPrimeGarden w) : LayeredGarden w :=
  layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)

end WaveTurbulence.Flower.MkSlots
