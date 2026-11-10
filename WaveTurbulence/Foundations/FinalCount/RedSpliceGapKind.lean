/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceGap
public import WaveTurbulence.Foundations.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a), R25: the gap kind of the specified pair equals that of the designated object

`gapSpecification_gapKind_eq`: for each group `S` of `𝒞`, on a decoration `κ` of the ORIGINAL garden with the source
conservation (a `(c_v)`-decoration with `c_v = 0` at the atoms of degree four), the gap kind of the specified pair of
`gapSpecification` (computed from the labels `κ ∘ od` of `G_sb`) is the gap kind of the designated object
`designatedObject G S`.  Cases (R25(b)):
1. non-hinge joint: the pair is inside the designated object (`obj_pair_gapKind`);
2. hinge with a skipped vine `A`: the pair is a pair of `A` at a joint, the flow of the ingredient equals the flow of
   the chain (`pair_norm_ingredient`);
3. whole-group unit: the external out/in pair at the degree-four joint has gap `-(internal gap)`
   (`ext_pair_norm'`, charge `0` at degree-four atoms).
The gap kind depends only on the norm (`gapKind_eq_of_norm_eq`).  Hence, together with `object_hasGapKind_unique`
(one object, one kind), the indicator factor of the group in `splicedGapIndicator` is `[kind of the object = σ S]`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Mole TTree WaveTurbulence.Stage1 WaveTurbulence.LGSpine
  WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

theorem kvec_cons {M : Molecule V D} (L : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0) :
    (∀ x, Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x) ∧
    (∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x = 0) :=
  ⟨fun x => by simp only [Molecule.kvec, hκ.1 x], fun v hv hd => (hκ.2 v hv).trans (hc0 v hv hd)⟩

/-- **Case 1.** An out/in pair of darts inside an object, at one of its joints, has the gap kind of the object. -/
theorem obj_pair_gapKind (M : Molecule V D) (hM : M.IsMolecule) (L γ η : ℝ) (w : Mom d) (c : V → Mom d)
    (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration L w c κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → c v = 0)
    (O : Object M) {k : Molecule.GapKind} (hk : O.HasGapKind L γ η w κ k) {j : V}
    (hj : j = O.upper ∨ j = O.lower) {x y : D} (hx : M.atom x = j) (hy : M.atom y = j)
    (hcx : O.ContainsDart x) (hcy : O.ContainsDart y) (hne : M.out x ≠ M.out y) :
    Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = k := by
  obtain ⟨r, hr, rfl⟩ := hk
  obtain ⟨hk1, hc1⟩ := kvec_cons L w c κ hκ hc0
  unfold VineLikeObject.IsGap at hr
  unfold Object.ContainsDart at hcx hcy
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
    obtain ⟨hk2, hc2⟩ := kvec_cons L w cN (fun z => κ z.1) hκN hcN
    have hn := pair_norm_block' (Mole.eraseBond M e) hN hadj.1 hj (Molecule.kvec L w (fun z => κ z.1)) hk2 hc2
      (x := ⟨x, hcx.1, hcx.2.1⟩) (y := ⟨y, hcy.1, hcy.2.1⟩) hx hy hcx.2.2 hcy.2.2 hne
    exact kind_of_flow_norm (Mole.eraseBond M e) hadj.1 L γ η w (fun z => κ z.1) hr hn

end generic

end WaveTurbulence.RedSplice
