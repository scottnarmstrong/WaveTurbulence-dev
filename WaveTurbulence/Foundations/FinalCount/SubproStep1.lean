/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.SubproSupportA
public import WaveTurbulence.Foundations.Molecule.VineSubsetVCClassification
public import WaveTurbulence.Foundations.Spine.SourceVineObjectBridge
import Mathlib.Tactic

/-!
# SUBPRO (S4): the Step-1 shape of an SG vine outside `C_1` (R21)

From `SubproSupportA.contained` and the universe's `subsetvc_classification` (TARGET Prop `subsetvc`, L2128): an SG object `P` of
ordinary (VC) shape that is outside `C_1` and avoids the hinges is a single vine, or one or two double bonds
(`DoubleChain`), possibly after deleting a bond joining its joints.  (For an object of hyper shape the host `Q` of
`contained` is an atom-set host; TARGET's containment of equal hyper groups also asks for the same designated bond, so the
hyper-hyper equal-atoms case is left to the consumer, see HANDOFF.)
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
set_option linter.unusedSectionVars false
namespace WaveTurbulence.Subpro
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine Finset

/-- **R21 form.** -/
theorem step1_vc_shape {w d : ℕ} (G : Garden w) (C : SubproChoices G) (L γ η : ℝ) (base : Mom d)
    (kFix : Finset (Mom d)) (κ : GardenDart G → (Fin d → ℤ))
    (hs : SubproSupportA G C L γ η base kFix κ)
    (c : GBranch G.tree → Mom d) (hκ : G.molecule.IsDecoration L base c κ)
    (hc : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (P : Object G.molecule) (hP : P.HasGapKind L γ η base κ .SG)
    (hout : ∀ i, ¬ P.atoms ⊆ (C.collection i).atoms) (hdis : Disjoint P.atoms C.hinges)
    (hvc : ∃ h, P.shape = VineLikeObject.vc h) :
    Vine.DoubleChain G.molecule P.atoms P.upper P.lower 1 ∨ Vine.DoubleChain G.molecule P.atoms P.upper P.lower 2 ∨
      G.molecule.IsVine .V P.atoms P.upper P.lower ∨
      ∃ e, G.molecule.ends e = s(P.upper, P.lower) ∧
        (Vine.DoubleChain (Mole.eraseBond G.molecule e) P.atoms P.upper P.lower 2 ∨
          (Mole.eraseBond G.molecule e).IsVine .V P.atoms P.upper P.lower) := by
  obtain ⟨r', hr', hk'⟩ := hP
  have hG := WaveTurbulence.Mole.garden_isMolecule G
  have hrP := (P.shape.toVine_isGap L base κ r').mpr hr'
  rcases hs.contained P ⟨r', hr', hk'⟩ hout hdis with ⟨S, a, b, hDV, hPS, -, -⟩ | ⟨Q, hPQ, hQk, -, -⟩
  · exact Vine.subsetvc_classification G.molecule hG P.shape.toVine hPS L γ η base c κ hκ hc hrP hk' (Or.inl hDV)
  · obtain ⟨r, hr, hkr⟩ : ∃ r, Q.shape.IsGap L base κ r ∧
        (Molecule.gapKind L γ η r = .LG ∨ Molecule.gapKind L γ η r = .ZG) := by
      rcases hQk with ⟨r, hr, hk⟩ | ⟨r, hr, hk⟩
      · exact ⟨r, hr, Or.inl hk⟩
      · exact ⟨r, hr, Or.inr hk⟩
    obtain ⟨h, hs'⟩ := hvc
    have hcont : P.shape.IsContained Q.shape := by
      rw [hs']
      exact hPQ
    exact Vine.subsetvc_classification G.molecule hG P.shape.toVine hPQ L γ η base c κ hκ hc hrP hk'
      (Or.inr ⟨Q.shape.toVine, (P.shape.toVine_isContained Q.shape).mpr hcont,
        r, (Q.shape.toVine_isGap L base _ r).mpr hr, hkr⟩)

end WaveTurbulence.Subpro
