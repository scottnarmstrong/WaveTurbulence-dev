/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceTriple
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): hinge atoms, inherited pre-layering, triple-bond clause

TARGET L1953-L1976, DH23 Prop 9.1 (2).  The hinge atoms of `𝒢_sb` are the merged atoms (the crowns of the
spliced blocks), i.e. the atoms of `G_sb` whose old name lies in a merged class.  The pre-layering is
inherited through the old-name map: every node of the spliced garden, including the crown and the three
new children, lies in the layer it had before splicing (TARGET L1958).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {w : ℕ} {G0 : Garden w}

/-- The hinge atoms: the merged (crown) atoms of the spliced garden. -/
@[expose] noncomputable def SpState.hinges (st : SpState G0) : Finset (GBranch st.G.tree) := by
  classical exact Finset.univ.filter (fun c => st.cls (st.M.ob c) ≠ none)

theorem SpState.mem_hinges (st : SpState G0) (c : GBranch st.G.tree) :
    c ∈ st.hinges ↔ st.cls (st.M.ob c) ≠ none := by
  classical simp [SpState.hinges]

/-- The inherited pre-layering (TARGET L1958). -/
@[expose] def SpState.layer (st : SpState G0) (layer0 : GBranch G0.tree → ℕ) :
    GBranch st.G.tree → ℕ := fun c => layer0 (st.M.ob c)

theorem SpState.layer_le (st : SpState G0) (layer0 : GBranch G0.tree → ℕ) {p : ℕ}
    (h : ∀ v, layer0 v ≤ p) : ∀ c, st.layer layer0 c ≤ p := fun c => h _

/-- Every triple bond of `M(G_sb)` has a hinge endpoint, provided `M(G_sk)` has no triple bond. -/
theorem SpState.triple_hinge (st : SpState G0) (hno : ∀ a b, G0.molecule.bondsBetween a b ≠ 3)
    (a b : GBranch st.G.tree) (h : st.G.molecule.bondsBetween a b = 3) : a ∈ st.hinges ∨ b ∈ st.hinges := by
  by_contra hn
  push_neg at hn
  have ha : st.cls (st.M.ob a) = none := by
    by_contra h'; exact hn.1 ((st.mem_hinges a).mpr h')
  have hb : st.cls (st.M.ob b) = none := by
    by_contra h'; exact hn.2 ((st.mem_hinges b).mpr h')
  exact hno _ _ ((st.M.bondsBetween_eq st.hcls ha hb).symm.trans h)

end WaveTurbulence.RedSplice
