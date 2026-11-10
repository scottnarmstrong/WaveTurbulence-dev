/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FinalCount.RedSpliceInduced
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHinge
import Mathlib.Tactic

/-!
# REDSPLICE-DEF (S2a): residual atomic groups of a splice are induced-isomorphic to the original ones

Let `B` be an atomic group of `G0` (e.g. an ingredient vine of a group of `𝒞` that was not spliced) and
let some spliced classes meet `B`.  Its residual group in the spliced garden is the image `π''B` under the
representative map `π v = ` (the atom of `G` whose old name is `repC v`).  If
* (H1) distinct atoms of `B` have distinct representatives,
* (H2) no dart of `B` is internal to a merged class,
* (H3) every dart of `G` between two atoms of `π''B` comes from a dart of `B` (no new bonds),
then `B` and `π''B` are isomorphic induced subgraphs, so blocks and vines transport (`InducedIso`).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.RedSplice
open TTree Finset WaveTurbulence WaveTurbulence.Mole SpMap

variable {w : ℕ} {G0 G : Garden w} {cls : GBranch G0.tree → Option (GBranch G0.tree)}

/-- The representative of an old atom in the spliced garden. -/
noncomputable def SpMap.pi (M : SpMap G0 G cls) (hcls : ClsOK cls) (v : GBranch G0.tree) : GBranch G.tree :=
  (M.repC_mem_range hcls v).choose

theorem SpMap.ob_pi (M : SpMap G0 G cls) (hcls : ClsOK cls) (v : GBranch G0.tree) :
    M.ob (M.pi hcls v) = repC cls v := (M.repC_mem_range hcls v).choose_spec

end WaveTurbulence.RedSplice
