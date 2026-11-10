/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineContributingGroups
/-! A choice-free normal form for the actual collection's list of atom supports. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine
open scoped Classical
variable {w : ℕ} {G : Garden w}

/-- Exactly the SG maximal groups which actually contribute a C1 object. -/
noncomputable def contributingGroups (G : Garden w) (σ : Prescription G) : List (Finset (GBranch G.tree)) := by
  classical
  exact (sgGroups G σ).filter (fun S => decide (HasObj G S))

end WaveTurbulence.VineA
