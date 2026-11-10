/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcInd

/-! # P4-W2 (R82 step 3): unit-layer windows of the branches of a block from `DomX`

`win_of_domX`: `DomX R lay Bex t₀ t₁ t₂ u` (the native clock domain with the parent-clock condition dropped at `Bex`) gives the OPEN unit layer window `lay v < u v < lay v + 1`
for every interior branch `v` of the region (`DomX` keeps the window condition at every branch, including those of `Bex`); with the window of the exterior clock `u a` (hypothesis, from `tt ∈ openTop`)
this covers every branch of any sub-block `V ⊆ U`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4

variable {w : ℕ} {G : Garden w}

theorem win_of_domX {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : CLRegionData G U a b) (lay : GBranch G.tree → ℕ)
    (Bex : Finset (GBranch G.tree)) (t0 t1 t2 : ℝ) (u : GBranch G.tree → ℝ) (hD : DomX R lay Bex t0 t1 t2 u)
    (hext : (lay a : ℝ) < u a ∧ u a < lay a + 1) {V : Finset (GBranch G.tree)} (hV : V ⊆ U) :
    ∀ v ∈ V, (lay v : ℝ) < u v ∧ u v < lay v + 1 := by
  intro v hv
  by_cases hva : v = a
  · subst hva; exact hext
  · have hi : v ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨hva, hV hv⟩
    exact ⟨(hD.1 v hi).1, (hD.1 v hi).2.1⟩

end WaveTurbulence.VineEstS5C.P4.W2
