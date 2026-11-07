/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.DepthEnumeration
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalFactors

/-! # Garden internal-node ordering for sumint hypothesis (ii) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed

/-- Interior nodes can be numbered with every actual branching child before
its parent, as required by the triangular predecessor identities. -/
theorem exists_clInternalEnumeration {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (R : CLRegionData G U a b) :
    ∃ e : ↥(clInteriorBranches R) ≃ Fin (clLocalOrder1 R),
      ∀ v u : ↥(clInteriorBranches R), ∀ i : Fin 3,
        u.1.toNode = v.1.child i → e u < e v := by
  classical
  obtain ⟨e,he⟩ := exists_depth_enumeration ↥(clInteriorBranches R) (fun v => v.1.1.2.length)
  have hc : Fintype.card ↥(clInteriorBranches R) = clLocalOrder1 R := Fintype.card_coe _
  refine ⟨e.trans (finCongr hc),?_⟩
  intro v u i hi
  have hp := congrArg (fun x : GNode G.tree => x.1.2) hi
  change u.1.1.2 = v.1.1.2++[i] at hp
  have hd : v.1.1.2.length < u.1.1.2.length := by
    rw [hp,List.length_append,List.length_singleton]
    omega
  exact he v u hd

end WaveTurbulence.VineEstS2
