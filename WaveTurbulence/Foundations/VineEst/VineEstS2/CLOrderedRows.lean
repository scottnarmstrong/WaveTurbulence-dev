/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLInteriorPredecessor
public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLeafCount

/-! # Canonical ordering of the actual CL predecessor coefficients -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS2
open TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The default (cardinality) enumeration of the regional pairs; any bijection works. -/
noncomputable def clPairEnumeration (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R) :=
  (Fintype.equivFin _).trans (finCongr ((Fintype.card_coe _).trans (card_clRegionalPairs hU R hG)))

/-- An enumeration of the interior branches that is increasing along the interior predecessor relation. -/
structure CLIntOrder (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) where
  e : ↥(clInteriorBranches R) ≃ Fin (clLocalOrder1 R)
  prev : ∀ (v u : ↥(clInteriorBranches R)), clInteriorPredecessor hU R v = some u → e u < e v

/-- The default predecessor-monotone enumeration (an arbitrary choice). -/
noncomputable def clInteriorEnumeration (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) :
    CLIntOrder hU R :=
  ⟨(exists_clInteriorPredecessor_order hU R).choose, (exists_clInteriorPredecessor_order hU R).choose_spec⟩

noncomputable def clOrderedPrev (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (Ei : CLIntOrder hU R)
    (v : Fin (clLocalOrder1 R)) : Option (Fin (clLocalOrder1 R)) :=
  (clInteriorPredecessor hU R (Ei.e.symm v)).map Ei.e

theorem clOrderedPrev_lt (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (Ei : CLIntOrder hU R)
    (v u : Fin (clLocalOrder1 R)) (hu : clOrderedPrev hU R Ei v = some u) : u < v := by
  obtain ⟨z,hz,rfl⟩ := Option.map_eq_some_iff.mp hu
  simpa only [Equiv.apply_symm_apply] using
    Ei.prev (Ei.e.symm v) z hz

noncomputable def clOrderedCoeff (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (v : Fin (clLocalOrder1 R)) : Fin (clLocalOrder1 R) ⊕ Fin 4 → ℤ
  | .inl p => clOriginCoeff hU R hG
      (clPredecessorSupport R (clInteriorCrop hU R (Ei.e.symm v)))
      (clInteriorCrop hU R (Ei.e.symm v)) (.inl (Ep.symm p))
  | .inr c => clOriginCoeff hU R hG
      (clPredecessorSupport R (clInteriorCrop hU R (Ei.e.symm v)))
      (clInteriorCrop hU R (Ei.e.symm v)) (.inr c)

theorem clOrderedCoeff_unit (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (hG : G.IsPlain) (Ei : CLIntOrder hU R) (Ep : ↥(clRegionalPairs hG U) ≃ Fin (clLocalOrder1 R)) (v : Fin (clLocalOrder1 R)) (o : Fin (clLocalOrder1 R) ⊕ Fin 4) :
    IsUnitCoeff (clOrderedCoeff hU R hG Ei Ep v o) := by
  cases o <;> exact clOriginCoeff_unit hU R hG _ _ _

theorem clInteriorPredecessor_value {E : Type*} [AddCommGroup E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (κ : GNode G.tree → E) (v : ↥(clInteriorBranches R)) :
    physicalPredecessor (fun _ : Fin 1 => G.sign a.toNode) (fun x => κ (clTreeNode R x))
      (clInteriorCrop hU R v) = (clInteriorPredecessor hU R v).elim 0 (fun u => κ u.1.toNode) := by
  cases hz : signPredecessor (fun _ : Fin 1 => G.sign a.toNode) (clInteriorCrop hU R v) with
  | none => simp only [physicalPredecessor,clInteriorPredecessor,hz,Option.pmap_none,Option.elim_none]
  | some z =>
    simp only [physicalPredecessor,clInteriorPredecessor,hz,Option.pmap_some,Option.elim_some]
    exact congrArg κ (clForestBranch_node hU R z)

end WaveTurbulence.VineEstS2
