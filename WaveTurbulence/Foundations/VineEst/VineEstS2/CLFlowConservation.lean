/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLRebuildLabels

/-! # The M9 flow fiber reconstructs the source branching conservation -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The boundary premise is precisely the signed four-boundary momentum
constraint from the source. Conservation is proved, not passed as a field. -/
theorem clRebuildLabels_conservation {E : Type} [AddCommGroup E] [Module ℝ E]
    (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b) (β : Fin 4 → E)
    (hβ : (((G.sign a.toNode : ℤ) : ℝ) • (β 0-β 1)) = β 2-β 3)
    (k : FlowFiber G.molecule U a b E (β 2-β 3)) :
    ∀ v ∈ U, clRebuildLabels R k.1 β v.toNode =
      clRebuildLabels R k.1 β (v.child 0)-clRebuildLabels R k.1 β (v.child 1)+
        clRebuildLabels R k.1 β (v.child 2) := by
  classical
  let κ := clRebuildLabels R k.1 β
  have hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode :=
    clRebuildLabels_matching R k.1 β
  have hk : (fun e : Bond G.molecule U => Mole.restrictLabels G κ e.1) = k.1 :=
    funext (clRebuildLabels_bond R k.1 β)
  have hslot (v : GBranch G.tree) : Mole.slotSum G κ v = flow G.molecule U k.1 v+externalSlotSum G U κ v := by
    have h := gardenInternalFlow_external κ hp v
    rw [hk] at h
    exact (eq_sub_iff_add_eq.mp h).symm
  have h0 : κ a.toNode = β 0 := clRebuildLabels_boundary hU R k.1 β 0
  have h1 : κ (a.child R.excluded) = β 1 := clRebuildLabels_boundary hU R k.1 β 1
  have h2 : κ (b.child R.positive) = β 2 := clRebuildLabels_boundary hU R k.1 β 2
  have h3 : κ (b.child R.negative) = β 3 := clRebuildLabels_boundary hU R k.1 β 3
  have hupper : externalSlotSum G U κ a = β 2-β 3 := by
    rw [cl_externalSlotSum_upper hU R κ,slotWeight_parent,slotWeight_child,
      Mole.outer_child_sign G a R.excluded R.excluded_ne_middle,h0,h1,neg_smul]
    rw [← sub_eq_add_neg]
    exact (smul_sub _ _ _).symm.trans hβ
  have hlower : externalSlotSum G U κ b = -(β 2-β 3) := by
    rw [cl_externalSlotSum_lower hU R κ,slotWeight_child,slotWeight_child,
      R.positive_sign,R.negative_sign,h2,h3]
    simp only [Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg,neg_neg,one_smul,neg_smul]
    abel
  intro v hv
  apply (Mole.slotSum_eq_zero_iff G κ v).mp
  rw [hslot]
  by_cases ha : v = a
  · subst v
    rw [k.2.1,hupper,neg_add_cancel]
  · by_cases hb : v = b
    · subst v
      rw [k.2.2.1,hlower,add_neg_cancel]
    · rw [k.2.2.2 v hv ha hb,cl_externalSlotSum_interior hU κ v hv ha hb,add_zero]

/-- Reconstruction commutes with additive embeddings, including the lattice
embedding into momentum space. It is a literal nodewise equality. -/
theorem clRebuildLabels_map {E F : Type*} [AddCommGroup E] [AddCommGroup F]
    (R : CLRegionData G U a b) (f : E →+ F) (k : Bond G.molecule U → E) (β : Fin 4 → E)
    (x : GNode G.tree) : f (clRebuildLabels R k β x) =
      clRebuildLabels R (fun e => f (k e)) (fun j => f (β j)) x := by
  classical
  unfold clRebuildLabels
  split_ifs
  · rfl
  · rfl
  · exact map_zero f

end WaveTurbulence.VineEstS2
