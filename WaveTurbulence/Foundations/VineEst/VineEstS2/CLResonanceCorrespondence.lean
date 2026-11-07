/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLFlowFiber

/-! # The exact M9 node phases are the original signed garden resonances -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed

/-- M9 uses the negative molecular quadratic energy. -/
theorem energy_eq_neg_flow_norm {V D : Type*} [DecidableEq V] [Fintype D] {d : ℕ}
    (M : Molecule V D) (S : Finset V) (k : Bond M S → Mom d) (v : V) :
    energy M S k v = -flow M S (fun e => ‖k e‖^2) v := by
  classical
  unfold energy flow
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Int.cast_smul_eq_zsmul ℝ]
  simp only [smul_eq_mul,neg_mul]

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

/-- The only discrepancy between an internal molecular energy and the
original resonance is the explicit exterior-slot energy. -/
theorem clEnergy_eq_signedOmega_add_external (κ : GNode G.tree → Mom d)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (v : GBranch G.tree) :
    energy G.molecule U (fun e => Mole.restrictLabels G κ e.1) v =
      (((G.sign v.toNode : ℤ) : ℝ)*omegaNode G κ v) +
        externalSlotSum G U (fun x => ‖κ x‖^2) v := by
  have h := gardenInternalFlow_external (fun x => ‖κ x‖^2)
    (fun ℓ hℓ => congrArg (fun q : Mom d => ‖q‖^2) (hp ℓ hℓ)) v
  calc
    _ = -flow G.molecule U (fun e => Mole.restrictLabels G (fun x => ‖κ x‖^2) e.1) v :=
      energy_eq_neg_flow_norm G.molecule U _ v
    _ = -(Mole.slotSum G (fun x => ‖κ x‖^2) v-externalSlotSum G U (fun x => ‖κ x‖^2) v) :=
      congrArg (fun q : ℝ => -q) h
    _ = _ := by rw [Mole.slotSum_energy]; ring

/-- The lower boundary correction in M9's nodeResonance is exactly the
original garden resonance. No replacement resonance or extra sign is used. -/
theorem clNodeResonance_eq_signedOmega (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) {X : VineType} (A : Indexing G.molecule X U a b)
    (κ : GNode G.tree → Mom d)
    (hp : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → κ ℓ.toNode = κ (G.pair ℓ).toNode)
    (i : Fin A.shape.n) :
    nodeResonance A (fun e => Mole.restrictLabels G κ e.1)
      (κ (b.child R.positive)) (κ (b.child R.positive)-κ (b.child R.negative)) i =
    (((G.sign (A.atom i).1.toNode : ℤ) : ℝ)*omegaNode G κ (A.atom i).1) := by
  classical
  by_cases hi : i = A.shape.x0
  · subst i
    unfold nodeResonance
    rw [ite_eq_left rfl,A.lower,clEnergy_eq_signedOmega_add_external κ hp,
      cl_externalSlotSum_lower hU R (fun x => ‖κ x‖^2),slotWeight_child,slotWeight_child,
      R.positive_sign,R.negative_sign]
    have hh : κ (b.child R.positive)-(κ (b.child R.positive)-κ (b.child R.negative)) =
        κ (b.child R.negative) := by abel
    rw [hh]
    simp only [Units.val_one,Units.val_neg,Int.cast_one,Int.cast_neg,neg_neg,one_smul,neg_smul]
    ring
  · have hv := Finset.mem_erase.mp (A.atom i).2
    have hb : (A.atom i).1 ≠ b := by
      intro hb
      apply hi
      apply A.atom.injective
      apply Subtype.ext
      exact hb.trans A.lower.symm
    unfold nodeResonance
    rw [ite_eq_right hi,add_zero,clEnergy_eq_signedOmega_add_external κ hp,
      cl_externalSlotSum_interior hU (fun x => ‖κ x‖^2) (A.atom i).1 hv.2 hv.1 hb,add_zero]

end WaveTurbulence.VineEstS2
