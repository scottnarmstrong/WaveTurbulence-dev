/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.RegRedDraft.LocalSlotBoundarySum
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalDecorations
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLPhaseRecentering

/-! # The four-boundary energy identity on the genuine local decoration fiber -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RegRed
open TTree Finset

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem cl_slotSum_boundary_local (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    {E : Type*} [AddCommGroup E] [Module ℝ E] (A : GNode G.tree → E)
    (hA : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → A ℓ.toNode = A (G.pair ℓ).toNode) :
    (∑ v ∈ U, Mole.slotSum G A v) =
      ((G.sign a.toNode : ℤ) : ℝ) • A a.toNode -
        ((G.sign (a.child R.excluded) : ℤ) : ℝ) • A (a.child R.excluded) -
        ((G.sign (b.child R.positive) : ℤ) : ℝ) • A (b.child R.positive) -
        ((G.sign (b.child R.negative) : ℤ) : ℝ) • A (b.child R.negative) := by
  rw [sum_slotSum_eq_externalSlots_local G U A hA,cl_sum_externalSlotSum hU A,
    cl_externalSlotSum_upper hU R A,cl_externalSlotSum_lower hU R A,
    slotWeight_parent,slotWeight_child,slotWeight_child,slotWeight_child]
  simp only [neg_smul]
  abel

theorem cl_sum_signed_resonance_local {d : ℕ} (hU : G.molecule.IsBlock U a b) (R : CLRegionData G U a b)
    (k : GNode G.tree → Mom d)
    (hk : ∀ ℓ, Mole.IsInternalLeaf G U ℓ → k ℓ.toNode = k (G.pair ℓ).toNode) :
    (∑ v ∈ U, ((G.sign v.toNode : ℤ) : ℝ) * omegaNode G k v) = clBoundaryEnergy R k := by
  have he := cl_slotSum_boundary_local hU R (fun x => ‖k x‖^2)
    (fun ℓ hℓ => congrArg (fun y => ‖y‖^2) (hk ℓ hℓ))
  have hleft : (∑ v ∈ U, Mole.slotSum G (fun x => ‖k x‖^2) v) =
      -(∑ v ∈ U, ((G.sign v.toNode : ℤ) : ℝ) * omegaNode G k v) := by
    simp_rw [Mole.slotSum_energy,neg_mul]
    rw [Finset.sum_neg_distrib]
  rw [hleft] at he
  simp only [smul_eq_mul] at he
  unfold clBoundaryEnergy
  linarith only [he]

/-- The local decoration definition supplies exactly the needed internal pairing;
no values or matching conditions outside the realization are used. -/
theorem clLocalDecoration_sum_signed_resonance {d : ℕ} (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) (L : ℝ) (base : Mom d) (boundary : Fin 4 → Mom d)
    (κ : CLLocalDecoration R L base boundary) :
    (∑ v ∈ U, ((G.sign v.toNode : ℤ) : ℝ) *
      omegaNode G (cosetDecoration G L base (clExtendIndices R κ.1)) v) =
      boundaryEnergyFromMomenta (G.sign a.toNode) (boundary 0) (boundary 1) (boundary 2) (boundary 3) := by
  let k := cosetDecoration G L base (clExtendIndices R κ.1)
  have he := cl_sum_signed_resonance_local hU R k
    (fun ℓ hℓ => congrArg (fun z => base+latticePoint L z) (κ.2.2.1 ℓ hℓ))
  apply he.trans
  have h0 : k a.toNode = boundary 0 := κ.2.2.2 0
  have h1 : k (a.child R.excluded) = boundary 1 := κ.2.2.2 1
  have h2 : k (b.child R.positive) = boundary 2 := κ.2.2.2 2
  have h3 : k (b.child R.negative) = boundary 3 := κ.2.2.2 3
  have hb := clBoundaryEnergy_eq_fourMomenta R k
  rw [h0,h1,h2,h3] at hb
  exact hb

/-- TARGET defKtilde on the actual local lattice fiber. The four-boundary
recentering energy is proved from incidence cancellation for every summand. -/
theorem clLocalDecoration_phase_recenter {d : ℕ} (hU : G.molecule.IsBlock U a b)
    (R : CLRegionData G U a b) (L γ δ : ℝ) (base : Mom d) (boundary : Fin 4 → Mom d)
    (κ : CLLocalDecoration R L base boundary) (τ : GBranch G.tree → ℝ) (t : ℝ) :
    Complex.exp (((-(Real.pi*δ*L^(2*γ))*t*
      boundaryEnergyFromMomenta (G.sign a.toNode) (boundary 0) (boundary 1) (boundary 2) (boundary 3) : ℝ) : ℂ)*Complex.I) *
      (∏ v ∈ U, phaseAtom L γ δ (G.sign v.toNode)
        (omegaNode G (cosetDecoration G L base (clExtendIndices R κ.1)) v) (τ v)) =
      ∏ v ∈ U, phaseAtom L γ δ (G.sign v.toNode)
        (omegaNode G (cosetDecoration G L base (clExtendIndices R κ.1)) v) (τ v-t) := by
  let k := cosetDecoration G L base (clExtendIndices R κ.1)
  have h := resonance_phase_recenter U (fun v => ((G.sign v.toNode : ℤ) : ℝ)*omegaNode G k v)
    τ (Real.pi*δ*L^(2*γ)) t
  rw [clLocalDecoration_sum_signed_resonance hU R L base boundary κ] at h
  have hp (u : GBranch G.tree → ℝ) :
      (∏ v ∈ U, Complex.exp ((((Real.pi*δ*L^(2*γ))*
        (((G.sign v.toNode : ℤ) : ℝ)*omegaNode G k v)*u v : ℝ) : ℂ)*Complex.I)) =
      ∏ v ∈ U, phaseAtom L γ δ (G.sign v.toNode) (omegaNode G k v) (u v) := by
    apply Finset.prod_congr rfl
    intro v _
    unfold phaseAtom
    congr 1
    push_cast
    ring
  rw [hp τ,hp (fun v => τ v-t)] at h
  exact h

end WaveTurbulence.RegRed
