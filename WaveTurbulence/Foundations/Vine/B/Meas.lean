/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Vine.B.Pointwise
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsBase2
public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm9
import Mathlib.Tactic

/-!
# VINE-B♯: joint measurability

The unit summand `lowModC · clLocalSummand` is jointly measurable in the exterior clocks and the interior times (V5's
`measT_psiNat`), hence in the glued variables `(τ', (τ_j))`; so are `clocks τ' j`, the phases and the modes.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
namespace WaveTurbulence.VineB
open TTree WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory

section Generic
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {α : Type*} [MeasurableSpace α]

theorem measurable_clLocalClock_joint (R : CLRegionData G U a b) (t : α → Fin 3 → ℝ) (τ : α → CLInternalTime R)
    (ht : ∀ i, Measurable fun x => t x i) (hτ : ∀ v, Measurable fun x => τ x v) (v : GBranch G.tree) :
    Measurable fun x => clLocalClock R (t x) (τ x) v := by
  classical
  by_cases ha : v = a
  · have : (fun x => clLocalClock R (t x) (τ x) v) = fun x => t x 0 :=
      funext fun x => by rw [ha]; exact clLocalClock_upper R (t x) (τ x)
    rw [this]; exact ht 0
  · by_cases hv : v ∈ U
    · have hm : v ∈ clInteriorBranches R := Finset.mem_erase.mpr ⟨ha, hv⟩
      have : (fun x => clLocalClock R (t x) (τ x) v) = fun x => τ x ⟨v, hm⟩ :=
        funext fun x => clLocalClock_internal R (t x) (τ x) ⟨v, hm⟩
      rw [this]; exact hτ _
    · have : (fun x => clLocalClock R (t x) (τ x) v) = fun x =>
          (if v.toNode = b.child R.positive then t x 1
            else if v.toNode = b.child R.negative then t x 2 else 0) :=
        funext fun x => by simp [clLocalClock, ha, hv]
      rw [this]
      by_cases h1 : v.toNode = b.child R.positive
      · simp only [if_pos h1]; exact ht 1
      · by_cases h2 : v.toNode = b.child R.negative
        · simp only [if_neg h1, if_pos h2]; exact ht 2
        · simp only [if_neg h1, if_neg h2]; exact measurable_const

variable {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}

theorem measurable_clLocalSummand_joint (R : CLRegionData G U a b) (hF : HF D hG L F layer base)
    (β : Fin 4 → Mom d) (κ : CLLocalDecoration R L base β) (t : α → Fin 3 → ℝ) (τ : α → CLInternalTime R)
    (ht : ∀ i, Measurable fun x => t x i) (hτ : ∀ v, Measurable fun x => τ x v) :
    Measurable fun x => clLocalSummand D hG R L γ δ F layer hLayer base β (t x) κ (τ x) := by
  have h1 : Measurable fun x => ((t x, fun v => clLocalClock R (t x) (τ x) v) :
      (Fin 3 → ℝ) × (GBranch G.tree → ℝ)) :=
    Measurable.prodMk (measurable_pi_iff.mpr ht)
      (measurable_pi_iff.mpr fun v => measurable_clLocalClock_joint R t τ ht hτ v)
  have h2 := (measT_psiNat (γ := γ) (δ := δ) (hLayer := hLayer) R hF (clExtendIndices R κ.1)).comp h1
  have heq : (fun x => clLocalSummand D hG R L γ δ F layer hLayer base β (t x) κ (τ x)) = fun x =>
      psiNat D hG R L γ δ F layer hLayer base (clExtendIndices R κ.1) (t x) (fun v => clLocalClock R (t x) (τ x) v) :=
    funext fun x => clLocalSummand_eq_psiNat D hG R L γ δ F layer hLayer base β (t x) κ (τ x)
  rw [heq]
  exact h2

end Generic

section Glued
variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

theorem measurable_clockOf (tt : Fin w → ℝ) (y : ClkSrc Gsb) :
    Measurable fun τ' : GBranch Gsb.tree → ℝ => clockOf Gsb tt τ' y := by
  rcases y with i | c
  · exact measurable_const
  · exact measurable_pi_apply c

namespace SpliceShape
variable (Φ : SpliceShape blk Gsb)

theorem measurable_extTime (v : GBranch S.tree) :
    Measurable fun τ' : GBranch Gsb.tree → ℝ => Φ.extTime τ' v := by
  classical
  by_cases h : Ret blk v.toNode
  · have : (fun τ' : GBranch Gsb.tree → ℝ => Φ.extTime τ' v) = fun τ' => τ' (Φ.brEquiv.symm ⟨v, h⟩) :=
      funext fun τ' => by unfold extTime; rw [dif_pos h]
    rw [this]; exact measurable_pi_apply _
  · have : (fun τ' : GBranch Gsb.tree → ℝ => Φ.extTime τ' v) = fun _ => 0 :=
      funext fun τ' => by unfold extTime; rw [dif_neg h]
    rw [this]; exact measurable_const

theorem measurable_clBranchClock_ext (x : GNode S.tree) :
    Measurable fun τ' : GBranch Gsb.tree → ℝ => clBranchClock (Φ.extTime τ') x := by
  classical
  by_cases hb : x.1.2 ∈ (S.tree x.1.1).branching
  · have : (fun τ' : GBranch Gsb.tree → ℝ => clBranchClock (Φ.extTime τ') x) = fun τ' => Φ.extTime τ' ⟨x.1, hb⟩ :=
      funext fun τ' => by unfold clBranchClock; rw [dif_pos hb]
    rw [this]; exact Φ.measurable_extTime _
  · have : (fun τ' : GBranch Gsb.tree → ℝ => clBranchClock (Φ.extTime τ') x) = fun _ => 0 :=
      funext fun τ' => by unfold clBranchClock; rw [dif_neg hb]
    rw [this]; exact measurable_const

theorem measurable_clocks (j : J) (i : Fin 3) :
    Measurable fun τ' : GBranch Gsb.tree → ℝ => Φ.clocks τ' j i := by
  fin_cases i
  · exact Φ.measurable_extTime _
  · exact Φ.measurable_clBranchClock_ext _
  · exact Φ.measurable_clBranchClock_ext _

theorem measurable_unitInt (D : ReconstructionData S) (hS : S.IsPlain) (L γ δ : ℝ)
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (layer : GNode (D.forest hS) → ℕ)
    (hLayer : IsLayering (D.garden hS) layer) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (hSb : Gsb.IsPlain) (z : GenDecoration Gsb d roots 0) (j : J)
    (hF : HF D hS L (unitProfile blk h j) layer base)
    (κ : CLLocalDecoration (regionOf (blk j)) L base (Φ.bdry L base z.1 j)) :
    Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.unitInt D hS L γ δ h layer hLayer base frq hSb z p.1 j κ (p.2 j) := by
  have hcl : ∀ i, Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.clocks p.1 j i := fun i => (Φ.measurable_clocks j i).comp measurable_fst
  have hτ : ∀ v, Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      p.2 j v := fun v => (measurable_pi_apply v).comp ((measurable_pi_apply j).comp measurable_snd)
  have h1 := measurable_clLocalSummand_joint (γ := γ) (δ := δ) (hLayer := hLayer) (regionOf (blk j)) hF
    (Φ.bdry L base z.1 j) κ (fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      Φ.clocks p.1 j) (fun p => p.2 j) hcl hτ
  have h2 : Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      lowModC (regionOf (blk j)) (modLam frq (Φ.route hS hSb) j : ℝ) (Φ.clocks p.1 j) (p.2 j) := by
    have hb := measurable_clLocalClock_joint (regionOf (blk j)) (fun p : (GBranch Gsb.tree → ℝ) ×
      (∀ j, CLInternalTime (regionOf (blk j))) => Φ.clocks p.1 j) (fun p => p.2 j) hcl hτ (blk j).lower
    unfold lowModC
    exact Measurable.cexp ((Complex.measurable_ofReal.comp (hb.const_mul (Real.pi *
      (modLam frq (Φ.route hS hSb) j : ℝ)))).mul_const Complex.I)
  have h3 : Measurable fun p : (GBranch Gsb.tree → ℝ) × (∀ j, CLInternalTime (regionOf (blk j))) =>
      recExp L γ δ (S.sign (blk j).upper.toNode) (Φ.clocks p.1 j 0) (Φ.bdry L base z.1 j) := by
    unfold recExp
    exact Measurable.cexp ((Complex.measurable_ofReal.comp
      (((hcl 0).const_mul (-(Real.pi * δ * L ^ (2 * γ)))).mul_const
        (boundaryEnergyFromMomenta (S.sign (blk j).upper.toNode) (Φ.bdry L base z.1 j 0) (Φ.bdry L base z.1 j 1)
          (Φ.bdry L base z.1 j 2) (Φ.bdry L base z.1 j 3)))).mul_const Complex.I)
  exact h3.mul (h2.mul h1)

theorem measurable_sbInt (hS : S.IsPlain) (hSb : Gsb.IsPlain) (L γ δ : ℝ) (base : Mom d)
    {roots : Fin w → (Fin d → ℤ)} (tt : Fin w → ℝ) (amp : ReplacementSlot Gsb → Mom d → ℂ)
    (frq : ReplacementSlot Gsb → Fin 2 → ℤ) (z : GenDecoration Gsb d roots 0) :
    Measurable fun τ' : GBranch Gsb.tree → ℝ => Φ.sbInt hS hSb L γ δ base tt amp frq z τ' := by
  unfold sbInt routedPhase
  refine (((continuous_phaseProd L γ δ _ _).measurable.mul_const _).mul
    (Finset.measurable_prod _ fun s _ => Finset.measurable_prod _ fun i _ => ?_))
  generalize Φ.route hS hSb s i = r
  rcases r with y | j
  · exact Measurable.cexp ((Complex.measurable_ofReal.comp ((measurable_clockOf tt y).const_mul
      (Real.pi * (frq s i : ℝ)))).mul_const Complex.I)
  · exact measurable_const

end SpliceShape
end Glued

end WaveTurbulence.VineB
