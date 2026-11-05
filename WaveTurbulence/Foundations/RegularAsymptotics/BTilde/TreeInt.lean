/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeBasic
public import Mathlib

/-!
# The time integral of one tree

DH21 (defcoefa2), (defcoefb2) and DH23 (defcoefb2) (L951–L954) integrate `∏_𝔫 e^{πiζ_𝔫α_𝔫t_𝔫}` over
the time domain of a tree (`0 < t_{𝔫'} < t_𝔫` for a child `𝔫'`, and `t_𝔫 < u`). By Fubini along the
tree this is the iterated integral
`A_T(u) = ∫_0^u e^{πiβ_∅τ} ∏_{i<3} A_{T_i}(τ) dτ` (`treeInt`), with `A_• = 1` (`integral_treeDomR`).
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree MeasureTheory Complex Set
open scoped Real

/-- **The iterated time integral of a tree** with phases `β` (indexed by the paths from its root). -/
noncomputable def treeInt : TTree → (TTree.Path → ℝ) → ℝ → ℂ
  | .leaf, _, _ => 1
  | .node l m r, β, u => ∫ τ in (0 : ℝ)..u, cexp (π * I * (β [] * τ)) *
      (treeInt l (fun p => β (0 :: p)) τ * treeInt m (fun p => β (1 :: p)) τ *
        treeInt r (fun p => β (2 :: p)) τ)

/-- The phase `∏_{p} e^{πiβ_p τ_p}` of node times. -/
noncomputable def treePhase (T : TTree) (β : TTree.Path → ℝ) (τ : TB T → ℝ) : ℂ :=
  ∏ p : TB T, cexp (π * I * (β p.1 * τ p))

/-- The time of the root and the times of the three subtrees of a node tree. -/
def tRoot {l m r : TTree} (τ : TB (.node l m r) → ℝ) : ℝ := τ ((tbNodeEquiv l m r).symm (.inl ()))
def tL {l m r : TTree} (τ : TB (.node l m r) → ℝ) : TB l → ℝ :=
  fun q => τ ((tbNodeEquiv l m r).symm (.inr (.inl q)))
def tM {l m r : TTree} (τ : TB (.node l m r) → ℝ) : TB m → ℝ :=
  fun q => τ ((tbNodeEquiv l m r).symm (.inr (.inr (.inl q))))
def tR {l m r : TTree} (τ : TB (.node l m r) → ℝ) : TB r → ℝ :=
  fun q => τ ((tbNodeEquiv l m r).symm (.inr (.inr (.inr q))))

/-- **The recursive time domain** of a tree: `0 < t_root < u`, and each subtree lies below `t_root`. -/
def treeDomR : (T : TTree) → ℝ → Set (TB T → ℝ)
  | .leaf, _ => Set.univ
  | .node l m r, u => {τ | 0 < tRoot τ ∧ tRoot τ < u ∧ tL τ ∈ treeDomR l (tRoot τ) ∧
      tM τ ∈ treeDomR m (tRoot τ) ∧ tR τ ∈ treeDomR r (tRoot τ)}

theorem treePhase_node (l m r : TTree) (β : TTree.Path → ℝ) (τ : TB (.node l m r) → ℝ) :
    treePhase (.node l m r) β τ = cexp (π * I * (β [] * tRoot τ)) *
      (treePhase l (fun p => β (0 :: p)) (tL τ) * treePhase m (fun p => β (1 :: p)) (tM τ) *
        treePhase r (fun p => β (2 :: p)) (tR τ)) := by
  unfold treePhase
  rw [← (tbNodeEquiv l m r).symm.prod_comp]
  simp only [Fintype.prod_sum_type, Finset.univ_unique, Finset.prod_singleton, tRoot, tL, tM, tR,
    mul_assoc]
  rfl

section Fubini

/-- Integrals are invariant under relabelling the coordinates. -/
theorem integral_reindex_pi {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (F : (ι → ℝ) → ℂ) : ∫ σ : ι' → ℝ, F (fun i => σ (e i)) = ∫ τ : ι → ℝ, F τ :=
  ((volume_measurePreserving_piCongrLeft (fun _ : ι' => ℝ) e).symm _).integral_comp' F

/-- Integrals over a disjoint union of coordinates. -/
theorem integral_sum_pi {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (F : (ι₁ → ℝ) × (ι₂ → ℝ) → ℂ) :
    ∫ σ : ι₁ ⊕ ι₂ → ℝ, F (fun i => σ (.inl i), fun i => σ (.inr i)) = ∫ p, F p :=
  (volume_measurePreserving_sumPiEquivProdPi (fun _ : ι₁ ⊕ ι₂ => ℝ)).integral_comp' F

theorem integral_sum_pi_mul {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (f : (ι₁ → ℝ) → ℂ)
    (g : (ι₂ → ℝ) → ℂ) :
    ∫ σ : ι₁ ⊕ ι₂ → ℝ, f (fun i => σ (.inl i)) * g (fun i => σ (.inr i)) = (∫ x, f x) * ∫ y, g y := by
  rw [integral_sum_pi (fun p => f p.1 * g p.2), Measure.volume_eq_prod, integral_prod_mul]

theorem continuous_tRoot (l m r : TTree) : Continuous (tRoot (l := l) (m := m) (r := r)) :=
  continuous_apply _
theorem continuous_tL (l m r : TTree) : Continuous (tL (l := l) (m := m) (r := r)) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_tM (l m r : TTree) : Continuous (tM (l := l) (m := m) (r := r)) :=
  continuous_pi fun _ => continuous_apply _
theorem continuous_tR (l m r : TTree) : Continuous (tR (l := l) (m := m) (r := r)) :=
  continuous_pi fun _ => continuous_apply _

theorem norm_treePhase (T : TTree) (β : TTree.Path → ℝ) (τ : TB T → ℝ) : ‖treePhase T β τ‖ = 1 := by
  unfold treePhase
  rw [norm_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [Complex.norm_exp]
  simp

theorem continuous_treePhase (T : TTree) (β : TTree.Path → ℝ) : Continuous (treePhase T β) := by
  unfold treePhase
  fun_prop

end Fubini

end WaveTurbulence.MainCoef

