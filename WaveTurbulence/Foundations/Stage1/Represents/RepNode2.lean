/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepNode1
import Mathlib.Tactic

/-!
# S2 REPRESENTS: the pointwise identity with node centres
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic
  WaveTurbulence.VineEstS3.FS

variable {w d : ℕ} {S : Garden w}

theorem fsPhase_norm {r : ℕ} (m : Fin r → ℤ) (t : Fin r → ℝ) : ‖fsPhase m t‖ = 1 := by
  unfold fsPhase; exact Circle.norm_coe _

open scoped Classical in
theorem hasSum_node_slots (fam : SlotFam S d) (hS : S.IsPlain)
    (Fn : ReplacementSlot S → (Fin 2 → ℝ) → Mom d → ℂ) (ts : ReplacementSlot S → Fin 2 → ℝ)
    (k : ReplacementSlot S → Mom d)
    (hFn : ∀ s, HasSum (fun l => (fam.w s l : ℂ) * fam.a s l (k s) * fsPhase (fam.m s l) (ts s))
      (Fn s (ts s) (k s)))
    (δ : GNode S.tree → Mom d)
    (hδ : ∀ b : GBranch S.tree, δ b.toNode = δ (b.child 0) - δ (b.child 1) + δ (b.child 2))
    (hleaf : ∀ ℓ : GLeaf S.tree, δ ℓ.toNode = k (Sum.inl (pairOfLeaf S hS ℓ)))
    (hbr : ∀ b : GBranch S.tree, δ b.toNode = k (Sum.inr b)) :
    HasSum (fam.term hS k ts) (∏ s, Fn s (ts s) (k s)) := by
  set u : ∀ s, fam.Λ s → ℂ := fun s l =>
    (fam.w s l : ℂ) * fam.a s l (k s) * fsPhase (fam.m s l) (ts s) with hu
  have hunorm : ∀ s, Summable fun l => ‖u s l‖ := by
    intro s
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) (fam.w_sum s)
    simp only [hu, norm_mul, fsPhase_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg (fam.w_nn s l)]
    exact mul_le_of_le_one_right (fam.w_nn s l) (fam.a_one s l _)
  obtain ⟨hgs, hgsum⟩ := hasSum_prod_fintype u hunorm
  have htsum : ∏ s, ∑' l, u s l = ∏ s, Fn s (ts s) (k s) :=
    Finset.prod_congr rfl fun s _ => (hFn s).tsum_eq
  rw [htsum] at hgsum
  set g : (∀ s, fam.Λ s) → ℂ := fun ξ => ∏ s, u s (ξ s) with hg
  -- the node partition of unity
  have hchi := hasSum_node_chi (tree := S.tree) (d := d) δ
  set c : (GBranch S.tree → Fin d → ℤ) → ℝ := fun x => ∏ b, chi d (x b) (k (Sum.inr b)) with hc
  have hchi' : HasSum c 1 := by
    have : ∀ x, ∏ b, chi d (x b) (δ b.toNode) = c x := fun x =>
      Finset.prod_congr rfl fun b _ => by rw [hbr b]
    simpa only [this] using hchi
  have hc0 : ∀ x, 0 ≤ c x := fun x => Finset.prod_nonneg fun b _ => chi_nonneg d _ _
  have hcC : ∀ x, ∏ b, chiC d (x b) (k (Sum.inr b)) = (c x : ℂ) := by
    intro x; simp [chiC, c, Complex.ofReal_prod]
  have hgfac : ∀ ξ : ∀ s, fam.Λ s, g ξ = (∏ s, ((fam.w s (ξ s) : ℝ) : ℂ)) * (∏ s, fam.a s (ξ s) (k s)) *
      ∏ s, fsPhase (fam.m s (ξ s)) (ts s) := by
    intro ξ
    simp only [hg, hu, Finset.prod_mul_distrib]
  have hterm_eq : ∀ p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ), fam.term hS k ts p =
      g p.1 * ((if p.2 ∈ nodeCentreSet (fam.leafCentre hS p.1) then (1 : ℂ) else 0) *
        ∏ b : GBranch S.tree, chiC d (p.2 b) (k (Sum.inr b))) := by
    intro p
    unfold SlotFam.term
    rw [hgfac]
    ring
  -- for g ξ ≠ 0 the indicator is automatic
  have hind : ∀ ξ : ∀ s, fam.Λ s, g ξ ≠ 0 → ∀ x : GBranch S.tree → Fin d → ℤ,
      (if x ∈ nodeCentreSet (fam.leafCentre hS ξ) then (1 : ℂ) else 0) *
        ∏ b : GBranch S.tree, chiC d (x b) (k (Sum.inr b)) = (c x : ℂ) := by
    intro ξ hξ x
    have hprod : ∏ s, fam.a s (ξ s) (k s) ≠ 0 := by
      rw [hgfac] at hξ
      intro h0; apply hξ; rw [h0]; ring
    have hne : ∀ s, fam.a s (ξ s) (k s) ≠ 0 := fun s => (Finset.prod_ne_zero_iff.1 hprod) s (Finset.mem_univ _)
    have hleaf' : ∀ ℓ : GLeaf S.tree, ‖δ ℓ.toNode - latPt d (fam.leafCentre hS ξ ℓ)‖ ≤ 1 := by
      intro ℓ
      rw [hleaf ℓ]
      exact fam.a_supp _ _ _ (hne _)
    rw [hcC]
    by_cases hx : x ∈ nodeCentreSet (fam.leafCentre hS ξ)
    · simp [hx]
    · have : c x = 0 := by
        by_contra hcx
        apply hx
        have h1 : ∏ b, chi d (x b) (δ b.toNode) ≠ 0 := by
          have : ∏ b, chi d (x b) (δ b.toNode) = c x := Finset.prod_congr rfl fun b _ => by rw [hbr b]
          rw [this]; exact hcx
        exact nodeCentreAdm_of_prod_ne_zero δ hδ hleaf' h1
      simp [hx, this]
  have hfib : ∀ ξ : ∀ s, fam.Λ s, HasSum (fun x => fam.term hS k ts (ξ, x)) (g ξ) := by
    intro ξ
    by_cases hξ : g ξ = 0
    · have : ∀ x, fam.term hS k ts (ξ, x) = 0 := fun x => by rw [hterm_eq]; simp [hξ]
      simp only [this, hξ]
      exact hasSum_zero
    · have : ∀ x, fam.term hS k ts (ξ, x) = g ξ * (c x : ℂ) := fun x => by
        rw [hterm_eq]; simp only; rw [hind ξ hξ x]
      simp only [this]
      have h1 := (Complex.hasSum_ofReal.2 hchi').mul_left (g ξ)
      simpa using h1
  have hbound : ∀ p : (∀ s, fam.Λ s) × (GBranch S.tree → Fin d → ℤ),
      ‖fam.term hS k ts p‖ ≤ ‖g p.1‖ * c p.2 := by
    intro p
    rw [hterm_eq, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    by_cases hx : p.2 ∈ nodeCentreSet (fam.leafCentre hS p.1)
    · simp only [hx, ite_true, one_mul]
      rw [hcC, Complex.norm_real, Real.norm_of_nonneg (hc0 _)]
    · simp [hx, hc0]
  have hterm : Summable (fam.term hS k ts) := by
    refine Summable.of_norm_bounded (g := fun p => ‖g p.1‖ * c p.2) ?_ hbound
    exact Summable.mul_of_nonneg (f := fun ξ => ‖g ξ‖) (g := c) hgs hchi'.summable
      (fun _ => norm_nonneg _) hc0
  have htot : ∑' p, fam.term hS k ts p = ∏ s, Fn s (ts s) (k s) := by
    rw [Summable.tsum_prod' hterm (fun ξ => (hfib ξ).summable)]
    rw [← hgsum.tsum_eq]
    exact tsum_congr fun ξ => (hfib ξ).tsum_eq
  rw [← htot]
  exact hterm.hasSum

end WaveTurbulence.Represents
