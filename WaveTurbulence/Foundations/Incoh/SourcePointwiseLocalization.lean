/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceCellMeasure
public import WaveTurbulence.Foundations.Incoh.LeafArrayLocalization
public import WaveTurbulence.Foundations.Incoh.FiniteLinkCellLocalization

/-!
# Exact pointwise countable localization of the raw source input product

The cell sum is pointwise finite. It recovers the literal input product
before applying any lattice or time summation.
-/

public section
noncomputable section

namespace WaveTurbulence.Incoh

/-- The unlocalized source input weight, TARGET (incohproof3). -/
@[expose] def MomentumTreeData.sourceLeafWeight {d n m w : ℕ} (P : MomentumTreeData n m w)
    (f : Fin m → Mom d → ℂ) (k : Mom d) (x : Fin n → Fin 2 → Mom d) : ℂ :=
  ∏ a, f a (P.inputMomentum k x a)

/-- Actual source weight of one selected leaf/link cell. -/
@[expose] def MomentumTreeData.sourceCellWeight {d n m w : ℕ} (P : MomentumTreeData n m w)
    (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) (u : SourceCellIndex S) : ℂ :=
  P.localizedLeafWeight f u.1 k x * halfCellArrayWeight u.2.val (fun p => x p.1 p.2)

/-- Any leaf-cell array outside the actual finite pointwise partition support vanishes. -/
theorem MomentumTreeData.localizedLeafWeight_eq_zero_of_not_mem {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ) (k : Mom d)
    (x : Fin n → Fin 2 → Mom d) (c : Fin m → Fin d → ℤ)
    (hc : c ∉ Fintype.piFinset (fun a => ApproxNT.thetaSupport (P.inputMomentum k x a))) :
    P.localizedLeafWeight f c k x = 0 := by
  classical
  have hn : ¬∀ a, c a ∈ ApproxNT.thetaSupport (P.inputMomentum k x a) := by
    simpa only [Fintype.mem_piFinset] using hc
  obtain ⟨a, ha⟩ := not_forall.mp hn
  exact Finset.prod_eq_zero (Finset.mem_univ a)
    (leafCell_eq_zero_of_notMem (f a) (P.inputMomentum k x a) ha)

/-- For a fixed leaf cell, the selected link cells recover its actual source weight. -/
theorem MomentumTreeData.sum_sourceCellWeight_fiber_eq_of_cover_at {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (x : Fin n → Fin 2 → Mom d)
    (hS : ∀ c, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    (c : Fin m → Fin d → ℤ) :
    (∑ z : {z : (Fin n × Fin 2) → Fin d → ℤ // z ∈ S c},
      P.sourceCellWeight f S k x ⟨c, z⟩) = P.localizedLeafWeight f c k x := by
  classical
  change (∑ z : ↥(S c), P.localizedLeafWeight f c k x *
    halfCellArrayWeight z.val (fun p => x p.1 p.2)) = _
  rw [Finset.sum_coe_sort (S c) (fun z => P.localizedLeafWeight f c k x *
    halfCellArrayWeight z (fun p => x p.1 p.2)), ← Finset.mul_sum]
  by_cases hc : P.inputCellWeight c k x = 0
  · simp only [P.localizedLeafWeight_eq, hc, mul_zero, zero_mul]
  · have hz (z : (Fin n × Fin 2) → Fin d → ℤ) (hz : z ∉ S c) :
        halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) = 0 := by
      by_contra hn
      exact hz (hS c hc z hn)
    have he : (∑ z ∈ S c, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2)) = 1 :=
      ((hasSum_halfCellArrayWeight (fun p : Fin n × Fin 2 => x p.1 p.2)).unique
        (hasSum_sum_of_ne_finset_zero hz)).symm
    rw [he, mul_one]

/-- All selected cell weights recover the raw source input product, with an actual finite
pointwise support. No analytic convergence premise is assumed. -/
theorem MomentumTreeData.hasSum_sourceCellWeight_of_cover_at {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d) (x : Fin n → Fin 2 → Mom d)
    (hS : ∀ c, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c) :
    HasSum (P.sourceCellWeight f S k x) (P.sourceLeafWeight f k x) := by
  classical
  let A := Fintype.piFinset (fun a => ApproxNT.thetaSupport (P.inputMomentum k x a))
  let F : Finset (SourceCellIndex S) := A.sigma (fun c => Finset.univ)
  have hz (u : SourceCellIndex S) (hu : u ∉ F) : P.sourceCellWeight f S k x u = 0 := by
    have hc : u.1 ∉ A := by simpa only [F, Finset.mem_sigma, Finset.mem_univ, and_true] using hu
    rw [sourceCellWeight, P.localizedLeafWeight_eq_zero_of_not_mem f k x u.1 hc, zero_mul]
  have hs : HasSum (P.sourceCellWeight f S k x) (∑ u ∈ F, P.sourceCellWeight f S k x u) :=
    hasSum_sum_of_ne_finset_zero hz
  have hleaf : HasSum (fun c => P.localizedLeafWeight f c k x) (P.sourceLeafWeight f k x) :=
    hasSum_leafCell_product f (P.inputMomentum k x)
  have hleafA : HasSum (fun c => P.localizedLeafWeight f c k x)
      (∑ c ∈ A, P.localizedLeafWeight f c k x) := hasSum_sum_of_ne_finset_zero
    (fun c hc => P.localizedLeafWeight_eq_zero_of_not_mem f k x c hc)
  have he : (∑ u ∈ F, P.sourceCellWeight f S k x u) = P.sourceLeafWeight f k x := by
    change (∑ u ∈ A.sigma (fun c => Finset.univ), P.sourceCellWeight f S k x u) = _
    rw [Finset.sum_sigma]
    simp_rw [P.sum_sourceCellWeight_fiber_eq_of_cover_at f S k x hS]
    exact hleafA.unique hleaf
  exact he ▸ hs

/-- All selected cell weights recover the raw source input product, with an actual finite
pointwise support. No analytic convergence premise is assumed. -/
theorem MomentumTreeData.hasSum_sourceCellWeight {d n m w : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (hS : ∀ c k x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    (k : Mom d) (x : Fin n → Fin 2 → Mom d) :
    HasSum (P.sourceCellWeight f S k x) (P.sourceLeafWeight f k x) :=
  P.hasSum_sourceCellWeight_of_cover_at f S k x (fun c => hS c k x)

end WaveTurbulence.Incoh
