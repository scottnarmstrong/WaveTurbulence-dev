/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Incoh.SourceAbsoluteConvergence
public import WaveTurbulence.Foundations.Incoh.LinkArraySummation

/-! # Global original lattice/cell rearrangement for bounded source time coefficients -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Incoh

/-- Original spatial input norms give the absolute double sum needed to localize
any bounded source lattice coefficient, before its analytic representation is chosen. -/
theorem tree_lattice_eq_tsum_cells {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hcover : ∀ c x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C B L : ℝ} (hS : ∀ c, ((S c).card:ℝ) ≤ C^n)
    (hL : 1 ≤ L) (hK : d+1 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (H : ((Fin n × Fin 2) → Fin d → ℤ) → ℂ) {D : ℝ}
    (hbH : ∀ p, ‖H p‖ ≤ D) :
    (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
      H p * P.sourceLeafWeight f k (fun i j => latticePoint L (p (i,j)))) =
      ∑' u : SourceCellIndex S, ∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        H p * P.sourceCellWeight f S k (fun i j => latticePoint L (p (i,j))) u := by
  have hn : Summable (fun q : SourceCellIndex S × ((Fin n × Fin 2) → Fin d → ℤ) =>
      ‖P.sourceCellWeight f S k (fun i j => latticePoint L (q.2 (i,j))) q.1‖) := by
    apply tsum_enorm_ne_top_iff_summable_norm.mp
    rw [ENNReal.tsum_prod']
    exact (P.tsum_enorm_sourceCellWeight_lattice_lt_top f S hS hL hK hM hB hf k).ne
  have hs : Summable (fun q : SourceCellIndex S × ((Fin n × Fin 2) → Fin d → ℤ) =>
      H q.2 * P.sourceCellWeight f S k (fun i j => latticePoint L (q.2 (i,j))) q.1) := by
    apply Summable.of_norm_bounded (hn.mul_left D)
    intro q
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hbH q.2) (norm_nonneg _)
  calc
    _ = ∑' p : (Fin n × Fin 2) → Fin d → ℤ, ∑' u : SourceCellIndex S,
        H p * P.sourceCellWeight f S k (fun i j => latticePoint L (p (i,j))) u := by
      apply tsum_congr
      intro p
      rw [tsum_mul_left, (P.hasSum_sourceCellWeight_of_cover_at f S k
        (fun i j => latticePoint L (p (i,j))) (fun c => hcover c _)).tsum_eq]
    _ = _ := hs.tsum_comm

/-- The same absolute source rearrangement in the actual separate x/y lattice arrays. -/
theorem tree_lattice_pair_eq_tsum_cells {d n m w K M : ℕ}
    (P : MomentumTreeData n m w) (f : Fin m → Mom d → ℂ)
    (S : (Fin m → Fin d → ℤ) → Finset ((Fin n × Fin 2) → Fin d → ℤ))
    (k : Mom d)
    (hcover : ∀ c x, P.inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin n × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c)
    {C B L : ℝ} (hS : ∀ c, ((S c).card:ℝ) ≤ C^n)
    (hL : 1 ≤ L) (hK : d+1 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (H : ((Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) → ℂ)
    {D : ℝ} (hbH : ∀ p, ‖H p‖ ≤ D) :
    (∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
      H g * P.sourceLeafWeight f k
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j))) =
      ∑' u : SourceCellIndex S,
        ∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
          H g * P.sourceCellWeight f S k
            (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) u := by
  let E := (linkLatticeArrayEquiv (Fin n) (Fin d → ℤ)).trans
    (Equiv.arrowProdEquivProdArrow (Fin n) (fun _ => Fin d → ℤ) (fun _ => Fin d → ℤ))
  have hx (g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ)) :
      (fun j i => latticePoint L (E.symm g (j,i))) =
        (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) := by
    funext j i
    fin_cases i <;> rfl
  have he := tree_lattice_eq_tsum_cells P f S k hcover hS hL hK hM hB hf
    (fun p => H (E p)) (fun p => hbH (E p))
  rw [← E.symm.tsum_eq] at he
  have he' (u : SourceCellIndex S) :
      (∑' p : (Fin n × Fin 2) → Fin d → ℤ,
        H (E p) * P.sourceCellWeight f S k (fun j i => latticePoint L (p (j,i))) u) =
      ∑' g : (Fin n → Fin d → ℤ) × (Fin n → Fin d → ℤ),
        H g * P.sourceCellWeight f S k
          (fun j i => if i=0 then latticePoint L (g.1 j) else latticePoint L (g.2 j)) u := by
    rw [← E.symm.tsum_eq]
    apply tsum_congr
    intro g
    rw [E.apply_symm_apply,hx]
  simp_rw [he'] at he
  convert he using 1
  apply tsum_congr
  intro g
  rw [E.apply_symm_apply,hx]

end WaveTurbulence.RegAsymp
