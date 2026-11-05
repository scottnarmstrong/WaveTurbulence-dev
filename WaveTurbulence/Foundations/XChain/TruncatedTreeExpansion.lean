/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.CumulantMultilinear
public import WaveTurbulence.Foundations.XChain.SysDraft.Duhamel
/-! The exact finite ordered-forest expansion of the aTr cumulant (first step of T.cmattr). -/
@[expose] public section
namespace WaveTurbulence.Induct
open MeasureTheory Finset
open SysAPI
open scoped ENNReal

noncomputable def truncatedTrees (N : ℕ) : Finset TTree :=
  (Finset.range (N + 1)).biUnion treesOfOrder

abbrev TrTree (N : ℕ) := ↥(truncatedTrees N)

theorem mem_truncatedTrees {N : ℕ} {T : TTree} : T ∈ truncatedTrees N ↔ T.order ≤ N := by
  simp only [truncatedTrees, Finset.mem_biUnion, Finset.mem_range, mem_treesOfOrder]
  constructor
  · rintro ⟨n, hn, rfl⟩
    omega
  · intro h
    exact ⟨T.order, by omega, rfl⟩

theorem aTr_eq_sum_TrTree {d : ℕ} (L γ δ : ℝ) (p N : ℕ)
    (c : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) :
    aTr L γ δ p N c t n = ∑ T : TrTree N, treeTerm L γ δ p T.1 c t n := by
  calc
    _ = ∑ T ∈ truncatedTrees N, treeTerm L γ δ p T c t n := by
      unfold aTr
      simp only [treeTermN_eq_sum]
      unfold truncatedTrees
      rw [Finset.sum_biUnion]
      intro i _ j _ hij
      change Disjoint (treesOfOrder i) (treesOfOrder j)
      rw [Finset.disjoint_left]
      intro T hi hj
      exact hij ((mem_treesOfOrder.mp hi).symm.trans (mem_treesOfOrder.mp hj))
    _ = _ := (Finset.sum_coe_sort (truncatedTrees N) (fun T => treeTerm L γ δ p T c t n)).symm

theorem zpowSign_sum {α : Type*} (s : Finset α) (f : α → ℂ) (ζ : ℤˣ) :
    zpowSign ζ (∑ a ∈ s, f a) = ∑ a ∈ s, zpowSign ζ (f a) := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact map_sum (starRingEnd ℂ) _ _

/-- The signed truncated cumulant is a finite sum indexed by the literal ordered top forests.
The moment side condition is retained explicitly until the tree estimates discharge it. -/
theorem cumulant_aTr_eq_sum_forests {d : ℕ} {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (L γ δ : ℝ) (p N : ℕ) (c : Ω → (Fin d → ℤ) → ℂ) (t : ι → ℝ)
    (n : ι → (Fin d → ℤ)) (ζ : ι → ℤˣ)
    (hX : ∀ i (T : TrTree N), ∀ q : ℕ, 1 ≤ q →
      MemLp (fun ω => treeTerm L γ δ p T.1 (c ω) (t i) (n i)) (q : ℝ≥0∞) μ) :
    cumulant μ (fun i ω => zpowSign (ζ i) (aTr L γ δ p N (c ω) (t i) (n i))) univ =
      ∑ f : ι → TrTree N, cumulant μ
        (fun i ω => zpowSign (ζ i) (treeTerm L γ δ p (f i).1 (c ω) (t i) (n i))) univ := by
  simp_rw [aTr_eq_sum_TrTree, zpowSign_sum]
  apply cumulant_fintype_sum
  intro i T q hq
  unfold zpowSign
  split_ifs
  · exact hX i T q hq
  · exact (hX i T q hq).star

end WaveTurbulence.Induct
