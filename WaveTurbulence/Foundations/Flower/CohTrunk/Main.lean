/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CohTrunk.Tree

/-!
# COH-TRUNK: the exports `RowTopAgreementCoupleR` and `RowTopAgreementTree` (supplement Lemma 5.1)

On a coherent regular couple the frontier weight `rowTopWeightR` has a single factor: `g j` at the momentum `k`
of the arm `j` whose root parent layer is `p` and whose object lies below `p` (exponent `c(q, q') ∈ {0, 1}` per
arm).  On a coherent regular tree it is `g k` iff `q' < p = q`, else `1`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.CohTrunk
open WaveTurbulence WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.LGSpine WaveTurbulence.PL234 TTree

theorem kernel_decoration {w d : ℕ} (G : Garden w) (L : ℝ) (k : Mom d) (n : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) (κ : GenDecoration G d n nfl) :
    IsDecoration G (cosetDecoration G L k κ.1) :=
  isDecoration_cosetDecoration G L k κ.1 κ.2.1

theorem latticePoint_zero' {d : ℕ} (L : ℝ) : latticePoint (d := d) L (fun _ => 0) = 0 := by
  ext i
  simp [latticePoint]

theorem coset_root {w d : ℕ} (G : Garden w) (L : ℝ) (k : Mom d) (nfl : Fin d → ℤ)
    (κ : GenDecoration G d (fun _ => 0) nfl) (j : Fin w) :
    cosetDecoration G L k κ.1 (GNode.root G.tree j) = k := by
  show k + latticePoint L (κ.1 (GNode.root G.tree j)) = k
  rw [κ.2.2.1 j]
  show k + latticePoint L (fun _ => 0) = k
  rw [latticePoint_zero', add_zero]

/-- **Lemma 5.1 (couples, per arm)**: `RowTopAgreementCoupleR`. -/
theorem rowTopAgreementCoupleR : Stage1W.RowTopAgreementCoupleR := by
  intro d p q q' Q LG hqp hq'p hcoh g L k κ
  have hK := kernel_decoration LG.garden L k _ _ κ
  have hKr := coset_root LG.garden L k 0 κ
  have key : CoupleCrossConcl LG p q q' k (cosetDecoration LG.garden L k κ.1) := by
    by_cases ht : Q.isType2 = true
    · rcases Q with _ | ⟨c, Q1, Q2, Q3⟩ | ⟨Xp, Xm, Qlp⟩
      · simp [RegCpl.isType2] at ht
      · simp [RegCpl.isType2] at ht
      · exact coupleCross_t2 hcoh hqp hq'p _ hK hKr
    · exact coupleCross_nt hcoh hqp hq'p (by simpa using ht) _ hKr
  by_cases h1 : q' < p ∧ q = p
  · obtain ⟨z0, hz0, hKz, hcr⟩ := key.1 h1
    rw [rowTopWeightR_single g _ _ z0 hcr, hz0, hKz, if_pos h1]
  · by_cases h2 : q < p ∧ q' = p
    · obtain ⟨z0, hz0, hKz, hcr⟩ := key.2.1 h2
      rw [rowTopWeightR_single g _ _ z0 hcr, hz0, hKz, if_neg h1, if_pos h2]
    · rw [rowTopWeightR_one g _ _ (key.2.2 h1 h2), if_neg h1, if_neg h2]

/-- **Lemma 5.1 (trees)**: `RowTopAgreementTree`. -/
theorem rowTopAgreementTree : Stage1W.RowTopAgreementTree := by
  intro d p q q' X LG hq'q hqp hcoh g L k κ
  have hK := kernel_decoration LG.garden L k _ _ κ
  have hKr := coset_root LG.garden L k 0 κ
  have key := treeCross hcoh hq'q hqp _ hK hKr
  by_cases h1 : q' < p ∧ q = p
  · obtain ⟨z0, hKz, hcr⟩ := key.1 h1
    show Stage1W.rowTopWeightR p (fun _ => g) LG ![q] _ = _
    rw [rowTopWeightR_single (fun _ => g) _ _ z0 hcr, hKz, if_pos h1]
  · show Stage1W.rowTopWeightR p (fun _ => g) LG ![q] _ = _
    rw [rowTopWeightR_one (fun _ => g) _ _ (key.2 h1), if_neg h1]

end WaveTurbulence.Flower.CohTrunk
