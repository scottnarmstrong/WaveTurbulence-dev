/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeNstarBound
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeTimeFactor

/-! # One uniform constant for both literal dominant-tree factors -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links TTree

/-- Both literal dominant-tree factors satisfy the source estimates with one constant
before every code, sign, order and logarithmic cutoff. -/
theorem exists_tree_dominant_factor_bounds {d : ℕ} (hd : 3 ≤ d) {η B : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ F : Mom d → ℝ,
      Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B →
      ∀ X : RegChain, X.wf = true → X.dominant = true → ∀ n : ℕ, X.size=2*n →
      ∀ ζ : ℤˣ, ∀ T : Set (Fin 2 → ℝ),
      (∀ t ∈ T, ∀ i, t i ∈ Set.Icc (0:ℝ) 1) → (∀ t ∈ T, t 1 ≤ t 0) →
      XNorm00Restr (V := Unit) (1-η) T Set.univ
        (fun ts _ => (X.JBtree 0 (ts 0) (ts 1):ℂ)) ≤ ENNReal.ofReal (C*C^n) ∧
      ∀ Z : Finset (Fin 1 × Path), IsSpecialSet (X.treeLinks ζ) Z →
        Fourier.spatialNorm (30*d) 0 (fun k => (X.Nstar F Z ζ ((0:Fin 1),[]) k:ℂ)) ≤
          ENNReal.ofReal (C*C^n) := by
  obtain ⟨Ct,hCt,ht⟩ := exists_tree_JB_time_bound hη hη1
  obtain ⟨Cs,hCs,hs⟩ := literal_Nstar_spatial_bound hd hB
  let C := max Ct Cs
  have hC : 1 ≤ C := hCt.trans (le_max_left _ _)
  have hb (a : ℝ) (ha : 1 ≤ a) (haC : a ≤ C) (n : ℕ) : a*a^n ≤ C*C^n :=
    mul_le_mul haC (pow_le_pow_left₀ (zero_le_one.trans ha) haC n)
      (pow_nonneg (zero_le_one.trans ha) _) (zero_le_one.trans hC)
  refine ⟨C,hC,?_⟩
  intro F hF X hwf hdom n hsize ζ T hT htri
  refine ⟨(ht X n hsize T hT htri).trans (ENNReal.ofReal_le_ofReal
    (hb Ct hCt (le_max_left _ _) n)),?_⟩
  intro Z hZ
  exact (hs X hwf hdom n hsize ζ F hF Z hZ).trans (ENNReal.ofReal_le_ofReal
    (hb Cs hCs (le_max_right _ _) n))

end WaveTurbulence.RegAsymp
