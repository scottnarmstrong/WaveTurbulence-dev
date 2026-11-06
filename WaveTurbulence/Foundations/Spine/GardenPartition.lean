/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
public import WaveTurbulence.Foundations.WaveB.RegularHeldOut
/-! TARGET L2055–2060: the actual finite couple sum splits into nonregular, incoherent and coherent parts. -/
@[expose] public section
namespace WaveTurbulence.LGSpine
open Finset
open scoped Classical

/-- TARGET Def defcoh L885–887, on the actual regular couple carrier and its structure code. -/
def IsCoherentCouple (LG : LayeredGarden 2) : Prop :=
  IsRegularCouple LG.garden ∧ ∃ Q : RegCpl,
    Q.wf = true ∧ Q.Decodes LG.garden ∧ LG.incoherency Q.links = 0

noncomputable def coupleCarrier (P : WTParams) (q N : ℕ) : Finset (LayeredGarden 2) :=
  (Canon.finite_truncSumC_support P q N).toFinset

noncomputable def nonregularCoupleSum (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (q N : ℕ) (t : ℝ) (k : Mom P.d) : ℂ :=
  ∑ LG ∈ (coupleCarrier P q N).filter (fun (LG : LayeredGarden 2) => ¬ IsRegularCouple LG.garden),
    KQ P.L P.γ P.δ F LG t k

noncomputable def incoherentCoupleSum (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (q N : ℕ) (t : ℝ) (k : Mom P.d) : ℂ :=
  ∑ LG ∈ (coupleCarrier P q N).filter (fun (LG : LayeredGarden 2) => IsRegularCouple LG.garden ∧ ¬ IsCoherentCouple LG),
    KQ P.L P.γ P.δ F LG t k

noncomputable def coherentCoupleSum (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (q N : ℕ) (t : ℝ) (k : Mom P.d) : ℂ :=
  ∑ LG ∈ (coupleCarrier P q N).filter IsCoherentCouple, KQ P.L P.γ P.δ F LG t k

/-- The terms (b),(c),(d) use a partition of the literal truncated carrier, with no truncation dropped. -/
theorem truncSumC_eq_three_parts (P : WTParams) (F : ℕ → Mom P.d → ℝ)
    (q N : ℕ) (t : ℝ) (k : Mom P.d) :
    truncSumC P F q N t k = nonregularCoupleSum P F q N t k +
      incoherentCoupleSum P F q N t k + coherentCoupleSum P F q N t k := by
  classical
  rw [Canon.truncSumC_eq_sum]
  change (∑ LG ∈ coupleCarrier P q N, KQ P.L P.γ P.δ F LG t k) = _
  unfold nonregularCoupleSum incoherentCoupleSum coherentCoupleSum
  simp only [sum_filter]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro LG _
  by_cases hr : IsRegularCouple LG.garden
  · by_cases hc : IsCoherentCouple LG <;> simp [hr, hc]
  · have hc : ¬ IsCoherentCouple LG := fun h => hr h.1
    simp [hr, hc]

/-- The remainder in B1.2 is exactly (b)+(c)+(d), including odd orders. -/
theorem coupleRemainder_eq_three_parts (P : WTParams) (R : ℕ → Mom P.d → ℝ)
    (p N : ℕ) (t : ℝ) :
    coupleRemainder P R p N t = fun k => nonregularCoupleSum P (inputsF P R) (p + 1) N t k +
      incoherentCoupleSum P (inputsF P R) (p + 1) N t k +
      (coherentCoupleSum P (inputsF P R) (p + 1) N t k -
        if Even N then (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p (N / 2) t k : ℂ) else 0) := by
  funext k
  unfold coupleRemainder
  rw [truncSumC_eq_three_parts]
  ring

end WaveTurbulence.LGSpine
