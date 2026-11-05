/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.SysDraft.API
/-! Equality on the time interval preserves the full classed solution predicate. -/
public section
namespace WaveTurbulence.Induct
open Set

theorem isASolution_congr {d : ℕ} {L γ δ T : ℝ} (hT : 0 ≤ T)
    {c : (Fin d → ℤ) → ℂ} {a b : ℝ → (Fin d → ℤ) → ℂ}
    (ha : IsASolution L γ δ T c a) (he : ∀ t ∈ Icc 0 T, b t = a t) :
    IsASolution L γ δ T c b := by
  refine ⟨(he 0 ⟨le_rfl, hT⟩).trans ha.1, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := ha.2.1
    refine ⟨C, fun t ht n => ?_⟩
    rw [he t ht]
    exact hC t ht n
  · intro t ht n
    have h := (ha.2.2 t ht n).congr (fun s hs => congrFun (he s hs) n) (congrFun (he t ht) n)
    rw [he t ht]
    exact h

end WaveTurbulence.Induct
