/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.SumProjection

/-! # Coupled triple counts at fixed sum variables -/

public section
open Finset Set
namespace WaveTurbulence.CountLemmas

/-- The chain counting problems reduce to the broad bilinear count and a
same-sign pair fiber. This retains both tolerance terms before scale algebra. -/
theorem exists_sum_triple_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ L τ : ℝ, 2 ≤ L → 0 < τ →
    1 ≤ τ*L^2 → 1/τ ≤ L^2 →
    ∀ a b c : Mom (d+2), ∀ nv : Fin (d+2) → ℤ, ∀ sel : Bool, ∀ α β : ℝ,
    ∀ s : Finset ((Fin (d+2) → ℤ) × (Fin (d+2) → ℤ) × (Fin (d+2) → ℤ)),
    (∀ q ∈ s, NearLattice L a q.1 ∧ NearLattice L b q.2.1 ∧ NearLattice L c q.2.2 ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1)-α| ≤ τ ∧
      |inner ℝ (latticePoint L (sumTripleProjection nv sel q).1)
        (latticePoint L q.2.2)-β| ≤ τ) →
    (s.card : ℝ) ≤ C*τ*L^(2*((d+2 : ℕ) : ℝ))*(2*L+1)^d*(2*τ*L^2+L) := by
  obtain ⟨C,hC,hband⟩ := exists_broad_bilinear_band_bound (d+2) (by omega)
  refine ⟨C*(6*Real.pi+1284002),by positivity,?_⟩
  intro L τ hL hτ hW hwin a b c nv sel α β s hs
  have hLp : 0 < L := by linarith only [hL]
  let f := sumTripleProjection nv sel
  let g := fun q : (Fin (d+2) → ℤ) × (Fin (d+2) → ℤ) × (Fin (d+2) → ℤ) => (q.1,q.2.1)
  let A := (2*L+1)^d*(6*Real.pi+1284002)*(2*τ*L^2+L)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hproj : ((s.image f).card : ℝ) ≤ C*τ*L^(2*((d+2 : ℕ) : ℝ)) := by
    apply hband L τ hL hτ hwin (a+b-latticePoint L nv-(if sel then c else 0)) c β (s.image f)
    intro p hp
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
    obtain ⟨ha,hb,hc,he₁,he₂⟩ := hs q hq
    exact ⟨sumTripleProjection_norm L a b c nv sel q ha hb hc,
      hc.trans (by norm_num),he₂⟩
  have hfib : ∀ p ∈ s.image f, (((s.filter (fun q => f q = p)).card) : ℝ) ≤ A := by
    intro p hp
    let t := s.filter (fun q => f q = p)
    have hi := sumTripleProjection_pair_injOn nv sel s p
    change (t.card : ℝ) ≤ A
    rw [← card_image_of_injOn hi]
    apply card_fixed_sum_band_le hLp hτ.le hW a b (p.1+nv+(if sel then p.2 else 0)) α (t.image g)
    intro xy hxy
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hxy
    obtain ⟨ha,hb,hc,he₁,he₂⟩ := hs q (mem_filter.mp hq).1
    exact ⟨ha,hb,sumTripleProjection_sum nv sel q p (mem_filter.mp hq).2,he₁⟩
  have hc := Counting.card_le_image_card_mul_of_fiber_le s f hfib
  calc
    _ ≤ ((s.image f).card : ℝ)*A := hc
    _ ≤ (C*τ*L^(2*((d+2 : ℕ) : ℝ)))*A := mul_le_mul_of_nonneg_right hproj hA
    _ = _ := by dsimp only [A]; ring

end WaveTurbulence.CountLemmas
