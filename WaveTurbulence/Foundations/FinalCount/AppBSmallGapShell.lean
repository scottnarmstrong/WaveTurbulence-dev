/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.CountLemmas.DotStrip
public import WaveTurbulence.Foundations.Counting.FiniteFibers

/-! # Appendix B radial shells for a small internal gap -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Mole
open CountLemmas

/-- Fixing the first vector and slicing a dominant coordinate of the second
retains the small-radius factor needed in DH23 A.2(1). -/
theorem appb_pair_radial_shell_le {d : ℕ} (hd : 0 < d)
    (s : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    {L τ R : ℝ} (hL : 0 < L) (hτ : 0 ≤ τ) (hR : 0 < R)
    (b : Mom d) (α : ℝ)
    (hs : ∀ q ∈ s, R/2 ≤ ‖latticePoint L q.1‖ ∧ ‖latticePoint L q.1‖ ≤ R ∧
      NearLattice L b q.2 ∧ |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ) :
    (s.card : ℝ) ≤ (2*(L*R)+1)^d*
      ((2*L+1)^(d-1)*(4*(d : ℝ)*τ*L/R+1)) := by
  classical
  have hproj : ((s.image Prod.fst).card : ℝ) ≤ (2*(L*R)+1)^d := by
    let B := Counting.latticeBox (fun _ : Fin d => (0 : ℝ)) (L*R)
    have hsub : s.image Prod.fst ⊆ B := by
      intro n hn
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
      apply (Counting.mem_latticeBox _ _ _).mpr
      intro i
      simpa using coordinate_bound_of_ball hL (0 : Mom d) q.1
        (by simpa only [sub_zero] using (hs q hq).2.1) i
    exact (show ((s.image Prod.fst).card : ℝ) ≤ B.card from by exact_mod_cast card_le_card hsub).trans
      (Counting.card_latticeBox_le _ (mul_nonneg hL.le hR.le))
  have hfib : ∀ x ∈ s.image Prod.fst,
      (((s.filter (fun q => q.1 = x)).card) : ℝ) ≤
      (2*L+1)^(d-1)*(4*(d : ℝ)*τ*L/R+1) := by
    intro x hx
    let t := s.filter (fun q => q.1 = x)
    have hinj : Set.InjOn Prod.snd (t : Set ((Fin d → ℤ) × (Fin d → ℤ))) := by
      intro q hq p hp he
      exact Prod.ext ((mem_filter.mp hq).2.trans (mem_filter.mp hp).2.symm) he
    rw [← card_image_of_injOn hinj]
    have hnorm : R/2 ≤ ‖latticePoint L x‖ := by
      obtain ⟨q,hq,hx⟩ := mem_image.mp hx
      rw [← hx]
      exact (hs q hq).1
    have hb := card_dot_strip_ball_norm_le hd (t.image Prod.snd) hL (by norm_num : (0 : ℝ) ≤ 1)
      hτ (by positivity : 0 < R/2) b (latticePoint L x) α hnorm
      (by
        intro n hn
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
        exact (hs q (mem_filter.mp hq).1).2.2.1)
      (by
        intro n hn
        obtain ⟨q,hq,rfl⟩ := mem_image.mp hn
        rw [← (mem_filter.mp hq).2]
        exact (hs q (mem_filter.mp hq).1).2.2.2)
    convert hb using 1; ring
  have hc := Counting.card_le_image_card_mul_of_fiber_le s Prod.fst hfib
  exact hc.trans (mul_le_mul_of_nonneg_right hproj (by positivity))

end WaveTurbulence.Mole
