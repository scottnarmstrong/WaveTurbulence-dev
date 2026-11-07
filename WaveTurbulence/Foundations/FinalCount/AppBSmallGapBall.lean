/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBSmallGapShell
public import WaveTurbulence.Foundations.FinalCount.AppBSmallGapProfile
public import WaveTurbulence.Foundations.CountLemmas.PairBallBox
public import WaveTurbulence.Foundations.CountLemmas.DyadicPacking

/-! # Appendix B small internal gaps down to the terminal lattice scale -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.Mole
open CountLemmas

/-- The small-ball part of DH23 A.2(1), with both radial powers retained.
No logarithmic number of shells is lost, including at γ=1/2. -/
theorem appb_pair_small_gap_ball_le {d : ℕ} (hd : 2 ≤ d)
    (s : Finset ((Fin d → ℤ) × (Fin d → ℤ)))
    {L τ R : ℝ} (hL : 1 ≤ L) (hτ : 0 ≤ τ) (hR : 0 < R) (hLR : 1 ≤ L*R)
    (b : Mom d) (α : ℝ)
    (hs : ∀ q ∈ s, ‖latticePoint L q.1‖ ≤ R ∧ NearLattice L b q.2 ∧
      |inner ℝ (latticePoint L q.1) (latticePoint L q.2)-α| ≤ τ) :
    let A := (3^d*L^d)*(3^(d-1)*L^(d-1))
    (s.card : ℝ) ≤ 15^d*L^d+2*A*R^d+2*(A*(4*(d : ℝ)*τ*L))*R^(d-1) := by
  classical
  dsimp only
  let A := (3^d*L^d)*(3^(d-1)*L^(d-1))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨J,hJ,hJnext⟩ := exists_nat_pow_near hLR (by norm_num : (1 : ℝ) < 2)
  have hpJ : 0 < (2 : ℝ)^J := by positivity
  have hterminal : L*(R/(2 : ℝ)^J) ≤ 2 := by
    have hh : L*R ≤ 2*(2 : ℝ)^J := by rw [pow_succ] at hJnext; linarith only [hJnext]
    simpa only [mul_div_assoc] using (div_le_iff₀ hpJ).mpr hh
  have hlow : (((s.filter (fun q => ‖latticePoint L q.1‖ ≤ R/(2 : ℝ)^J)).card) : ℝ) ≤ 15^d*L^d :=
    card_pair_terminal_ball_le _ hL (by positivity) hterminal b (by
      intro q hq
      exact ⟨(mem_filter.mp hq).2,(hs q (mem_filter.mp hq).1).2.1⟩)
  apply card_le_of_two_geometric_shell_bounds s (fun q => ‖latticePoint L q.1‖)
    hR.le hA (mul_nonneg hA (by positivity)) d (d-1) J (by omega) (by omega)
    (fun q hq => (hs q hq).1) hlow
  intro j hj
  let Rj := R/(2 : ℝ)^j
  have hRj : 0 < Rj := div_pos hR (by positivity)
  have hLRj : 1 ≤ L*Rj := by
    have hpow : (2 : ℝ)^j ≤ (2 : ℝ)^J := pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hj)
    have hh : 1 ≤ (L*R)/(2 : ℝ)^j := (le_div_iff₀ (by positivity : 0 < (2 : ℝ)^j)).mpr
      (by simpa only [one_mul] using hpow.trans hJ)
    simpa only [Rj,mul_div_assoc] using hh
  let t := s.filter (fun q => R/(2 : ℝ)^(j+1) < ‖latticePoint L q.1‖ ∧
    ‖latticePoint L q.1‖ ≤ R/(2 : ℝ)^j)
  have hc := appb_pair_radial_shell_le (by omega : 0 < d) t hLp hτ hRj b α (by
    intro q hq
    have hq' := mem_filter.mp hq
    have hh := hs q hq'.1
    refine ⟨?_,hq'.2.2,hh.2.1,hh.2.2⟩
    have heq : Rj/2 = R/(2 : ℝ)^(j+1) := by dsimp only [Rj]; rw [pow_succ]; ring
    rw [heq]
    exact hq'.2.1.le)
  have hp := appb_small_gap_shell_profile d (by omega) hL hRj hLRj
    (by positivity : 0 ≤ 4*(d : ℝ)*τ*L)
  have hh := hc.trans hp
  change (t.card : ℝ) ≤ _
  convert hh using 1
  simp only [A]
  ring

end WaveTurbulence.Mole
