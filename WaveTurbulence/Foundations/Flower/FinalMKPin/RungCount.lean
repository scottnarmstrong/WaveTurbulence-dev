/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.Loc
public import WaveTurbulence.Foundations.Flower.FinalMKPin.Box
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: counting the retained rungs and the segments

Per maximal ladder `S` let `hS` be the number of rungs (among `0..m`) meeting a non-clock branch.
- The retained `X` rungs number at least `m - d - 1 - hS` on a small ladder (`m_le_sumKq`): main's `CD.m_le_Kn`
  minus the removed rungs (o73: "at most `h ≤ 4r` variables are removed from the source X").
- The nonempty segments number at most `1 + hS` (`card_seg_nonzero_le`): a bad rung contains a pinned branch.
- `∑_S hS ≤ |E₀|` (`sum_hS_le`): distinct removed rungs carry distinct non-clock branches. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LadderDisjoint
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w : ℕ} {G : Garden w}
variable {fix : GBranch G.tree → Option ℝ} {face : GBranch G.tree → Option (GBranch G.tree)} {π0 : PF G}

/-- The rungs of `S` meeting a non-clock branch. -/
noncomputable def hS (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (π0 : PF G) (S : LQ G) : ℕ :=
  ((Finset.range (π0.m S + 1)).filter fun j => ¬ rungFree fix face π0 S j).card

theorem segN_le (S : LQ G) (j : ℕ) : segN fix π0 S j ≤ j := by
  unfold segN
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem segN_le_hS (S : LQ G) {j : ℕ} (hj : j ≤ π0.m S + 1) : segN fix π0 S j ≤ hS fix face π0 S := by
  unfold segN hS
  refine Finset.card_le_card fun k hk => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  refine ⟨by omega, fun hfree => ?_⟩
  rcases hk.2 with ⟨p, _, hpin, _⟩ | ⟨p, _, hpin, _⟩
  · exact hpin hfree.1.1
  · exact hpin hfree.2.1

section counts
variable {JS : LQ G → Finset ℕ} (hJS : ∀ S j, j ∈ JS S → 1 ≤ j ∧ j < π0.m S)
include hJS

theorem sum_Kq_eq (S : LQ G) :
    ∑ k : Fin (π0.m S + 1), Kq fix face π0 JS ⟨S, k⟩ = ((JS S).filter (rungFree fix face π0 S)).card := by
  set s := (JS S).filter (rungFree fix face π0 S)
  let f : ℕ → Fin (π0.m S + 1) := fun j => ⟨min (segN fix π0 S j) (π0.m S), by omega⟩
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold Kq JSk
  congr 1
  ext j
  simp only [Finset.mem_filter, s, f]
  constructor
  · rintro ⟨hj, hfr, hseg⟩
    refine ⟨⟨hj, hfr⟩, Fin.ext ?_⟩
    simp only
    rw [hseg]; exact min_eq_left (by have := k.2; omega)
  · rintro ⟨⟨hj, hfr⟩, hk⟩
    refine ⟨hj, hfr, ?_⟩
    have h1 := (hJS S j hj).2
    have h2 := segN_le (fix := fix) (π0 := π0) S j
    rw [← hk]; simp only; exact (min_eq_left (by omega)).symm

theorem sum_Kq_le (S : LQ G) : ∑ k : Fin (π0.m S + 1), Kq fix face π0 JS ⟨S, k⟩ ≤ π0.m S := by
  rw [sum_Kq_eq hJS]
  refine (Finset.card_filter_le _ _).trans ((Finset.card_le_card fun j hj => ?_).trans (by simp : (Finset.range (π0.m S)).card ≤ π0.m S))
  simp only [Finset.mem_range]; exact (hJS S j hj).2

theorem card_JS_le (S : LQ G) :
    (JS S).card ≤ ∑ k : Fin (π0.m S + 1), Kq fix face π0 JS ⟨S, k⟩ + hS fix face π0 S := by
  rw [sum_Kq_eq hJS, ← Finset.card_filter_add_card_filter_not (s := JS S) (rungFree fix face π0 S)]
  refine Nat.add_le_add_left (Finset.card_le_card fun j hj => ?_) _
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  exact ⟨by have := (hJS S j hj.1).2; omega, hj.2⟩

theorem card_seg_nonzero_le (S : LQ G) :
    ((Finset.univ : Finset (Fin (π0.m S + 1))).filter fun k => Kq fix face π0 JS ⟨S, k⟩ ≠ 0).card ≤
      hS fix face π0 S + 1 := by
  calc ((Finset.univ : Finset (Fin (π0.m S + 1))).filter fun k => Kq fix face π0 JS ⟨S, k⟩ ≠ 0).card
      ≤ ((Finset.univ : Finset (Fin (π0.m S + 1))).filter fun k => k.val ≤ hS fix face π0 S).card := by
        refine Finset.card_le_card fun k hk => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
        obtain ⟨i⟩ : Nonempty (Fin (Kq fix face π0 JS ⟨S, k⟩)) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
        have hsp := enumq_spec (JS := JS) (fix := fix) (face := face) ⟨S, k⟩ i
        rw [← hsp.2.2]
        exact segN_le_hS S (by have := (hJS S _ hsp.1).2; omega)
    _ ≤ ((Finset.range (hS fix face π0 S + 1)).image (fun n => n)).card := by
        refine Finset.card_le_card_of_injOn (fun k => k.val) (fun k hk => ?_) (fun a _ b _ h => Fin.ext h)
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hk
        simp only [Finset.coe_image, Finset.coe_range, Set.image_id', Set.mem_Iio]; omega
    _ ≤ hS fix face π0 S + 1 := by simp

end counts

/-- Distinct removed rungs carry distinct non-clock branches. -/
theorem sum_hS_le : ∑ S : LQ G, hS fix face π0 S ≤ (E0 fix face).card := by
  set T : Finset (Σ S : LQ G, ℕ) :=
    Finset.univ.sigma fun S => (Finset.range (π0.m S + 1)).filter fun j => ¬ rungFree fix face π0 S j with hT
  have hcard : ∑ S : LQ G, hS fix face π0 S = T.card := by rw [hT, Finset.card_sigma]; rfl
  rw [hcard]
  let f : (Σ S : LQ G, ℕ) → GBranch G.tree := fun p =>
    atomAt π0 p.1 (decide (fix (rowN (π0.u p.1) p.2) = none ∧ face (rowN (π0.u p.1) p.2) = none) = false) p.2
  refine Finset.card_le_card_of_injOn f (fun p hp => ?_) (fun p hp q hq h => ?_)
  · rw [Finset.mem_coe, Finset.mem_sigma] at hp
    obtain ⟨-, hp⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    simp only [Finset.mem_coe, E0, Finset.mem_filter, Finset.mem_univ, true_and, f, atomAt]
    by_cases hu : fix (rowN (π0.u p.1) p.2) = none ∧ face (rowN (π0.u p.1) p.2) = none
    · simp only [hu, and_self, decide_true, Bool.true_eq_false]
      exact fun hv => hp.2 ⟨hu, hv⟩
    · simp only [hu, decide_false]; exact hu
  · rw [Finset.mem_coe, Finset.mem_sigma] at hp hq
    simp only [Finset.mem_filter, Finset.mem_range] at hp hq
    obtain ⟨h1, h2, h3⟩ := atomAt_inj π0 p.1 q.1 _ _ (by omega) (by omega) h
    obtain ⟨S, j⟩ := p
    obtain ⟨S', j'⟩ := q
    simp only at h1 h3
    subst h1 h3
    rfl

end WaveTurbulence.Flower.FinalMKPin
