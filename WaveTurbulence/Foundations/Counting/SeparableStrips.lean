/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Counting.LinearStrip
public import WaveTurbulence.Foundations.Counting.LatticeBox
public import WaveTurbulence.Foundations.Counting.FiniteFibers
import Mathlib.Tactic

/-!
# Counting two independent linear strip coordinates

DH23 `estcross`: after fixing the dominant coordinate and the remaining free
coordinates, the two short integer relations constrain two separate integer
coordinates. The offsets may depend arbitrarily on the fixed coordinates.
-/

public section

namespace WaveTurbulence.Counting

/-- Product bound for two independent integer linear strips. -/
theorem card_two_linear_strips_le (s : Finset (Fin 2 → ℤ))
    {a b alpha beta rho : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hrho : 0 ≤ rho)
    (ha' : |a| ≤ rho) (hb' : |b| ≤ rho)
    (h₀ : ∀ n ∈ s, |a*(n 0:ℝ)-alpha| ≤ rho)
    (h₁ : ∀ n ∈ s, |b*(n 1:ℝ)-beta| ≤ rho) :
    (s.card:ℝ) ≤ (3*rho/|a|)*(3*rho/|b|) := by
  classical
  have hcoord (i : Fin 2) (A B : ℝ) (hA : A ≠ 0) (hA' : |A| ≤ rho)
      (h : ∀ n ∈ s, |A*(n i:ℝ)-B| ≤ rho) :
      ((s.image (fun n => n i)).card:ℝ) ≤ 3*rho/|A| := by
    apply card_linear_strip_le_of_abs_le _ hA hrho hA'
    intro k hk
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hk
    exact h n hn
  have hc₀ := hcoord 0 a alpha ha ha' h₀
  have hc₁ := hcoord 1 b beta hb hb' h₁
  have hc := card_le_prod_card_coordinate_images s
  rw [Fin.prod_univ_two] at hc
  have hcR : (s.card:ℝ) ≤ ((s.image (fun n => n 0)).card:ℝ)*((s.image (fun n => n 1)).card:ℝ) := by
    exact_mod_cast hc
  exact hcR.trans (mul_le_mul hc₀ hc₁ (Nat.cast_nonneg _) (by positivity))

/-- Fixing `d` box coordinates leaves the product of the two independent
strip counts. No relation or density conclusion is assumed. -/
theorem card_separable_strips_le {d : ℕ}
    (s : Finset ((Fin d → ℤ) × (Fin 2 → ℤ)))
    (c : Fin d → ℝ) (F G : (Fin d → ℤ) → ℝ)
    {a b rho L : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hrho : 0 ≤ rho)
    (ha' : |a| ≤ rho) (hb' : |b| ≤ rho) (hL : 0 ≤ L)
    (hbox : ∀ n ∈ s, ∀ i, |(n.1 i:ℝ)-c i| ≤ L)
    (h₀ : ∀ n ∈ s, |a*(n.2 0:ℝ)-F n.1| ≤ rho)
    (h₁ : ∀ n ∈ s, |b*(n.2 1:ℝ)-G n.1| ≤ rho) :
    (s.card:ℝ) ≤ (2*L+1)^d*((3*rho/|a|)*(3*rho/|b|)) := by
  classical
  let C : ℝ := (3*rho/|a|)*(3*rho/|b|)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hfiber (z : Fin d → ℤ) : ((s.filter (fun n => n.1 = z)).card:ℝ) ≤ C := by
    let t := s.filter (fun n => n.1 = z)
    let P := t.image Prod.snd
    have hinj : Set.InjOn Prod.snd (t : Set ((Fin d → ℤ) × (Fin 2 → ℤ))) := by
      intro p hp q hq he
      apply Prod.ext _ he
      exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm
    have he : P.card = t.card := Finset.card_image_of_injOn hinj
    rw [← he]
    apply card_two_linear_strips_le P (alpha := F z) (beta := G z) ha hb hrho ha' hb'
    · intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      have hp' := Finset.mem_filter.mp hp
      have hh := h₀ p hp'.1
      rw [hp'.2] at hh
      exact hh
    · intro n hn
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      have hp' := Finset.mem_filter.mp hp
      have hh := h₁ p hp'.1
      rw [hp'.2] at hh
      exact hh
  have hbase : ((s.image Prod.fst).card:ℝ) ≤ (2*L+1)^d := by
    apply card_le_of_coordinate_bounds _ c hL
    intro z hz i
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact hbox p hp i
  have hc := card_le_image_card_mul_of_fiber_le s Prod.fst (fun z _ => hfiber z)
  exact hc.trans (mul_le_mul_of_nonneg_right hbase hC)

end WaveTurbulence.Counting
