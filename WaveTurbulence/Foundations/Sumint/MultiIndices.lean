/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Sumint.Words
/-! Canonical words for coordinate multiindices. -/
public section
namespace WaveTurbulence.NormBridgeScratch
open Finset
open scoped Classical

@[expose] def canonical {d : ℕ} (ρ : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap (fun j => List.replicate (ρ j) j)

theorem canonical_count {d : ℕ} (ρ : Fin d → ℕ) (j : Fin d) : (canonical ρ).count j = ρ j := by
  simp [canonical, List.count_flatMap, List.count_replicate, ← List.ofFn_eq_map, List.sum_ofFn]

theorem canonical_length {d : ℕ} (ρ : Fin d → ℕ) : (canonical ρ).length = ∑ j, ρ j := by
  simp [canonical, List.length_flatMap, ← List.ofFn_eq_map, List.sum_ofFn]

theorem canonical_counts_perm {d : ℕ} (l : List (Fin d)) :
    (canonical (fun j => l.count j)).Perm l :=
  List.perm_iff_count.mpr (fun j => canonical_count _ j)

theorem sum_counts {d : ℕ} (l : List (Fin d)) : (∑ j, l.count j) = l.length := by
  simpa only [canonical_length] using (canonical_counts_perm l).length_eq

theorem wordD_append {d : ℕ} (l l' : List (Fin d)) (f : Mom d → ℂ) :
    wordD (l ++ l') f = wordD l (wordD l' f) := by
  induction l with
  | nil => rfl
  | cons j l ih => simp only [List.cons_append, wordD, ih]

theorem wordD_replicate {d : ℕ} (j : Fin d) (n : ℕ) (f : Mom d → ℂ) :
    wordD (List.replicate n j) f = (partialMom j)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, wordD, ih, Function.iterate_succ_apply']

theorem iterPartial_eq_wordD {d : ℕ} (ρ : Fin d → ℕ) (f : Mom d → ℂ) :
    iterPartial ρ f = wordD (canonical ρ) f := by
  unfold iterPartial canonical
  generalize List.finRange d = l
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, List.flatMap_cons, wordD_append, wordD_replicate, ih]

theorem momentumDerivative_eq_iterPartial_counts {d n : ℕ} (ρ : Fin n → Fin d)
    {f : Mom d → ℂ} (hf : ContDiff ℝ n f) :
    Fourier.momentumDerivative ρ f = iterPartial (fun j => (List.ofFn ρ).count j) f := by
  rw [momentumDerivative_eq_wordD ρ hf, iterPartial_eq_wordD]
  exact wordD_perm (canonical_counts_perm (List.ofFn ρ)).symm (by simpa using hf)

theorem iterPartial_eq_momentumDerivative_canonical {d : ℕ} (ρ : Fin d → ℕ)
    {f : Mom d → ℂ} (hf : ContDiff ℝ (∑ j, ρ j : ℕ) f) :
    iterPartial ρ f = Fourier.momentumDerivative (canonical ρ).get f := by
  rw [momentumDerivative_eq_wordD _ (by simpa only [canonical_length] using hf)]
  rw [List.ofFn_get, iterPartial_eq_wordD]
end WaveTurbulence.NormBridgeScratch
