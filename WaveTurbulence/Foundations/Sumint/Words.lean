/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.WaveB.FrozenB1
public import WaveTurbulence.Foundations.Fourier.MixedNorm
/-! Coordinate words and multiindices, checked against snapshot 3. -/
public section
namespace WaveTurbulence.NormBridgeScratch
open scoped ContDiff

@[expose] noncomputable def wordD {d : ℕ} : List (Fin d) → (Mom d → ℂ) → Mom d → ℂ
  | [], f => f
  | j :: l, f => partialMom j (wordD l f)

theorem wordD_contDiff {d : ℕ} (l : List (Fin d)) (N : ℕ) {f : Mom d → ℂ}
    (hf : ContDiff ℝ (N + l.length : ℕ) f) : ContDiff ℝ N (wordD l f) := by
  induction l generalizing N with
  | nil => simpa only [List.length_nil, Nat.add_zero, wordD] using hf
  | cons j l ih =>
    have h : ContDiff ℝ ((N + 1) + l.length : ℕ) f := by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hf
    have ht := ih (N + 1) h
    change ContDiff ℝ N (fun x => fderiv ℝ (wordD l f) x (EuclideanSpace.single j 1))
    exact (ht.fderiv_right (m := N) (by simp)).clm_apply contDiff_const

theorem partialMom_comm {d : ℕ} {f : Mom d → ℂ} (hf : ContDiff ℝ 2 f) (i j : Fin d) :
    partialMom i (partialMom j f) = partialMom j (partialMom i f) := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  funext x
  unfold partialMom
  rw [fderiv_clm_apply (hd x) (differentiableAt_const _), fderiv_clm_apply (hd x) (differentiableAt_const _)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] using
    (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem wordD_perm {d : ℕ} {l l' : List (Fin d)} (h : l.Perm l') {f : Mom d → ℂ}
    (hf : ContDiff ℝ l.length f) : wordD l f = wordD l' f := by
  induction h generalizing f with
  | nil => rfl
  | @cons a l l' h ih =>
    have ht : ContDiff ℝ l.length f := hf.of_le (by exact_mod_cast Nat.le_succ l.length)
    simp only [wordD, ih ht]
  | swap a b l =>
    have ht : ContDiff ℝ (2 + l.length : ℕ) f := by
      simpa only [List.length_cons, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hf
    exact partialMom_comm (wordD_contDiff l 2 ht) b a
  | @trans l l' l'' h h' ih ih' =>
    exact (ih hf).trans (ih' (by simpa only [← h.length_eq] using hf))

theorem momentumDerivative_eq_wordD {d n : ℕ} (ρ : Fin n → Fin d) {f : Mom d → ℂ}
    (hf : ContDiff ℝ n f) : Fourier.momentumDerivative ρ f = wordD (List.ofFn ρ) f := by
  induction n with
  | zero => simp [Fourier.momentumDerivative_zero, List.ofFn_zero, wordD]
  | succ n ih =>
    have hn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hd : Differentiable ℝ (iteratedFDeriv ℝ n f) :=
      (hf.iteratedFDeriv_right (m := 1) (by simp [add_comm])).differentiable (by norm_num)
    rw [List.ofFn_succ, wordD]
    rw [← ih (fun i => ρ i.succ) hn]
    funext x
    unfold Fourier.momentumDerivative partialMom
    exact (hd x).iteratedFDeriv_succ_apply_left'

end WaveTurbulence.NormBridgeScratch
