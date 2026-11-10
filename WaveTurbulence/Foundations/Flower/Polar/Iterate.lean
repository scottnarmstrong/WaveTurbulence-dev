/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Norms
/-! # FL-POLAR: iterating the root form.  One round multiplies by `1 + |x|^2`, using two applications
for the same tree; the norm invariant `Adm` tracks the weight cost, and the final bound is by induction on
the list of rounds. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

variable {w d : ℕ}

/-- The perturbed profile of the `m`-th evaluation of the central difference. -/
def pert (j : Fin w) (i : Fin d) (g : TProf d w) (lam : ℝ) (M m : ℕ) : TProf d w :=
  TProf.perturb g (polForm ((-1 : ℝ) ^ (j : ℕ)) j i g) (lam * ((m : ℝ) - M))

theorem Adm.pert_step {p A B : ℕ} {j : Fin w} {os : List (Fin w)} {u : ℝ} {g : TProf d w}
    (h : Adm p A B (j :: os) u g) (hu : 0 ≤ u) (i : Fin d) (lam : ℝ) (hlam : 0 < lam) (M m : ℕ)
    (hm : m ∈ range (2 * M + 1)) :
    Adm p A B os ((1 + lam * M * ((2 : ℝ) ^ A * (d : ℝ) ^ A)) * u) (pert j i g lam M m) := by
  have hm' : (m : ℝ) ≤ 2 * M := by
    have := mem_range.mp hm
    have : m ≤ 2 * M := by omega
    exact_mod_cast this
  have habs : |lam * ((m : ℝ) - M)| ≤ lam * M := by
    rw [abs_mul, abs_of_pos hlam]
    refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hlam.le
  have hσ : |((-1 : ℝ) ^ (j : ℕ))| ≤ 1 := by simp
  exact h.step hu _ hσ i _ _ habs

variable (P : WTParams) (hL : 1 ≤ P.L) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
  (dagger : Option (Fin w → Fin 3 → Mom P.d))
  (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (hW : ∀ LG k, |W LG k| ≤ 1)
  (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ)

include hL hW in
theorem app_step (A B : ℕ) (hB : P.d + 1 ≤ B) (M : ℕ) (hM : 1 ≤ M) (hMw : 2 * N + w ≤ 2 * M)
    (lam : ℝ) (hlam : 0 < lam) (j : Fin w) (i : Fin P.d) (os : List (Fin w)) (u : ℝ) (hu : 0 ≤ u)
    (g : TProf P.d w) (hg : Adm p A B (j :: os) u g) :
    (((latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') i : ℝ) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n' g =
      ∑ m ∈ range (2 * M + 1), ((CentralDiff.cw M m / lam : ℝ) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n' (pert j i g lam M m) := by
  have hu' : 0 ≤ (1 + lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A)) * u := by positivity
  refine Phi_polarize P hL p N kind pat dagger W hW ζ t s n n' j i g M hM hMw lam hlam.ne'
    ((1 + lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A)) * u) hu' ?_
  intro m hm q hq j1 j2
  obtain ⟨hcd, hn⟩ := (hg.pert_step hu i lam hlam M m hm) q hq j1 j2
  refine SNormR_mono_bound (Nat.zero_le _) ?_ _ hcd _ hu' hn
  omega

include hL hW in
theorem round_identity (A B : ℕ) (hB : P.d + 1 ≤ B) (M : ℕ) (hM : 1 ≤ M) (hMw : 2 * N + w ≤ 2 * M)
    (lam : ℝ) (hlam : 0 < lam) (j : Fin w) (os : List (Fin w)) (u : ℝ) (hu : 0 ≤ u)
    (g : TProf P.d w) (hg : Adm p A B (j :: j :: os) u g) :
    (((1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2 : ℝ)) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n' g =
      Phi P p N kind pat dagger W ζ t s n n' g +
        ∑ i : Fin P.d, ∑ m ∈ range (2 * M + 1), ∑ m' ∈ range (2 * M + 1),
          ((CentralDiff.cw M m / lam : ℝ) : ℂ) * ((CentralDiff.cw M m' / lam : ℝ) : ℂ) *
            Phi P p N kind pat dagger W ζ t s n n' (pert j i (pert j i g lam M m) lam M m') := by
  set X0 : Mom P.d := latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n' with hX0
  have hu1 : 0 ≤ (1 + lam * M * ((2 : ℝ) ^ A * (P.d : ℝ) ^ A)) * u := by positivity
  have hnorm : ‖X0‖ ^ 2 = ∑ i : Fin P.d, (X0 i) ^ 2 := EuclideanSpace.real_norm_sq_eq X0
  have hsum : ((1 + ‖X0‖ ^ 2 : ℝ) : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g =
      Phi P p N kind pat dagger W ζ t s n n' g +
        ∑ i : Fin P.d, (X0 i : ℂ) * ((X0 i : ℂ) * Phi P p N kind pat dagger W ζ t s n n' g) := by
    rw [hnorm]
    push_cast
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [app_step P hL p N kind pat dagger W hW ζ t s n n' A B hB M hM hMw lam hlam j i (j :: os) u hu g hg,
    Finset.mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hgm := hg.pert_step hu i lam hlam M m hm
  rw [← mul_assoc, mul_comm (X0 i : ℂ), mul_assoc,
    app_step P hL p N kind pat dagger W hW ζ t s n n' A B hB M hM hMw lam hlam j i os _ hu1 _ hgm,
    Finset.mul_sum]
  refine sum_congr rfl fun m' _ => ?_
  ring

end WaveTurbulence.Flower.Polar
