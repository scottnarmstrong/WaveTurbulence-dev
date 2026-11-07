/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Step
/-! # FL-POLAR: one root-form application to the whole flower-weighted sum `Phi`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

variable {w : ℕ}

theorem Phi_polarize (P : WTParams) (hL : 1 ≤ P.L) (p N : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
    (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (hW : ∀ LG k, |W LG k| ≤ 1)
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (j : Fin w) (i : Fin P.d)
    (g : TProf P.d w) (M : ℕ) (hM : 1 ≤ M) (hMw : 2 * N + w ≤ 2 * M)
    (lam : ℝ) (hlam : lam ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ m ∈ range (2 * M + 1), ∀ q ≤ p, ∀ j1 j2,
      SNormR 0 (P.d + 1) (TProf.perturb g (polForm ((-1 : ℝ) ^ (j : ℕ)) j i g)
        (lam * ((m : ℝ) - M)) q j1 j2) ≤ ENNReal.ofReal C) :
    (((latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') i : ℝ) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n' g =
      ∑ m ∈ range (2 * M + 1), ((CentralDiff.cw M m / lam : ℝ) : ℂ) *
        Phi P p N kind pat dagger W ζ t s n n'
          (TProf.perturb g (polForm ((-1 : ℝ) ^ (j : ℕ)) j i g) (lam * ((m : ℝ) - M))) := by
  unfold Phi
  simp only [FC23.flowerWeighted_eq_sum]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun LG hLG => ?_
  have hmem := (FC23.flowerCarrier_finite P p N kind pat ζ).mem_toFinset.mp hLG
  obtain ⟨hH, -, hord, -, hfl, -⟩ := hmem
  have hcard : (inputLeaves LG.garden).card ≤ 2 * M := by
    have h1 : (inputLeaves LG.garden).card ≤ Fintype.card (GLeaf LG.garden.tree) := Finset.card_le_univ _
    rw [Comb.card_gleaf] at h1
    have h2 : LG.garden.order = ∑ j, (LG.garden.tree j).order := rfl
    omega
  have hσ : (((LG.garden.sig j : ℤˣ) : ℤ) : ℝ) = (-1 : ℝ) ^ (j : ℕ) := by
    rw [hH.1.2.2 j]; simp
  have := flowerKernel_polarize P hL p pat dagger W hW ζ t s n n' LG hH hfl j i _ hσ g M hM hcard lam hlam
    C hC hg
  exact this

end WaveTurbulence.Flower.Polar
