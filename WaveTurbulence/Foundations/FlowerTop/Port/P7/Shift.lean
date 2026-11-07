/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSum
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Trunc
/-! FLOWER-P7: a plain couple kernel with equal root labels `m` at base `k` is the kernel with root labels `0`
at base `k + m/L`; unequal root labels give `0`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {w d : ℕ}

theorem epsCoef_sub {d : ℕ} (x y z m : Fin d → ℤ) : epsCoef (x - m) (y - m) (z - m) = epsCoef x y z := by
  unfold epsCoef
  simp only [sub_left_inj, ne_eq]

theorem epsDec_shift (G : Garden w) (κ : GNode G.tree → (Fin d → ℤ)) (m : Fin d → ℤ) :
    epsDec G (fun a => κ a - m) = epsDec G κ := by
  unfold epsDec
  exact Finset.prod_congr rfl fun b _ => epsCoef_sub _ _ _ m

/-- Translation of decorations by the constant label `m` (plain gardens: no flower condition). -/
def shiftDec (G : Garden w) (hP : G.IsPlain) (m : Fin d → ℤ) :
    GenDecoration G d (fun _ => m) 0 ≃ GenDecoration G d (fun _ => 0) 0 where
  toFun κ := ⟨fun a => κ.1 a - m, ⟨fun b => by
      have := κ.2.1.1 b
      simp only [this]; abel, fun ℓ => by simp [κ.2.1.2 ℓ]⟩,
    fun j => by simp [κ.2.2.1 j],
    fun ℓ hℓ => absurd hℓ (by rw [Garden.IsFlower, hP ℓ]; simp)⟩
  invFun κ := ⟨fun a => κ.1 a + m, ⟨fun b => by
      have := κ.2.1.1 b
      simp only [this]; abel, fun ℓ => by simp [κ.2.1.2 ℓ]⟩,
    fun j => by simp [κ.2.2.1 j],
    fun ℓ hℓ => absurd hℓ (by rw [Garden.IsFlower, hP ℓ]; simp)⟩
  left_inv κ := by apply Subtype.ext; funext a; simp
  right_inv κ := by apply Subtype.ext; funext a; simp

theorem latticePoint_sub (L : ℝ) (x y : Fin d → ℤ) :
    latticePoint L (x - y) = latticePoint L x - latticePoint L y := by
  ext j
  simp [latticePoint, sub_div]

theorem kgTerm_shift (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (k : Mom d)
    (m : Fin d → ℤ) (κ : GNode LG.garden.tree → (Fin d → ℤ)) :
    kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) up k κ =
      kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) up (k + latticePoint L m) (fun a => κ a - m) := by
  unfold kgTerm
  have hc : cosetDecoration LG.garden L (k + latticePoint L m) (fun a => κ a - m) =
      cosetDecoration LG.garden L k κ := by
    funext a
    simp only [cosetDecoration, latticePoint_sub]
    abel
  rw [hc, epsDec_shift]

/-- Equal root labels `m` at base `k` are root labels `0` at base `k + m/L` (plain gardens). -/
theorem kernelKgen_shift (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (hP : LG.garden.IsPlain)
    (up : GBranch LG.garden.tree → ℝ) (k : Mom d) (m : Fin d → ℤ) :
    kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) up k (fun _ => m) 0 =
      kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) up (k + latticePoint L m) (fun _ => 0) 0 := by
  rw [kernelKgen_eq_tsum, kernelKgen_eq_tsum]
  congr 1
  rw [← (shiftDec LG.garden hP m).tsum_eq]
  refine tsum_congr fun κ => ?_
  exact kgTerm_shift L γ δ F LG up k m κ.1

/-- A plain couple kernel vanishes for unequal root labels. -/
theorem couple_kernel_offdiag (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (hP : LG.garden.IsPlain)
    (hsig : LG.garden.sig = ![1, -1]) (up : GBranch LG.garden.tree → ℝ) (k : Mom d) (n : Fin 2 → (Fin d → ℤ)) (h : n 0 ≠ n 1) :
    kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) up k n 0 = 0 := by
  have hE := Canon.isEmpty_genDecoration_of_unbalanced LG.garden hP n 0 (by
    rw [Fin.sum_univ_two, hsig]
    simpa [sub_eq_add_neg] using sub_ne_zero.2 h)
  rw [kernelKgen_eq_tsum, tsum_empty, mul_zero]

end WaveTurbulence.FlowerP7
