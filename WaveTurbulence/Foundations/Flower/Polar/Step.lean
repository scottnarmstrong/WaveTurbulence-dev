/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Kernel
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
/-! # FL-POLAR: one application of the root form to the flower-weighted sum, as a central-difference
combination of flower-weighted sums with perturbed pair-type profiles. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

variable {w : ℕ}

theorem mark_ne_lower_of_flowerGarden (G : Garden w) (hFG : G.IsFlowerGarden) :
    ∀ ℓ, G.mark ℓ ≠ some MarkTag.lower := by
  intro ℓ h
  have hne : G.mark ℓ ≠ none := by rw [h]; exact Option.some_ne_none _
  have : G.mark ℓ = some MarkTag.equal := hFG.2.1 ℓ hne
  rw [h] at this
  exact absurd (Option.some.inj this) (by decide)

theorem flowerKernel_polarize (P : WTParams) (hL : 1 ≤ P.L) (p : ℕ) (pat : Fin w → FixPat)
    (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (W : ∀ LG : LayeredGarden w, (GNode LG.garden.tree → Mom P.d) → ℝ) (hW : ∀ LG k, |W LG k| ≤ 1)
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (LG : LayeredGarden w)
    (hH : IsCanonH (p + 1) LG)
    (hfl : ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
      LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1)
    (j : Fin w) (i : Fin P.d) (σ : ℝ) (hσ : (((LG.garden.sig j : ℤˣ) : ℤ) : ℝ) = σ)
    (g : TProf P.d w) (M : ℕ) (hM : 1 ≤ M) (hcard : (inputLeaves LG.garden).card ≤ 2 * M)
    (lam : ℝ) (hlam : lam ≠ 0) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ m ∈ range (2 * M + 1), ∀ q ≤ p, ∀ j1 j2,
      SNormR 0 (P.d + 1) (TProf.perturb g (polForm σ j i g) (lam * ((m : ℝ) - M)) q j1 j2) ≤
        ENNReal.ofReal C) :
    (((latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') i : ℝ) : ℂ) *
        FC23.flowerKernel P (fun _ _ => 1) p pat dagger (fun LG k => W LG k * leafProd LG g k) t s n n' LG =
      ∑ m ∈ range (2 * M + 1), ((CentralDiff.cw M m / lam : ℝ) : ℂ) *
        FC23.flowerKernel P (fun _ _ => 1) p pat dagger
          (fun LG k => W LG k *
            leafProd LG (TProf.perturb g (polForm σ j i g) (lam * ((m : ℝ) - M))) k) t s n n' LG := by
  have hFG : LG.garden.IsFlowerGarden := hH.1
  have hn := mark_ne_lower_of_flowerGarden LG.garden hFG
  have hmarks : ∀ ℓ, LG.garden.mark ℓ ≠ none → LG.garden.IsFlower ℓ := hFG.2.1
  have hone : ∀ j : Fin w, (univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsFlower ℓ).card = 1 := by
    intro j
    rw [← hFG.1 j]
    congr 1
    ext ℓ
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      intro h0
      have : LG.garden.mark ℓ = some MarkTag.equal := h2
      rw [h0] at this
      exact absurd this (by simp)
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hmarks ℓ h2⟩
  have hlayer : ∀ a, LG.layer a ≤ p := Canon.layer_le_of_isCanonH hH
  unfold FC23.flowerKernel
  refine kernelKgen_linear_step P.L P.γ P.δ (fun _ _ => 1) LG _ _ _ 0 (fun _ => n) n'
    (range (2 * M + 1)) (fun m => CentralDiff.cw M m / lam)
    (((latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') i : ℝ)) _ _ ?_ ?_
  · intro κ
    beta_reduce
    have hX := flower_root_coord LG P.L 0 (fun _ => n) n' ζ hfl hmarks κ j (hone j)
      (by simp) i
    rw [hσ] at hX
    have hlp := leafProd_polarize LG σ j i g (cosetDecoration LG.garden P.L 0 κ.1) _ hX.symm M hM hcard
      lam hlam
    generalize (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') i = x at hlp ⊢
    generalize W LG (cosetDecoration LG.garden P.L 0 κ.1) = Wv
    generalize (dagger.elim 1 fun c => LG.sibWeight c (cosetDecoration LG.garden P.L 0 κ.1)) = Sv
    generalize leafProd LG g (cosetDecoration LG.garden P.L 0 κ.1) = Pg at hlp ⊢
    rw [show x * (Wv * Pg * Sv) = Wv * Sv * (x * Pg) by ring, hlp, Finset.mul_sum]
    exact sum_congr rfl fun m _ => by ring
  · intro m hm
    refine summable_kernelGenFactor_dom P.L P.γ P.δ hL LG _ _ _ _ _ hn _ C hC fun k => ?_
    have hsib := sibWeight_abs_le_one (d := P.d) LG
    have hprod : |leafProd LG (TProf.perturb g (polForm σ j i g) (lam * ((m : ℝ) - M))) k| ≤
        ∏ ℓ ∈ inputLeaves LG.garden, (C * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ))) := by
      unfold leafProd
      rw [Finset.abs_prod]
      refine Finset.prod_le_prod₀ (fun ℓ _ => abs_nonneg _) fun ℓ _ => ?_
      rw [typeProfiles_leaf]
      exact Induct.SNormR_pointwise _ C hC (hg m hm _ (hlayer _) _ _) _
    have hS : |dagger.elim 1 fun c => LG.sibWeight c k| ≤ 1 := by
      cases dagger with
      | none => simp
      | some c => exact sibWeight_abs_le_one LG c k
    calc _ = |W LG k| * |leafProd LG (TProf.perturb g (polForm σ j i g) (lam * ((m : ℝ) - M))) k| *
          |dagger.elim 1 fun c => LG.sibWeight c k| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (∏ ℓ ∈ inputLeaves LG.garden, (C * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ)))) * 1 := by
        have hB : 0 ≤ ∏ ℓ ∈ inputLeaves LG.garden, (C * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ))) :=
          Finset.prod_nonneg fun ℓ _ => mul_nonneg hC (Real.rpow_nonneg (jbr_pos_p _).le _)
        exact mul_le_mul (mul_le_mul (hW LG k) hprod (abs_nonneg _) zero_le_one) hS (abs_nonneg _)
          (by positivity)
      _ = _ := by ring

end WaveTurbulence.Flower.Polar
