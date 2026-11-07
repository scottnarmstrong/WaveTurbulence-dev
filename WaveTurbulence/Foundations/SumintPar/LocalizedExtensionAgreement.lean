/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.LocalizedExtensionFourier

/-!
# Pointwise localized source agreement after spatial Fourier recombination

The source cutoff centers are chosen once per pair of localization
labels, independently of all external momenta and output times.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace WaveTurbulence.SumintPar

/-- Each actual localized lattice expression has the explicit Fourier-recombined ambient extension. -/
theorem exists_localizedSourceExtension_agreement {d : ℕ} (hd : 1 ≤ d) (D : SumintDatum d)
    (hI : 0 < D.S.I) (N : ℕ) {h : ℝ} (hh : 0 < h) {A L γ δ η : ℝ}
    {Dsteps : ℕ} (hL : 0 < L) (hη : η ≤ 1/3) (hD : D.Admissible A L γ η Dsteps)
    (a b : D.S.VIdx → Fin d → ℤ) :
    ∃ p : D.S.VIdx → Fin d → ℝ, ∀ E : Fin 4 → Mom d,
      (∀ j, ‖E j-D.centre j‖ ≤ 1) → ∀ t : Fin 3 → ℝ,
      (∀ j, t j ∈ Icc (0:ℝ) N) →
      localizedSourceExtension D hI N h L γ δ η a b p E t =
        ((‖E 0-E 1‖^(Finset.univ.filter (fun i => D.S.nor i = false ∧ D.badKind i = 1)).card : ℝ):ℂ)*
          ∑' x : D.S.VIdx → Fin d → ℤ, localizedSourceWeight D L a b E x *
            (∫ τ in D.timeDom hI (t 0) (t 1) (t 2), D.phase L γ δ η x (E 0-E 1) (t 0) τ) := by
  classical
  obtain ⟨p,hp⟩ := exists_inputCutoff_insertion D hD a b
  refine ⟨p,?_⟩
  intro E hE t ht
  have hinsert (x : D.S.VIdx → Fin d → ℤ) : localizedSourceWeight D L a b E x =
      ((∏ v, inputCutoff (p v) (latticePoint L (x v)) : ℝ):ℂ)*localizedSourceWeight D L a b E x := hp E hE x
  have hzero (x : D.S.VIdx → Fin d → ℤ) (hx : x ∉ inputCutoffBox L p) :
      localizedSourceWeight D L a b E x = 0 := by
    rw [hinsert x,inputCutoff_product_eq_zero hL p x hx,Complex.ofReal_zero,zero_mul]
  rw [localizedSourceExtension_eq_sum hd D hI N h hL hη hD a b p E t]
  congr 1
  rw [tsum_eq_sum (s := inputCutoffBox L p) (fun x hx => by rw [hzero x hx,zero_mul])]
  apply Finset.sum_congr rfl
  intro x _
  rw [phaseCellExtension_agreement D hI N hh L γ δ η x (E 0-E 1) t ht,
    ← hinsert x]

end WaveTurbulence.SumintPar
