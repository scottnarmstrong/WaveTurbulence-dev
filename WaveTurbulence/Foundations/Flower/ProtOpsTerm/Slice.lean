/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtOpsTerm.Split
public import WaveTurbulence.Foundations.Flower.ProtTa.Recon

/-! # PROT-OPS-TERM: slicing `ℝ^(r+3)` through the middle time, with `r` spectators -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory WaveTurbulence.Fourier WaveTurbulence.Flower.ProtTa
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtOpsTerm

theorem splitE_symm {n m : ℕ} (a : Fin n → ℝ) (w : Fin m → ℝ) :
    (splitE n m).symm (a, w) = Fin.append a w := by
  have h := splitE_apply ((splitE n m).symm (a, w))
  rw [MeasurableEquiv.apply_symm_apply] at h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only at h1 h2
  generalize (splitE n m).symm (a, w) = z at h1 h2 ⊢
  subst h1 h2
  exact (append_hd_tl z).symm

/-- The middle-time insertion `(u, y) ↦ (y₀, u, y₁)`. -/
def mid (p : ℝ × (Fin 2 → ℝ)) : Fin 3 → ℝ := ![p.2 0, p.1, p.2 1]

theorem midMP : MeasurePreserving mid (volume.prod volume) volume := by
  have h1 := (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 1).symm
  convert h1 using 1
  funext p
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply]
  ext j
  fin_cases j <;> simp [mid, Fin.insertNth, Fin.succAboveCases]

/-- The slice map with `r` spectators. -/
def lam (r : ℕ) (p : ℝ × (Fin (r + 2) → ℝ)) : Fin (r + 3) → ℝ :=
  Fin.append (hd p.2) ![tl p.2 0, p.1, tl p.2 1]

theorem lamMP (r : ℕ) : MeasurePreserving (lam r) (volume.prod volume) volume := by
  have hα : MeasurePreserving
      (fun q : ℝ × ((Fin r → ℝ) × (Fin 2 → ℝ)) => (q.2.1, (q.1, q.2.2)))
      (volume.prod (volume.prod volume)) (volume.prod (volume.prod volume)) := by
    have e1 := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure (Fin r → ℝ))
      (volume : Measure (Fin 2 → ℝ))).symm
    have e2 := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Fin r → ℝ)))).prod
      (MeasurePreserving.id (volume : Measure (Fin 2 → ℝ)))
    have e3 := measurePreserving_prodAssoc (volume : Measure (Fin r → ℝ)) (volume : Measure ℝ)
      (volume : Measure (Fin 2 → ℝ))
    have := e3.comp (e2.comp e1)
    convert this using 1
    funext q
    simp [MeasurableEquiv.prodAssoc]
  have hs := (splitMP r 2)
  have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod hs
  have h2 := (MeasurePreserving.id (volume : Measure (Fin r → ℝ))).prod midMP
  have h4 : MeasurePreserving (splitE r 3).symm (volume.prod volume) volume := (splitMP r 3).symm
  have := h4.comp (h2.comp (hα.comp h1))
  convert this using 1
  funext p
  simp only [Function.comp_apply, Prod.map, splitE_apply, mid, lam]
  rw [splitE_symm]
  rfl
