/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import Mathlib

/-! # PROT-OPS-TERM: splitting `ℝ^(n+m)` as `ℝ^n × ℝ^m` (measure preserving) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtOpsTerm

/-- The leading `n` coordinates. -/
def hd {n m : ℕ} (z : Fin (n + m) → ℝ) : Fin n → ℝ := fun i => z (Fin.castAdd m i)
/-- The trailing `m` coordinates. -/
def tl {n m : ℕ} (z : Fin (n + m) → ℝ) : Fin m → ℝ := fun j => z (Fin.natAdd n j)

theorem append_hd_tl {n m : ℕ} (z : Fin (n + m) → ℝ) : Fin.append (hd z) (tl z) = z :=
  Fin.append_castAdd_natAdd

theorem hd_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) : hd (Fin.append x y) = x := by
  funext i; simp [hd]

theorem tl_append {n m : ℕ} (x : Fin n → ℝ) (y : Fin m → ℝ) : tl (Fin.append x y) = y := by
  funext i; simp [tl]

/-- The splitting as a measurable equivalence. -/
def splitE (n m : ℕ) : (Fin (n + m) → ℝ) ≃ᵐ (Fin n → ℝ) × (Fin m → ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + m) => ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ))

theorem splitE_apply {n m : ℕ} (z : Fin (n + m) → ℝ) : splitE n m z = (hd z, tl z) := by
  refine Prod.ext ?_ ?_
  · funext i
    simp [splitE, hd, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
    exact (Equiv.piCongrLeft_symm_apply (fun _ : Fin (n + m) => ℝ) finSumFinEquiv z (Sum.inl i)).trans (by simp)
  · funext j
    simp [splitE, tl, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
    exact (Equiv.piCongrLeft_symm_apply (fun _ : Fin (n + m) => ℝ) finSumFinEquiv z (Sum.inr j)).trans (by simp)

theorem splitMP (n m : ℕ) :
    MeasurePreserving (splitE n m) volume (volume.prod volume) := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n ⊕ Fin m => ℝ)
  have h2 := (volume_measurePreserving_piCongrLeft (fun _ : Fin (n + m) => ℝ) finSumFinEquiv).symm
  exact h2.trans h1

theorem integral_split {n m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (Fin n → ℝ) × (Fin m → ℝ) → E) :
    ∫ z : Fin (n + m) → ℝ, f (hd z, tl z) = ∫ p, f p ∂(volume.prod volume) := by
  have := (splitMP n m).integral_comp' f
  simpa only [splitE_apply] using this

theorem integrable_split {n m : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : (Fin n → ℝ) × (Fin m → ℝ) → E) :
    Integrable (fun z : Fin (n + m) → ℝ => f (hd z, tl z)) ↔ Integrable f (volume.prod volume) := by
  have := (splitMP n m).integrable_comp_emb (splitE n m).measurableEmbedding (g := f)
  simpa only [Function.comp_def, splitE_apply] using this

theorem lintegral_split {n m : ℕ} (f : (Fin n → ℝ) × (Fin m → ℝ) → ℝ≥0∞) :
    ∫⁻ z : Fin (n + m) → ℝ, f (hd z, tl z) = ∫⁻ p, f p ∂(volume.prod volume) := by
  have := (splitMP n m).lintegral_comp_emb (splitE n m).measurableEmbedding f
  simpa only [Function.comp_def, splitE_apply] using this

end WaveTurbulence.Flower.ProtOpsTerm
