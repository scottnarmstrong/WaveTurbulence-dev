/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Engine1
/-! # Rung sums (S3b LADDER-DECAY)

The one-rung twisted sum with kernel phase `c (t₂ - t₁) ⟨φx, φy⟩` and additive linear phase, and
the representation of additive characters of the rung lattice by pairs of momenta. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset WaveTurbulence WaveTurbulence.WeylSums

variable {d : ℕ}

/-- The bilinear form `⟨φ x, φ y⟩` of a rung point. -/
noncomputable def bil (L : ℝ) (p : Pt d) : ℝ := inner ℝ (latticePoint L p.1) (latticePoint L p.2)

/-- The twisted one-rung sum with weights `w` on the finite set `S`. -/
noncomputable def rungSum (L c : ℝ) (w : Pt d → ℂ) (S : Finset (Pt d)) (lam ν : Pt d →+ ℝ)
    (t : ℝ × ℝ) : ℂ :=
  ∑ p ∈ S, w p * e (c * (t.2 - t.1) * bil L p + (t.2 * lam p + ν p))

/-- Coordinates of an additive functional on one factor. -/
noncomputable def repVec (L : ℝ) (f : (Fin d → ℤ) →+ ℝ) : Mom d :=
  WithLp.toLp 2 (fun j => L * f (Pi.single j 1))

lemma addHom_eq_sum (f : (Fin d → ℤ) →+ ℝ) (x : Fin d → ℤ) :
    f x = ∑ j, (x j : ℝ) * f (Pi.single j 1) := by
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin d → ℤ) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_zsmul]; simp

lemma addHom_eq_inner {L : ℝ} (hL : L ≠ 0) (f : (Fin d → ℤ) →+ ℝ) (x : Fin d → ℤ) :
    f x = inner ℝ (latticePoint L x) (repVec L f) := by
  rw [addHom_eq_sum]
  simp only [latticePoint, repVec, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  field_simp

/-- Left/right restriction of an additive character of the rung lattice. -/
def Pt.left (ν : Pt d →+ ℝ) : (Fin d → ℤ) →+ ℝ := ν.comp (AddMonoidHom.inl _ _)

/-- Right restriction. -/
def Pt.right (ν : Pt d →+ ℝ) : (Fin d → ℤ) →+ ℝ := ν.comp (AddMonoidHom.inr _ _)

lemma addHom_pt_eq {L : ℝ} (hL : L ≠ 0) (ν : Pt d →+ ℝ) (p : Pt d) :
    ν p = inner ℝ (latticePoint L p.1) (repVec L (Pt.left ν)) +
      inner ℝ (latticePoint L p.2) (repVec L (Pt.right ν)) := by
  rw [← addHom_eq_inner hL, ← addHom_eq_inner hL]
  have : p = (p.1, 0) + (0, p.2) := by simp
  conv_lhs => rw [this]
  rw [map_add]
  rfl

end WaveTurbulence.LadderDecay
