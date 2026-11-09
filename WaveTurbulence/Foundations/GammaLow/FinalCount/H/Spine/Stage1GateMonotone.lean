/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Stage1GateMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SpliceGateMonotone
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.Stage1Gate
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.Stage1GateMonotone`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 Large-constant monotonicity of the Stage 1 reduction gate (needed to combine it with the other spine
inputs through `prefix_and`): enlarging `C_1`, `C_2` only weakens the mass bound of `Represents` and the
class count, and leaves the carrier and `Sound` unchanged. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open MeasureTheory Set Finset
open scoped Classical

theorem RepresentsInt_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (π : Stage1Piece P R) (n : ℕ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : 0 ≤ s)
    (val : ℂ) (h : π.RepresentsInt n tt base roots s val) :
    Stage1Piece.RepresentsInt (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π n tt base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, ?_, hD⟩
  refine hwb.trans ?_
  have hsq : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hLp : 0 ≤ P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) := Real.rpow_nonneg hL _
  have hpow : (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) :=
    pow_le_pow_left₀ (mul_nonneg h0 hsq) (mul_le_mul_of_nonneg_right hc hsq) _
  have hpow2 : P.C₁ ^ (π.Gsb.order + 2 * R) ≤ c₁ ^ (π.Gsb.order + 2 * R) := pow_le_pow_left₀ h0 hc _
  have hA : 0 ≤ (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) := pow_nonneg (mul_nonneg h0 hsq) _
  have hB : 0 ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) := pow_nonneg (mul_nonneg (h0.trans hc) hsq) _
  have hC : 0 ≤ P.C₁ ^ (π.Gsb.order + 2 * R) := pow_nonneg h0 _
  have hC' : 0 ≤ c₁ ^ (π.Gsb.order + 2 * R) := pow_nonneg (h0.trans hc) _
  have hAC := mul_le_mul hpow hpow2 hC hB
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hLp) hs

theorem Represents_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (π : Stage1Piece P R) (n : ℕ) (tt : Fin (2 * R) → ℝ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (members : Finset (LayeredGarden (2 * R)))
    (sel : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (F : LeafFamily P (2 * R)) (s : ℝ) (hs : 0 ≤ s)
    (val : ℂ) (h : π.Represents n tt base roots members sel F s val) :
    Stage1Piece.Represents (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π n tt base roots members sel F s
      val :=
  ⟨h.1, RepresentsInt_largeConstants c₁ c₂ hc h0 hδ hL π n tt base roots s hs val h.2⟩

theorem Sound_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (π : Stage1Piece P R) (p : ℕ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : π.Sound p base roots) :
    Stage1Piece.Sound (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π p base roots :=
  { plain := h.plain, irreducible := h.irreducible, balanced := h.balanced, order_pos := h.order_pos,
    order_le := by rw [N_largeConstants]; exact h.order_le, layer_le := h.layer_le,
    molecule := h.molecule, connected := h.connected, atom_count := h.atom_count,
    bond_count := h.bond_count, structural := h.structural, support := h.support,
    hingeOutsideFirst := h.hingeOutsideFirst,
    tripleDesignated := h.tripleDesignated,
    hingeNoLoop := h.hingeNoLoop }

theorem stage1ReductionAtOld_largeConstantMonotone (C₀ : ℕ) : LargeConstantMonotone (Stage1ReductionAtOld C₀) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hN A hA tt htt base roots F s hs0 hctrl hsize
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hN
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcounts⟩ := h p hp R hR hRmax N hN1 hN A
    (fun LG hLG => stage1Carries_largeConstants c₁ c₂ LG (hA LG hLG)) tt htt base roots F s hs0 hctrl hsize
  refine ⟨⟨S.Pc, S.fin, S.piece, S.val⟩, Cl, hCl, cls, members, sel, hpart, ?_, ?_, hord, ?_⟩
  · intro π
    exact Represents_largeConstants c₁ c₂ h₁ (by linarith) hδ.le (by linarith) (S.piece π) N tt base roots
      (members (cls π)) (sel π) F s hs0.le (S.val π) (hrep π)
  · intro π
    exact Sound_largeConstants c₁ c₂ (S.piece π) p base roots (hsound π)
  · obtain ⟨hr, hg, hcnt⟩ := hcounts
    refine ⟨hr, hg, ?_⟩
    intro g r
    refine (hcnt g r).trans ?_
    have hC₂0 : 0 ≤ P.C₂ := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC₂0 h₂ _) (by positivity)

theorem stage1ReductionAt_largeConstantMonotone (C₀ : ℕ) : LargeConstantMonotone (Stage1ReductionAt C₀) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots U s hs0 hb hsize
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hN
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcounts⟩ := h p hp R hR hRmax N hN1 hN A
    (fun LG hLG => stage1Carries_largeConstants c₁ c₂ LG (hA LG hLG)) hcl tt htt base roots U s hs0 hb hsize
  refine ⟨⟨S.Pc, S.fin, S.piece, S.val⟩, Cl, hCl, cls, members, sel, hpart, ?_, ?_, hord, ?_⟩
  · intro π
    exact Represents_largeConstants c₁ c₂ h₁ (by linarith) hδ.le (by linarith) (S.piece π) N tt base roots
      (members (cls π)) (sel π) U.toLF s hs0.le (S.val π) (hrep π)
  · intro π
    exact Sound_largeConstants c₁ c₂ (S.piece π) p base roots (hsound π)
  · obtain ⟨hr, hg, hcnt⟩ := hcounts
    refine ⟨hr, hg, ?_⟩
    intro g r
    refine (hcnt g r).trans ?_
    have hC₂0 : 0 ≤ P.C₂ := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC₂0 h₂ _) (by positivity)

end WaveTurbulence.GammaLow.FinalCount.H
