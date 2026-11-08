/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.Account

/-! # D6a PROT-PTW: structural facts for the protected tree

The terminal (lone-parent) branch, the designations of `ProtCfg.term`/`none`, the selected link weight and its
antiderivative bound, and the normal links' masses (D5a). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links
open WaveTurbulence.Flower.FiltSrc WaveTurbulence.Flower.FiltProd WaveTurbulence.Flower.FiltGate

variable {d : ℕ} {LG : LayeredGarden 1} {X : RegChain}

/-- The terminal chain node of a nonempty paired tree is a branch. -/
theorem exists_termBranch (hX : X.DecodesTree LG.garden) (hne : X.lonePath ≠ []) :
    ∃ bT : GBranch LG.garden.tree, bT.1.2 = X.lonePath.dropLast := by
  have hnil : X ≠ .nil := by rintro rfl; exact hne rfl
  let C := actualTreeSelection hX hnil
  refine ⟨C.parentBranch, ?_⟩
  obtain ⟨i, hi⟩ := C.last_parent
  have h2 := congrArg Prod.snd hi
  simp only [addrExt] at h2
  change X.lonePath = (C.parentBranch).1.2 ++ [i] at h2
  rw [h2, List.dropLast_concat]

theorem fix_none_eq (s t₀ : ℝ) (b : GBranch LG.garden.tree) : ProtCfg.none.fix X s s t₀ b = none := by
  simp [ProtCfg.fix, ProtCfg.pins]

theorem fix_term_eq (s t₀ : ℝ) (bT : GBranch LG.garden.tree) (hT : bT.1.2 = X.lonePath.dropLast)
    (b : GBranch LG.garden.tree) : ProtCfg.term.fix X s s t₀ b = if b = bT then some s else none := by
  have hiff : b = bT ↔ b.1.2 = X.lonePath.dropLast := by
    rw [← hT]
    constructor
    · rintro rfl; rfl
    · intro h; exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)
  simp only [ProtCfg.fix, ProtCfg.pins, Fin.val_eq_zero, ite_true]
  by_cases h : b = bT
  · rw [ite_eq_left h, List.lookup_cons, beq_iff_eq.mpr (hiff.1 h)]
  · rw [ite_eq_right h, List.lookup_cons, (beq_eq_false_iff_ne).mpr (fun h' => h (hiff.2 h'))]
    rfl

/-- The antiderivative weight of a selected link is `≤ 2K/(π δ L^{2γ} M₂)` on that link and `≤ K` elsewhere. -/
theorem norm_selWeight_le {L : ℝ} (hL : 0 < L) (γ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (Q : Fin (X.treeLinks (LG.garden.sig 0)).length → LayerLink d)
    (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) {K : ℝ} (hψ : ∀ i q, ‖ψ i q‖ ≤ K)
    {M₂ : ℝ} (hM₂ : 0 < M₂) (hz : ∀ q, |linkBilinear L q| < M₂ / 4 → ψ j q = 0)
    (i : Fin (X.treeLinks (LG.garden.sig 0)).length) (q : LPair d) :
    ‖selWeight (X := X) (LG := LG) L γ δ Q j ev ψ i q‖ ≤
      if i = j then 2 * K / (Real.pi * δ * L ^ (2 * γ) * M₂) else K := by
  unfold selWeight
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, ite_eq_left rfl]
    by_cases hq : |linkBilinear L q| < M₂ / 4
    · rw [hz q hq, zero_div, norm_zero]
      have hK : 0 ≤ K := (norm_nonneg _).trans (hψ i q)
      positivity
    · push Not at hq
      have hL2 : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL _
      have hsel : δ * L ^ (2 * γ) * (M₂ / 4) ≤ |selFreq (X := X) (LG := LG) L γ δ Q i ev q| := by
        have h1 : |((if ev = 0 then 1 else -1 : ℝ))| = 1 := by split_ifs <;> simp
        have h2 : |((((Q i).orientation : ℤ) : ℝ))| = 1 := by
          rcases Int.units_eq_one_or (Q i).orientation with h | h <;> simp [h]
        have he : |selFreq (X := X) (LG := LG) L γ δ Q i ev q| = δ * L ^ (2 * γ) * |linkBilinear L q| := by
          unfold selFreq
          simp only [abs_mul, h1, h2, abs_of_pos hδ, abs_of_pos hL2, one_mul]
        rw [he]
        exact mul_le_mul_of_nonneg_left hq (by positivity)
      have hn : ‖(2 * Real.pi * Complex.I * (selFreq (X := X) (LG := LG) L γ δ Q i ev q : ℂ))‖ =
          2 * Real.pi * |selFreq (X := X) (LG := LG) L γ δ Q i ev q| := by
        simp [abs_of_pos Real.pi_pos]
      rw [norm_div, hn]
      have hK : 0 ≤ K := (norm_nonneg _).trans (hψ i q)
      have hpos : 0 < δ * L ^ (2 * γ) * (M₂ / 4) := by positivity
      have hspos := hpos.trans_le hsel
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      calc ‖ψ i q‖ * (Real.pi * δ * L ^ (2 * γ) * M₂) ≤ K * (Real.pi * δ * L ^ (2 * γ) * M₂) :=
            mul_le_mul_of_nonneg_right (hψ i q) (by positivity)
        _ = 2 * K * (2 * Real.pi * (δ * L ^ (2 * γ) * (M₂ / 4))) := by ring
        _ ≤ 2 * K * (2 * Real.pi * |selFreq (X := X) (LG := LG) L γ δ Q i ev q|) := by gcongr
  · rw [Function.update_of_ne hij, ite_eq_right_iff.mpr (fun h => absurd h hij)]
    exact hψ i q

theorem lintegral_filtLink_eq {L : ℝ} (γ δ : ℝ) (A : LayerLink d) (φ : ℝ → ℂ) :
    ∫⁻ s in linkBox A, ‖genLinkTimeFactor L γ δ A (fun q => φ (linkBilinear L q)) s‖ₑ =
      filtLayerLinkMass L (δ * L ^ (2 * γ)) A φ := by
  unfold filtLayerLinkMass
  apply setLIntegral_congr_fun measurableSet_Icc
  intro s _
  dsimp only
  rw [genLinkTimeFactor_bilinear]
  unfold filtLinkTimeFactor
  rw [mul_assoc (((A.orientation : ℤ) : ℝ)) δ]

end WaveTurbulence.Flower.ProtPtw
