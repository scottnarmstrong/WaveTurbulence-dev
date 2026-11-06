/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SpliceGateMonotone
public import WaveTurbulence.Foundations.Spine.MoleculeCircuitRank
/-! Large-constant monotonicity of `FinalCountAt` (the counting input `finalcount1`, TARGET L2114-L2116).
`countA` decreases in `C_1` because its circuit rank is nonnegative (`circuitRank_nonneg`), so the bound
at one `C_1` implies the bound at every larger `C_1`. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open WaveTurbulence Finset
open scoped ENNReal

theorem countA_mono_C₁ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d : ℕ} (L γ δ c c' : ℝ) (hδ : 0 ≤ δ) (hc : 0 < c) (hcc : c ≤ c')
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) :
    M.countA L γ δ c' w Adm P ≤ M.countA L γ δ c w Adm P := by
  unfold Molecule.countA
  refine mul_le_mul' le_rfl ?_
  have hχ := circuitRank_nonneg M
  have hc' : 0 < c' := lt_of_lt_of_le hc hcc
  have hbase : c'⁻¹ * δ ^ (1 / 2 : ℝ) ≤ c⁻¹ * δ ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right (inv_anti₀ hc hcc) (Real.rpow_nonneg hδ _)
  have hpow : (c'⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank ≤ (c⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank :=
    zpow_le_zpow_left₀ hχ (mul_nonneg (inv_nonneg.mpr hc'.le) (Real.rpow_nonneg hδ _)) hbase
  have hnn : 0 ≤ (c'⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank :=
    zpow_nonneg (mul_nonneg (inv_nonneg.mpr hc'.le) (Real.rpow_nonneg hδ _)) _
  have e1 : ∀ a : ℝ, L ^ (-((d : ℝ) - γ) * M.circuitRank) * a ^ M.circuitRank *
      ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S =
      a ^ M.circuitRank * (L ^ (-((d : ℝ) - γ) * M.circuitRank) *
        ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) :=
    fun a => by ring
  rw [e1, e1]
  exact ofReal_mul_mono_any hnn hpow

theorem finalCountAt_largeConstantMonotone : LargeConstantMonotone FinalCountAt := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirred hbal hn hnmax D C hD hgeom base roots
    Adm hAdm
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirred hbal hn hnmax D C hD hgeom base roots Adm hAdm
  refine le_trans ?_ h0
  exact countA_mono_C₁ G.molecule P.L P.γ P.δ P.C₁ c₁ hδ.le (by linarith) h₁ base Adm C.ladderScale

end WaveTurbulence.LGSpine
