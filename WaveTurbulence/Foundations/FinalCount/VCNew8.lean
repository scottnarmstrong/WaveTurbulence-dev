/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew7
/-! # VINE-COUNT part 30 (session 4): **`prop94_vine_newcomp`** -- TARGET excessprop1 (2) (L2167--L2177) for a single vine. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {d : ℕ}

theorem delta_const_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : δ⁻¹ * δ ^ (-(1 : ℝ) / 2) ≤ (1 + δ⁻¹) ^ 2 := by
  have h1 : δ ^ (-(1 : ℝ) / 2) ≤ δ ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.2 hδ0.le
  calc δ⁻¹ * δ ^ (-(1 : ℝ) / 2) ≤ δ⁻¹ * δ⁻¹ := mul_le_mul_of_nonneg_left h1 hi
    _ ≤ (1 + δ⁻¹) ^ 2 := by nlinarith

/-- **TARGET excessprop1 (2), Operation 1 that creates a new connected component, a single vine** (L2154--L2177;
DH23 `(excesseqn2+)`). For `d ≥ 3`, `γ ∈ (0,1)` there are constants `Cs, C₂` (depending on `d, γ`) such that for all
`δ ∈ (0,1]`, `L` large, `C₁ ≥ C₂`, `η ∈ (0,1)` and `ν ≥ 1` (`ν = n_sb`): for every molecule `M` (degrees `≤ 4`) and every vine
removal `K` (Stage-2 operation `vine`) of a single vine with `ΔF = 1` (`K.post` has one more component), under the
ladder-scale clause of `Adm` and the fixed-set fact `NewCompFixed` (L2174), the deviation of the operation is
`≲ L^{γ₀} · L^{-η³} · L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔV_β}` with `ΔF = 1`, `ΔV_β = 2` and no new `α`-atom (the empty product, L2169),
i.e. `L^{γ₀-η³} L^{η²}`: the right-hand side of (excesseqn2+). -/
theorem prop94_vine_newcomp_single (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → (∃ X, M.IsVine X K.C.atoms K.C.upper K.C.lower) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents + 1 →
        DecScale M L w Adm (VCLadderScale K L w P) → NewCompFixed M K L γ δ ν w Adm →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) *
            (L ^ (min γ (1 - γ)) * excessRHS L γ η [] 1 2))) := by
  obtain ⟨Cf, C₂, hCf, hC₂, hmain⟩ := vine_count_main_new hvp hd hγ
  refine ⟨Cf * C₂, C₂, mul_nonneg hCf (hC₂.trans' zero_le_one), hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hcnt⟩ := hmain δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν => ?_⟩
  intro V D _ _ _ M K hMol hM hvine w Adm Adm' hAdm' P hP0 hP1 hP2 hF hscale hfix
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hL
  have hcount := hcnt L hL ν hν M K hMol hM hvine w Adm P hP0 hscale hfix
  obtain ⟨X, hX⟩ := hvine
  obtain ⟨A⟩ := hvp V D M hMol X _ _ _ hX
  have hcard := card_atoms_eq K A
  have hbc : K.vc.bonds.card = 2 * (K.C.atoms.card - 1) := by
    rw [vc_bonds_card K hX.1, A.bond_count]; omega
  have hn1 : 1 ≤ A.indexing.shape.n := by unfold Shape.n; omega
  have h := vine_excess_new K hM L γ δ C₁ C₂ η ν w Adm Adm' hAdm' P hL1 hδ.1 (hC₂.trans' zero_le_one |>.trans' le_rfl |> fun _ => (hC₂.trans hC₁))
    (hC₂.trans' zero_le_one) hC₁ (by linarith) hP0 hP1 hP2 hη hη1 hF hbc (by omega) Cf hCf 4 hcount
  refine isDeviation_mono h (ENNReal.ofReal_le_ofReal ?_)
  have hε : 0 < η ^ 2 - η ^ 3 := by nlinarith [pow_pos hη 2, pow_pos hη 3]
  have hdc := delta_const_le hδ.1 hδ.2
  have hK0 : 0 ≤ (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) := pow_nonneg (div_nonneg (Nat.cast_nonneg _) hε.le) _
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL1
  have hexc : 0 ≤ L ^ (min γ (1 - γ)) * excessRHS L γ η [] 1 2 := by
    rw [excessRHS_beta L γ η hL0]; positivity
  have hCC : 0 ≤ Cf * C₂ * ν := by
    have : 0 < ν := by linarith
    have := hC₂.trans' zero_le_one
    positivity
  refine mul_le_mul_of_nonneg_right ?_ hexc
  calc Cf * ν * δ⁻¹ * C₂ * δ ^ (-(1 : ℝ) / 2) * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)
      = (Cf * C₂ * ν) * (δ⁻¹ * δ ^ (-(1 : ℝ) / 2)) * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) := by ring
    _ ≤ (Cf * C₂ * ν) * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) := by
        gcongr
    _ = _ := by ring

end WaveTurbulence.VineCount
