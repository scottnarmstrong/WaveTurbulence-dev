/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmGReg2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmGReg1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmGReg2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (garden level): the REG bound for one garden** (TARGET finalcount1, L2114–L2116, REG case).

`reg_garden_bound`: for `d ≥ 3`, `1/2 < γ < 1` and `η` small, there is `Cstar ≥ 1` (depending on `d, γ, η` only) such that for all
exponents `m, c`, all `C₁ ≥ 4 Cstar` and `δ ∈ (0, 1]` there is `R₀` with: for `L ≥ R₀`, every REG garden `G` of width `2R`
(`R ≤ (1 + log L)^c`, order `≤ (1 + log L)^m / 2`) with amended geometry, and every admissible set of decorations, satisfies the
`FinalCountAt` bound.  Chain: base shift to `0` (`countA_base_eq_of_molecule`), the renaming `Sum.inl` (`countA_inl_scale`), the
hereditary ladder scale (`countA_le_hered`), `reg_molecule_bound` with `regClassHyps_garden` for every nonempty class, and the
identifications `rho_inl`, `numCriticalSG_eq`. 

**Low-range change (L6-HASM).** `γ ∈ (1/2, 1)` → `γ ∈ (0, 1/2]`, `hsm2 : dη ≤ (2γ−1)/1000` deleted, `[Src.AsmInputs]`
added (Prop 9.6 and Step 1 at γ ≤ 1/2, through `reg_class_bound`).-/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp WaveTurbulence.Mole WaveTurbulence.VineCount

theorem reg_garden_bound {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioc (0 : ℝ) (1 / 2)) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {R : ℕ} (G : Garden (2 * R)), G.IsPlain → 1 ≤ R → (R : ℝ) ≤ (1 + Real.log L) ^ c →
        ((2 * G.order : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m →
      ∀ (D : SplicedKernelData G d) (C : Src.CountingChoices Src.γL G d), Src.CountingGeometry G C → RegGeom G →
      ∀ (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Src.splicedCountingAdmissible G D C L γ η base roots κ) →
        G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
          ENNReal.ofReal (L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
            L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40))) := by
  obtain ⟨Cs, hCs, hreg⟩ := reg_molecule_bound hd hγ hη hsm hηs
  have hγ1 : γ < 1 := by linarith [hγ.2]
  have hηγ : η ≤ γ := by
    have h1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have h2 : min γ (1 - γ) ≤ γ := min_le_left _ _
    nlinarith
  refine ⟨Cs, hCs, fun m c C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR₀, hb⟩ := hreg m c C1 hC1 δ hδ
  obtain ⟨L6, hL6, h6⟩ := polylog_absorb 2 0 (1 - γ) (by linarith)
  have e2 := Real.exp_pos 2
  refine ⟨R₀ + L6 + Real.exp 2, by linarith, fun L hL R G hp hR hRc hord D C hg hregG base roots Adm hA => ?_⟩
  have hLR : R₀ ≤ L := by linarith
  have hL6' : L6 ≤ L := by linarith
  have hLe2 : Real.exp 2 ≤ L := by linarith
  have hLe : Real.exp 1 ≤ L := le_trans (Real.exp_le_exp.2 (by norm_num)) hLe2
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hLe
  have hL0 : 0 < L := by linarith
  have h2 : 2 / L ≤ L ^ (-γ + η) := by
    have h6' := h6 L hL6'
    simp only [pow_zero, mul_one] at h6'
    have h7 : 2 / L ≤ L ^ (-γ) := by
      rw [div_le_iff₀ hL0]
      calc (2 : ℝ) ≤ L ^ (1 - γ) := h6'
        _ = L ^ (-γ) * L := by rw [show 1 - γ = -γ + 1 by ring, Real.rpow_add hL0, Real.rpow_one]
    exact le_trans h7 (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hB : 0 ≤ L ^ (-4 * η ^ 6 * ((G.molecule.rho : ℝ) + (C.numCriticalSG : ℝ))) *
      L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)) := by positivity
  by_cases hne : ∃ κ, Adm κ
  swap
  · push Not at hne
    have h0 := countA_union_le G.molecule L γ δ C1 base (∅ : Finset Bool) (Adm := Adm) (fun _ _ => True)
      (fun κ hκ => absurd hκ (hne κ)) C.ladderScale
    simp only [Finset.sum_empty] at h0
    exact h0.trans bot_le
  obtain ⟨κ0, hκ0⟩ := hne
  have hSG : SubHyp R G.molecule := subHyp_of_geometry hg hR hregG.1 hregG.2
  have hS : SubHyp R (inlMol G.molecule) := subHyp_mapAtoms (inlEmb _) hSG
  have hk : (kFix0 C base).card ≤ 2 * R := Finset.card_image_le.trans hg.fixedRoots_card
  have hmateAll : ∀ κ, Adm κ → ∀ x, κ ((inlMol G.molecule).mate x) = κ x := by
    intro κ hκ x
    obtain ⟨c, hc, -⟩ := gdec hp hL0.ne' (hA κ hκ)
    exact hc.1 x
  have hcard' : ((2 * (inlMol G.molecule).atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m := by
    rw [inlMol_atoms, Finset.card_map, hg.atom_count]; exact hord
  have hP0 : ∀ S ∈ (inlMol G.molecule).maximalLadders, 0 ≤ scaleMap (inlEmb _) C.ladderScale S := by
    intro S hS'
    have hgaps : SourceLadderGaps (inlMol G.molecule) L base (scaleMap (inlEmb _) C.ladderScale) κ0 :=
      (ladderGaps_mapAtoms (inlEmb _) C L γ η base κ0).2 (hA κ0 hκ0).2.2.2.2.2.2.2.2.2
    rcases (hgaps S hS').1 with h | ⟨-, h, -⟩
    · rw [h]
    · exact le_trans (inv_nonneg.2 hL0.le) h
  have hC10 : 0 ≤ C1 := by linarith
  have hmol := hb L hLR (M₀ := inlMol G.molecule) (Rn := R)
    (P := heredScale' (inlMol G.molecule) (scaleMap (inlEmb _) C.ladderScale)) (Adm := Adm) (C := C0 C)
    (Un := Un0 C L γ η) (Fst := Fst0 C) (crit := critMap (inlEmb _) C) (kFix0 C base) hS hk hRc hmateAll
    (fun lab _ hne' => regClassHyps_garden hp hR hg hregG hL0 hA hLe hηγ hη h2 lab hne' m hcard')
  rw [rho_inl, ← numCriticalSG_eq (inlEmb _) C] at hmol
  calc G.molecule.countA L γ δ C1 base Adm C.ladderScale
      = G.molecule.countA L γ δ C1 0 Adm C.ladderScale := countA_base_eq_of_molecule G.molecule hg.molecule L γ δ C1 base 0 Adm _
    _ = (inlMol G.molecule).countA L γ δ C1 0 Adm (scaleMap (inlEmb _) C.ladderScale) :=
        (countA_inl_scale G.molecule L γ δ C1 0 Adm C.ladderScale).symm
    _ ≤ (inlMol G.molecule).countA L γ δ C1 0 Adm (heredScale' (inlMol G.molecule) (scaleMap (inlEmb _) C.ladderScale)) :=
        countA_le_hered _ L γ δ C1 0 Adm hL0 hδ.1.le hC10 hP0
    _ ≤ _ := hmol

end WaveTurbulence.GammaLow.FinalCount.H
