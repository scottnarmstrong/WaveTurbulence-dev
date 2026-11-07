/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCAll2
/-! # VINE-COUNT part 32: **Prop 9.4, Step 1, for every vine-like object removed by `Stage2Op.vine`** (DH23 L1773--L1801).

The VC removed in Step 1 is, by `Prop subsetvc` (L1797: "`𝕍ℂ` is either a single vine, or is formed by two double bonds"),
a single vine (an ordinary VC, or the adjoint of a hyper object: HV and the triple bonds of `subpro` (c)) or two double
bonds `a = x = b` (`DoubleShape`; a VC, or the adjoint of an HVC).  `prop94_vine_all` proves the deviation bound in each
case, with `VINEPARAM` the only vine hypothesis.  NOT covered, and false as a count: a chain of `m ≥ 2` vines that is not
two double bonds (see `FINDING-CHAIN` in `PROGRESS.md`). -/
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

/-- The removed VC of `K` is a single vine: of `M` for an ordinary VC, of the adjoint `eraseBond M R.added` for a
hyper object (DH23 L1797, first alternative of `Prop subsetvc`). -/
def SingleVineVC {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}
    (K : VineCut M) : Prop :=
  match K.C.shape with
  | .vc _ => ∃ X, M.IsVine X K.C.atoms K.C.upper K.C.lower
  | .hyper R => ∃ X, (Molecule.eraseBond M R.added).IsVine X K.C.atoms K.C.upper K.C.lower

theorem dev_const_single {Cf Cs t δ E : ℝ} (d : ℕ) (hCf0 : 0 ≤ Cf) (hCf : Cf ≤ Cs) (ht : 0 < t) (hδ : 0 < δ)
    (hE : 0 ≤ E) :
    Cf * (2 ^ d * (((4 + 8 + 1 : ℕ) : ℝ) / t) ^ (4 + 8 + 1)) * E ≤
      (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * E := by
  have hA : 0 ≤ (2 : ℝ) ^ d * ((13 : ℝ) / t) ^ 13 := by positivity
  have h13 : (((4 + 8 + 1 : ℕ) : ℝ)) = 13 := by norm_num
  rw [h13]
  have hs : 0 ≤ Cs := hCf0.trans hCf
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  apply mul_le_mul_of_nonneg_right _ hE
  calc Cf * (2 ^ d * (13 / t) ^ (4 + 8 + 1)) ≤ Cs * (2 ^ d * (13 / t) ^ 13) := by
        norm_num; exact mul_le_mul_of_nonneg_right hCf hA
    _ ≤ Cs * (2 ^ d * (13 / t) ^ 13) * (1 + δ⁻¹) := by
        have : 0 ≤ Cs * (2 ^ d * (13 / t) ^ 13) := mul_nonneg hs hA
        nlinarith

theorem dev_const_double {Cd Cs t δ E : ℝ} (d : ℕ) (hCd0 : 0 ≤ Cd) (hCd : Cd ≤ Cs) (ht : 0 < t) (ht2 : t ≤ 2)
    (hδ : 0 < δ) (hE : 0 ≤ E) :
    (Cd * (2 ^ d * (((0 + 8 + 1 : ℕ) : ℝ) / t) ^ (0 + 8 + 1)) * (1 + δ⁻¹)) * E ≤
      (Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) * (1 + δ⁻¹)) * E := by
  have h9 : (((0 + 8 + 1 : ℕ) : ℝ)) = 9 := by norm_num
  rw [h9]
  have hδi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have h13 : (1 : ℝ) ≤ 13 / t := (one_le_div ht).2 (by linarith)
  have hp : ((9 : ℝ) / t) ^ (0 + 8 + 1) ≤ ((13 : ℝ) / t) ^ 13 := by
    calc ((9 : ℝ) / t) ^ (0 + 8 + 1) ≤ ((13 : ℝ) / t) ^ (0 + 8 + 1) :=
          pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right (by norm_num) ht.le) _
      _ ≤ ((13 : ℝ) / t) ^ 13 := pow_le_pow_right₀ h13 (by norm_num)
  apply mul_le_mul_of_nonneg_right _ hE
  apply mul_le_mul_of_nonneg_right _ (by linarith)
  have hs : 0 ≤ Cs := hCd0.trans hCd
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hq : 0 ≤ ((13 : ℝ) / t) ^ 13 := by positivity
  calc Cd * (2 ^ d * ((9 : ℝ) / t) ^ (0 + 8 + 1)) ≤ Cd * (2 ^ d * ((13 : ℝ) / t) ^ 13) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp h2d) hCd0
    _ ≤ Cs * (2 ^ d * ((13 : ℝ) / t) ^ 13) := mul_le_mul_of_nonneg_right hCd (mul_nonneg h2d hq)


/-- **DH23 Prop 9.4, Step 1, for every vine-like object removed by `Stage2Op.vine K`** (L1773--L1801): a single vine
(ordinary VC or the adjoint of a hyper object) or two double bonds (VC or the adjoint of an HVC), with the new
`α`-atoms labelled `Rg ∈ [L⁻¹, L^{-γ+η}]`, `κ ∈ {0, 50}`.  Vine hypothesis: `VINEPARAM` only.  Premises are the
source ones: the classification of `Prop subsetvc` (`hcls`), `ΔF = 0` (`hF`, L1798), the gap `|r| ∼ Rg`
(`hgap`, `hlow`, L1800), `ι` (L1782, L1801), the heredity of `P` along maximal ladders (F-FC-3) and the molecule-level
ladder-gap clause of `Adm` (`SourceLadderGaps` = lg-spine `sourceLadderGapScales`, requirement (ii) of `kqmainest2`, L1692), at decorations (`DecScale`).  (`hlow` is used for the
double bonds only.) -/
theorem prop94_vine_all (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → η ≤ γ →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → (SingleVineVC K ∨ Nonempty (DoubleShape K)) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents →
        ∀ (Rg : ℝ), L⁻¹ ≤ Rg → Rg ≤ L ^ (-γ + η) → ∀ (κ : ℕ) (ρ : ℝ),
        ((κ = 0 ∧ ρ = 2 * Rg) ∨ (κ = 50 ∧ ρ = L ^ (-50 * η) * Rg ∧ L⁻¹ ≤ ρ)) →
        (∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖ ≤ 2 * Rg) →
        (∀ κ', Adm κ' → Rg / 2 ≤ ‖Molecule.gapAt L w κ' K.x₁ K.x₂‖) →
        (κ = 50 → IotaReading M L w Adm K.x₁ K.x₂ (L ^ (-50 * η) * Rg)) →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) *
            excessRHS L γ η [(Rg, κ), (Rg, κ)] 0 0)) := by
  obtain ⟨Cf₁, C₂₁, hCf₁, hC₂₁, h₁⟩ := prop94_vine_final hvp hd hγ
  obtain ⟨Cf₂, C₂₂, hCf₂, hC₂₂, h₂⟩ := prop94_hyper_final hvp hd hγ
  refine ⟨max (max Cf₁ Cf₂) ((9 : ℝ) ^ d * 5 ^ d * (2 * d)), ?_, max C₂₁ C₂₂, le_max_of_le_left hC₂₁, ?_⟩
  · exact le_max_of_le_left (le_max_of_le_left hCf₁)
  intro δ hδ
  obtain ⟨L₁, hL₁, hh₁⟩ := h₁ δ hδ
  obtain ⟨L₂, hL₂, hh₂⟩ := h₂ δ hδ
  refine ⟨max (max L₁ L₂) (Real.exp 1), le_max_right _ _, ?_⟩
  intro L hL C₁ η hC₁ hη hη1 hηγ V D _ _ _ M K hMol hM hcls w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF Rg hRl hRu κ ρ
    hρ hgap hlow hι
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1' : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hL0 : 0 < L := by linarith
  have hLa : L ≥ L₁ := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLb : L ≥ L₂ := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hCa : C₂₁ ≤ C₁ := (le_max_left _ _).trans hC₁
  have hCb : C₂₂ ≤ C₁ := (le_max_right _ _).trans hC₁
  obtain ⟨hR0, hρ0, hρ2, hρL⟩ := rho_facts hL1' hRl hRu hη hηγ hρ
  have ht : 0 < 2 * η - η ^ 3 := by nlinarith [sq_nonneg η, mul_pos hη hη]
  have ht2 : 2 * η - η ^ 3 ≤ 2 := by nlinarith [sq_nonneg η, pow_pos hη 3]
  have hE : 0 ≤ excessRHS L γ η [(Rg, κ), (Rg, κ)] 0 0 := by
    rw [excessRHS_alpha]; positivity
  set Cs := max (max Cf₁ Cf₂) ((9 : ℝ) ^ d * 5 ^ d * (2 * d)) with hCs
  rcases hcls with hs | hS
  · -- a single vine
    unfold SingleVineVC at hs
    rcases hsh : K.C.shape with hv | R
    · rw [hsh] at hs
      have hscale : DecScale M L w Adm (VCLadderScale K L w P) :=
        fun c κ' hd hc hk => vcLadderScale_of_sourceAdm K hMol hM L w P hP1 hP2 hd hc (hAdm c κ' hd hc hk)
      have := hh₁ L hLa C₁ η hCa hη hη1 hηγ M K hMol hM hs w Adm Adm' hAdm' P hP0 hP1 hP2 hF Rg hRl hRu κ ρ hρ hgap
        hι hscale
      refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
      exact dev_const_single d hCf₁ (le_max_of_le_left (le_max_left _ _)) ht hδ.1 hE
    · rw [hsh] at hs
      have := hh₂ L hLb C₁ η hCb hη hη1 hηγ M K R hsh hMol hM hs w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF Rg hRl hRu κ
        ρ hρ hgap hι
      refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
      exact dev_const_single d hCf₂ (le_max_of_le_left (le_max_right _ _)) ht hδ.1 hE
  · -- two double bonds
    obtain ⟨S⟩ := hS
    have hC1 : 1 ≤ C₁ := hC₂₁.trans hCa
    have := prop94_vine_double_full K S hd hM L γ δ C₁ η w Adm Adm' hAdm' P hLe hδ.1 hδ.2 hC1 hP0 hP1 hP2 hη hη1 hηγ
      hγ.2 hF (double_bonds_card S) (double_noLadder S) Rg hRl hRu κ ρ hρ hgap hlow hι
    refine isDeviation_mono this (ENNReal.ofReal_le_ofReal ?_)
    exact dev_const_double d (by positivity) (le_max_right _ _) ht ht2 hδ.1 hE

end WaveTurbulence.VineCount
