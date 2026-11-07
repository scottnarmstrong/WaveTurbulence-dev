/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCNew9
public import WaveTurbulence.Foundations.FinalCount.VCAll3
/-! # VINE-COUNT part 32 (session 4): **TARGET excessprop1 (2)** for every single-vine object removed by `Stage2Op.vine`
(an ordinary VC, or the adjoint of a hyper object), with the ladder scales in the canonical `SourceLadderGaps` form. -/
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

/-- **Excessprop1 (2) for a hyper object** whose adjoint VC is a single vine (as `prop94_vine_newcomp`). -/
theorem prop94_hyper_newcomp (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M)
        (R : HyperLikeRealization M K.C.atoms K.C.upper K.C.lower) (_h : K.C.shape = .hyper R),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) →
        (∃ X, (Molecule.eraseBond M R.added).IsVine X K.C.atoms K.C.upper K.C.lower) →
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
  obtain ⟨Cf, C₂, hCf, hC₂, hmain⟩ := hyper_count_main_new hvp hd hγ
  refine ⟨Cf * C₂, C₂, mul_nonneg hCf (hC₂.trans' zero_le_one), hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hcnt⟩ := hmain δ hδ
  refine ⟨L₀, hL₀, fun L hL C₁ η ν hC₁ hη hη1 hν => ?_⟩
  intro V D _ _ _ M K R h hMol hM hvine w Adm Adm' hAdm' P hP0 hP1 hP2 hF hscale hfix
  have hL1 : Real.exp 1 ≤ L := hL₀.trans hL
  have hcount := hcnt L hL ν hν M K R h hMol hM hvine w Adm P hP0 hscale hfix
  obtain ⟨X, hX⟩ := hvine
  have hMol' : (Molecule.eraseBond M R.added).IsMolecule := Vine.eraseBond_isMolecule M hMol _ (added_nonloop K R h)
  obtain ⟨hbc', hm'⟩ := vine_bonds_of_vine hvp hMol' (adjointCut K R h) hX
  have hbc : K.vc.bonds.card = 2 * (K.C.atoms.card - 1) := by
    rw [← adj_bonds_card K R h]; exact hbc'
  have hC1 : 1 ≤ C₁ := hC₂.trans hC₁
  have hh := vine_excess_new K hM L γ δ C₁ C₂ η ν w Adm Adm' hAdm' P hL1 hδ.1 hC1
    (hC₂.trans' zero_le_one) hC₁ (by linarith) hP0 hP1 hP2 hη hη1 hF hbc hm' Cf hCf 4 hcount
  refine isDeviation_mono hh (ENNReal.ofReal_le_ofReal ?_)
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

/-- **TARGET excessprop1 (2), for the single-vine objects removed by `Stage2Op.vine`** (an ordinary VC, or a hyper object
whose adjoint is a single vine), with the molecule-level ladder-gap clause of `Adm` (`SourceLadderGaps`, as `prop94_vine_all`).
`VINEPARAM` is the only vine hypothesis. The premise `NewCompFixed` is the source's fixed-set fact (L2174). There is no
`ι`/`κ` hypothesis: no `α`-atom is created (L2169), so the product over new `α`-atoms is empty. -/
theorem prop94_vine_newcomp_all (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cs C₂ : ℝ, 0 ≤ Cs ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ C₁ η ν : ℝ, C₂ ≤ C₁ → 0 < η → η < 1 → 1 ≤ ν →
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M),
        M.IsMolecule → (∀ a ∈ M.atoms, M.deg a ≤ 4) → SingleVineVC K →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
          (Adm' : (PDart K.cutMol (fun a => a ∉ K.C.atoms) → (Fin d → ℤ)) → Prop),
        (∀ κ, Adm κ → Adm' (fun x => κ x.1)) → ∀ P : Finset V → ℝ, (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (SourceLadderGaps M L w P) →
        (∀ S' ∈ K.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) →
        (∀ S' ∈ K.cutMol.maximalLadders, ∀ S ∈ K.m1.maximalLadders, S' ⊆ S → P S' = P S) →
        K.post.numComponents = M.numComponents + 1 → NewCompFixed M K L γ δ ν w Adm →
        IsDeviation (M.countA L γ δ C₁ w Adm P) ((Stage2Op.vine K).post.countA L γ δ C₁ w Adm' P)
          (ENNReal.ofReal ((Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) *
            (L ^ (min γ (1 - γ)) * excessRHS L γ η [] 1 2))) := by
  obtain ⟨Cs₁, C₂₁, hCs₁, hC₂₁, h₁⟩ := prop94_vine_newcomp_single hvp hd hγ
  obtain ⟨Cs₂, C₂₂, hCs₂, hC₂₂, h₂⟩ := prop94_hyper_newcomp hvp hd hγ
  refine ⟨max Cs₁ Cs₂, max C₂₁ C₂₂, le_max_of_le_left hCs₁, le_max_of_le_left hC₂₁, fun δ hδ => ?_⟩
  obtain ⟨L₁, hL₁, hh₁⟩ := h₁ δ hδ
  obtain ⟨L₂, hL₂, hh₂⟩ := h₂ δ hδ
  refine ⟨max (max L₁ L₂) (Real.exp 1), le_max_right _ _, fun L hL C₁ η ν hC₁ hη hη1 hν => ?_⟩
  intro V D _ _ _ M K hMol hM hs w Adm Adm' hAdm' P hP0 hAdm hP1 hP2 hF hfix
  have hLa : L ≥ L₁ := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLb : L ≥ L₂ := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hCa : C₂₁ ≤ C₁ := (le_max_left _ _).trans hC₁
  have hCb : C₂₂ ≤ C₁ := (le_max_right _ _).trans hC₁
  have hscale : DecScale M L w Adm (VCLadderScale K L w P) :=
    fun c κ' hd hc hk => vcLadderScale_of_sourceAdm K hMol hM L w P hP1 hP2 hd hc (hAdm c κ' hd hc hk)
  have hε : 0 < η ^ 2 - η ^ 3 := by nlinarith [pow_pos hη 2, pow_pos hη 3]
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) ((le_max_right _ _).trans hL)
  have hexc : 0 ≤ L ^ (min γ (1 - γ)) * excessRHS L γ η [] 1 2 := by
    rw [excessRHS_beta L γ η hL0]; positivity
  have hν0 : 0 < ν := by linarith
  have hconst : ∀ Cx : ℝ, Cx ≤ max Cs₁ Cs₂ →
      Cx * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) ≤
        max Cs₁ Cs₂ * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) := by
    intro Cx hCx
    have h0 : 0 ≤ (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) :=
      pow_nonneg (div_nonneg (Nat.cast_nonneg _) hε.le) _
    have hp : 0 ≤ ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8) := by
      have := hδ.1; positivity
    calc Cx * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)
        = Cx * (ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) := by ring
      _ ≤ max Cs₁ Cs₂ * (ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) :=
          mul_le_mul_of_nonneg_right hCx hp
      _ = _ := by ring
  unfold SingleVineVC at hs
  rcases hsh : K.C.shape with hv | R
  · rw [hsh] at hs
    have := hh₁ L hLa C₁ η ν hCa hη hη1 hν M K hMol hM hs w Adm Adm' hAdm' P hP0 hP1 hP2 hF hscale hfix
    exact isDeviation_mono this (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hconst _ (le_max_left _ _)) hexc))
  · rw [hsh] at hs
    have := hh₂ L hLb C₁ η ν hCb hη hη1 hν M K R hsh hMol hM hs w Adm Adm' hAdm' P hP0 hP1 hP2 hF hscale hfix
    exact isDeviation_mono this (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hconst _ (le_max_right _ _)) hexc))

end WaveTurbulence.VineCount
