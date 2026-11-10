/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3NewComp1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAll3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCExcess
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCHyper4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew12
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew13
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew6
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew8
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCNew9
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCSource
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCStmt
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineCover2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDev
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineDouble7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineExcess5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineRank2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Step5b
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.G3NewComp1`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-G3 (step 5b, part 1): the flux identity through a bridge and `NewCompFixedUp`** (TARGET L2174).

`atoms_flux`: for an atom set `A` and an antisymmetric dart function `g` (`g (mate x) = - g x`), the sum of `g` over all darts at atoms of `A`
equals the sum over the boundary darts (atom in `A`, mate atom outside `A`).  If the boundary of `A` is exactly the two darts `x₁, x₂` of a
vine cut (the new component hanging at the upper joint), the decoration identity gives `k_{x₂} - k_{x₁} = Σ_A c_v` and the energy window gives
`| |k_{x₂}|² - |k_{x₁}|² - Σ_A β_v | ≤ |A| δ⁻¹ L^{-2γ}`: `NewCompFixedUp M K L γ δ |A| w Adm` (VINE-COUNT's form), with `n₀ ≠ 0` from the gap. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

variable {M : Molecule V D}

/-- If the boundary of `A` is `{x₁, x₂}` (a new component hanging at the upper joint), `Step1.NewCompFixedUp` with `ν = |A|`. -/
theorem newCompFixedUp_of_boundary (hd : 0 < d) (K : Step1.VineCut Src.γL M) {L γ δ : ℝ} (hL : L ≠ 0) {w : Mom d}
    {Adm : (D → (Fin d → ℤ)) → Prop} (A : Finset V) (hA : A ⊆ M.atoms)
    (hbd : ∀ x, M.atom x ∈ A → M.atom (M.mate x) ∉ A → x = K.x₁ ∨ x = K.x₂)
    (h1 : M.atom K.x₁ ∈ A ∧ M.atom (M.mate K.x₁) ∉ A) (h2 : M.atom K.x₂ ∈ A ∧ M.atom (M.mate K.x₂) ∉ A)
    (hgap : ∀ κ, Adm κ → κ K.x₁ ≠ κ K.x₂) :
    Step1.NewCompFixedUp M K L γ δ (A.card : ℝ) w Adm := by
  intro c β k0 _
  have hbdry : Finset.univ.filter (fun x => M.atom x ∈ A ∧ M.atom (M.mate x) ∉ A) = {K.x₁, K.x₂} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h; exact hbd x h.1 h.2
    · rintro (rfl | rfl)
      · exact h1
      · exact h2
  have hx12 : K.x₁ ≠ K.x₂ := K.x₁_ne_x₂
  have hflux : ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      Molecule.kvec L w κ K.x₂ - Molecule.kvec L w κ K.x₁ = ∑ v ∈ A, c v := by
    intro κ hκ
    have hdec := hκ.1
    have hg : ∀ x, (fun x => M.dartSign x • Molecule.kvec L w κ x) (M.mate x) =
        - (fun x => M.dartSign x • Molecule.kvec L w κ x) x := by
      intro x
      simp only [Molecule.kvec, hdec.1 x, FinalCountG3.dartSign_mate, neg_smul]
    have := atoms_flux M A (fun x => M.dartSign x • Molecule.kvec L w κ x) hg
    rw [hbdry, Finset.sum_pair hx12] at this
    have e1 : ∑ v ∈ A, ∑ x ∈ M.dartsAt v, M.dartSign x • Molecule.kvec L w κ x = ∑ v ∈ A, c v :=
      Finset.sum_congr rfl fun v hv => hdec.2 v (hA hv)
    rw [e1] at this
    rw [this]
    simp only [Molecule.dartSign, K.Mout₁, K.Mout₂]
    simp; abel
  have henergy : ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      ‖Molecule.kvec L w κ K.x₂‖ ^ 2 - ‖Molecule.kvec L w κ K.x₁‖ ^ 2 = ∑ v ∈ A, M.Gamma L w κ v := by
    intro κ hκ
    have hdec := hκ.1
    have hg : ∀ x, (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) (M.mate x) =
        - (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) x := by
      intro x
      simp only [Molecule.kvec, hdec.1 x, FinalCountG3.dartSign_mate]; ring
    have := atoms_flux M A (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) hg
    rw [hbdry, Finset.sum_pair hx12] at this
    unfold Molecule.Gamma
    rw [this]
    simp only [Molecule.dartSign, K.Mout₁, K.Mout₂]
    simp; ring
  have hlat : ∀ κ ∈ decSet M L γ δ w Adm c β k0,
      latticePoint L (κ K.x₁ - κ K.x₂) = - ∑ v ∈ A, c v := by
    intro κ hκ
    have := hflux κ hκ
    rw [FinalCount.latticePoint_sub]
    simp only [Molecule.kvec] at this
    rw [← neg_sub, ← this]
    abel
  by_cases hex : ∃ κ₀, κ₀ ∈ decSet M L γ δ w Adm c β k0
  · obtain ⟨κ₀, hκ₀⟩ := hex
    refine ⟨κ₀ K.x₁ - κ₀ K.x₂, sub_ne_zero.2 (hgap κ₀ hκ₀.2.2), ∑ v ∈ A, β v, fun κ hκ => ⟨?_, ?_⟩⟩
    · exact latticePoint_injective L hL ((hlat κ hκ).trans (hlat κ₀ hκ₀).symm)
    · rw [henergy κ hκ, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ v ∈ A, |M.Gamma L w κ v - β v| ≤ ∑ _v ∈ A, δ⁻¹ * L ^ (-2 * γ) :=
            Finset.sum_le_sum fun v hv => hκ.2.1.1 v (hA hv)
        _ = (A.card : ℝ) * δ⁻¹ * L ^ (-2 * γ) := by
            rw [Finset.sum_const, nsmul_eq_mul]; ring
  · push Not at hex
    refine ⟨fun _ => 1, ?_, 0, fun κ hκ => absurd hκ (hex κ)⟩
    intro h
    have := congrFun h ⟨0, hd⟩
    simp at this

end WaveTurbulence.GammaLow.FinalCount.H
