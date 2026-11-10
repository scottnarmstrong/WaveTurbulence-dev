/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm15c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Anc
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3ConclN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Dart
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3FinalCopy
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HInv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3HRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Hist
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3MapDec5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Run
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3RunN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3URun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3UStep
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Vine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3VineLG10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Ops
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Prop94Statement
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCAdm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCoords
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCDict
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCFlow
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCInj
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCScale
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
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmProp96Low
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmTerm15c`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, `hterm` part 15c: the bound for an untouched component** (`prop96`, `Cstar` before `m`). 

**Low-range change (L6-HASM, PLAN-L6 §3e "Prop 9.6 → `prop96_low_proved`").** `unt_comp_bound`: `γ ∈ (1/2, 1)` →
`γ ∈ (0, 1/2]`, `hsm2` deleted; main's `final_component_bound` →
`final_component_bound_low` (AsmProp96Low). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe v u

theorem unt_comp_bound {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2))
    {η : ℝ} (hη : 0 < η) (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type v} [DecidableEq V] [Infinite V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
        {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {R : ℕ} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ},
        SubHyp R M₀ → RunDataN L γ η M₀ hf (fun k => k ∈ A) →
        (∀ κ ∈ A, DegenSGT M₀ L γ η (0 : Mom d) κ Tm) →
        (∀ κ ∈ A, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0) →
        (∃ κ, κ ∈ A) → (∀ S, 0 ≤ P S) → (hf.s.M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        ∀ {a : V}, a ∈ (hf.op5 Tm).s.M.atoms → UntC hf Tm R a →
        WaveTurbulence.FinalCountG8.MaxLadderGapAdm (compMol hf.s.M a) L (0 : Mom d) P (MoleProp.GapScale L)
          (compAdm hf a (fun k => k ∈ A)) →
        (compMol (hf.op5 Tm).s.M a).countA L γ δ C1 (0 : Mom d)
          (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P ≤
        ENNReal.ofReal ((∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹) *
          L ^ exa γ η hf Tm R a) := by
  obtain ⟨Cs, hCs, h⟩ := final_component_bound_low.{v, u} hd hγ hη hsm hηs
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR⟩ := h m C1 hC1 δ hδ
  refine ⟨max R₀ 1, le_max_right _ _, fun L hL V _ _ D₀ _ _ M₀ hf Tm R A P hS hrun hdeg h0 hne hP0 hsz a ha hU hML => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hT := hU.1
  have haM : a ∈ hf.s.M.atoms := (Op5.atoms_sub ha).1
  have e1 := comp_count_eq_unt hT ha A L γ δ C1 P
  obtain ⟨κ₀, hκ₀⟩ := hne
  obtain ⟨C, Unsel, obl, hT3, -, hrC⟩ := hrun κ₀ hκ₀
  have hC : Prop95ConclAt L γ η (0 : Mom d) κ₀ R hf Tm :=
    hrC.toHRunN.prop95At hS obl hT3 (hdeg κ₀ hκ₀) (h0 κ₀ hκ₀)
  have hshape := finalShape_comp hC haM hU.2 hT
  have hdec := finalDec_compN hS (fun k => k ∈ A) hrun hdeg h0 ⟨κ₀, hκ₀⟩ hL1 hη.le haM hT
  have hsz' : ((compMol hf.s.M a).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m := by
    refine le_trans ?_ hsz
    exact_mod_cast Finset.card_le_card (fun v hv => ((mem_compMol _ _).1 hv).1)
  obtain ⟨v₂, hv₂⟩ := Infinite.exists_notMem_finset (compMol hf.s.M a).atoms
  have hb := hR L (le_trans (le_max_left _ _) hL) (compMol hf.s.M a) (fun v => toCls (hf.s.cls v)) (CompOdd hf a)
    (compAdm hf a (fun k => k ∈ A)) P hshape hdec hsz' hP0 hML ⟨v₂, hv₂⟩
  have hrhs := finalRHS_eq hf (compMol hf.s.M a) (CompOdd hf a) hL0 γ η
  have hat : (compMol (hf.op5 Tm).s.M a).atoms = (compMol hf.s.M a).atoms := by
    rw [compMol_atoms_eq, compMol_atoms_eq]; exact op5_compAtoms hT ha
  have hρ := dartIso_rho_eq (untouchedIso hT ha)
  refine (le_of_eq e1).trans (hb.trans (le_of_eq ?_))
  change ENNReal.ofReal (WaveTurbulence.FinalCountG8.finalRHS (compMol hf.s.M a) (cl8 hf) (CompOdd hf a) L γ η) = _
  rw [hrhs]
  unfold exa
  rw [hat, hρ]
  have h1 : (if UntC hf Tm R a ∧ ¬ CompOdd hf a then eraseA γ η else 0) = (if ¬ CompOdd hf a then eraseA γ η else 0) := by
    by_cases hc : CompOdd hf a <;> simp [hU, hc]
  have h2 : (if UntC hf Tm R a then (0:ℝ) else
      η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ)) = 0 := by simp [hU]
  rw [h1, h2]
  congr 3
  ring

end WaveTurbulence.GammaLow.FinalCount.H
