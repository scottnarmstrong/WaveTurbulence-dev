/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm15d
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmTerm15c
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3ConclN
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3MapDec5
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmTerm15d`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY, `hterm` part 15d: the bound for a damaged component** (`prop96_damaged`, `Cstar` before `m`). -/
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

section dam
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {Tm : V → Prop}

end dam


theorem dam_comp_bound {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type v} [DecidableEq V] [Infinite V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
        {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {R : ℕ} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ},
        SubHyp R M₀ → RunDataN L γ η M₀ hf (fun k => k ∈ A) →
        (∀ κ ∈ A, DegenSGT M₀ L γ η (0 : Mom d) κ Tm) →
        (∀ κ ∈ A, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0) →
        (∃ κ, κ ∈ A) → (∀ S, 0 ≤ P S) → (hf.s.M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → Good R hf.s →
        ∀ {a : V}, a ∈ (hf.op5 Tm).s.M.atoms → ¬ UntC hf Tm R a →
        WaveTurbulence.FinalCountG8.MaxLadderGapAdm (compMol (hf.op5 Tm).s.M a) L (0 : Mom d) P (MoleProp.GapScale L)
          (compAdm (hf.op5 Tm) a (fun k => k ∈ A)) →
        (compMol (hf.op5 Tm).s.M a).countA L γ δ C1 (0 : Mom d)
          (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P ≤
        ENNReal.ofReal ((∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹) *
          L ^ exa γ η hf Tm R a) := by
  obtain ⟨Cs, hCs, h⟩ := damaged_component_bound'.{v, u} hd hγ hη hsm hηs
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR⟩ := h m C1 hC1 δ hδ
  refine ⟨max R₀ 1, le_max_right _ _, fun L hL V _ _ D₀ _ _ M₀ hf Tm R A P hS hrun hdeg h0 hne hP0 hsz hg a ha hU hML => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hCN : ∀ κ, κ ∈ A → Prop95ConclN L γ η (0 : Mom d) κ Tm R hf := fun κ hκ => by
    obtain ⟨C, Unsel, obl, hT3, -, hrC⟩ := hrun κ hκ
    exact hrC.toHRunN.prop95N hS obl hT3 (hdeg κ hκ) (h0 κ hκ)
  obtain ⟨κ₀, hκ₀⟩ := hne
  obtain ⟨R5, -, hg5⟩ := Op5.good (Tm := Tm) hg
  have hn : NoTripleBond (hf.op5 Tm).s.M := noTriple_eraseSetSt (hCN κ₀ hκ₀).no_triple _
  have himp : ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧ contrib (hf.op5 Tm).s b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hU (by have := perfect_unt hg ha hcon; exact ⟨this.1, fun h => absurd h this.2⟩)
  have hshape := Good.damagedShape hg5 hn ha himp
  have hdec := op5_damagedDec' (L := L) (γ := γ) (η := η) (Tm := Tm) (fun x => hg5.1.noloop x) (fun k => k ∈ A) hCN ⟨κ₀, hκ₀⟩ (a₀ := a)
  have hsz' : ((compMol (hf.op5 Tm).s.M a).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m := by
    refine le_trans ?_ hsz
    exact_mod_cast Finset.card_le_card (fun v hv => (Op5.atoms_sub ((mem_compMol _ _).1 hv).1).1)
  have hb := hR L (le_trans (le_max_left _ _) hL) (compMol (hf.op5 Tm).s.M a) (fun v => toCls ((hf.op5 Tm).s.cls v))
    (compAdm (hf.op5 Tm) a (fun k => k ∈ A)) P hshape hdec hsz' hP0 hML
  refine (countA_mono_adm _ L γ δ C1 (0 : Mom d) (proj_adm5_sub hf Tm a A) P).trans (hb.trans (le_of_eq ?_))
  change ENNReal.ofReal (WaveTurbulence.FinalCountG8.damagedRHS (compMol (hf.op5 Tm).s.M a) (cl8 hf) L γ η) = _
  rw [damagedRHS_eq hf _ hL0 γ η]
  unfold exa
  have h1 : (if UntC hf Tm R a ∧ ¬ CompOdd hf a then eraseA γ η else 0) = 0 := by simp [hU]
  have h2 : (if UntC hf Tm R a then (0:ℝ) else
      η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ)) =
      η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) := by simp [hU]
  rw [h1, h2]
  congr 3
  ring

end WaveTurbulence.GammaLow.FinalCount.H
