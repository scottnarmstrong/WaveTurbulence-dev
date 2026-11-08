/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.RunData
public import WaveTurbulence.Foundations.FinalCount.LowChain40

/-! # C1b2 MK-CHAIN (9): the component wrappers with survivors (`unt_comp_boundLE`, `dam_comp_boundLE`)

Copy-thread of main's LowChain40 (`unt_comp_boundL`, `dam_comp_boundL`) with the run data `RunDataLE` (RunData): the run
facts come from C1a's `HRunLE.inv`/`HRunLE.prop95L`, the final decorations from `finalDec_compLE`. Main's generic
`op5_damagedDecL`, `Op5.epsLGL`, `Op5.labelL` and the component theorems are imported. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep

universe v u

theorem unt_comp_boundLE {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type v} [DecidableEq V] [Infinite V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
        {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {Rn r : ℕ} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ},
        SubHypL Rn M₀ → RunDataLE L γ η M₀ hf (fun k => k ∈ A) →
        (∀ κ ∈ A, DegenSGT M₀ L γ η (0 : Mom d) κ Tm) →
        (∀ κ ∈ A, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0) →
        (∃ κ, κ ∈ A) → (∀ S, 0 ≤ P S) → (hf.s.M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        ∀ {a : V}, a ∈ (hf.op5 Tm).s.M.atoms → UntCL hf Tm r a →
        (((compMol hf.s.M a).atoms.filter fun b => ¬ Even ((compMol hf.s.M a).deg b)).card ≤ 2) →
        WaveTurbulence.FinalCountG8.MaxLadderGapAdm (compMol hf.s.M a) L (0 : Mom d) P (MoleProp.GapScale L)
          (compAdm hf a (fun k => k ∈ A)) →
        (compMol (hf.op5 Tm).s.M a).countA L γ δ C1 (0 : Mom d)
          (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P ≤
        ENNReal.ofReal ((∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹) *
          L ^ exaL γ η hf Tm r a) := by
  obtain ⟨Cs, hCs, h⟩ := final_component_bound.{v, u} hd hγ hη hsm hsm2 hηs
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR⟩ := h m C1 hC1 δ hδ
  refine ⟨max R₀ 1, le_max_right _ _, fun L hL V _ _ D₀ _ _ M₀ hf Tm Rn r A P hS hrun hdeg h0 hne hP0 hsz a ha hU hodd hML => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hT := hU.1
  have haM : a ∈ hf.s.M.atoms := (Op5.atoms_sub ha).1
  have e1 := comp_count_eq_unt hT ha A L γ δ C1 P
  obtain ⟨κ₀, hκ₀⟩ := hne
  obtain ⟨C, m', E, Unsel, obl, hT3, -, -, hrC⟩ := hrun κ₀ hκ₀
  obtain ⟨R', -, hI⟩ := FinalMKStep.HRunLE.inv hrC.toHRunLE (InvL.init hS (h0 κ₀ hκ₀))
  have hC : Prop95ConclAtL L γ η (0 : Mom d) κ₀ Rn hf Tm :=
    (FinalMKStep.HRunLE.prop95L hrC.toHRunLE hS (SubproOblGMK.hingeSGP obl) hT3 (hdeg κ₀ hκ₀) (h0 κ₀ hκ₀)).toAtL
      (fun a ha => hI.good.2 a ha)
  have hshape := finalShape_compL' hC haM (hodd) hT hU.2.1
  have hdec := finalDec_compLE hS (fun k => k ∈ A) hrun hdeg h0 ⟨κ₀, hκ₀⟩ hL1 hη.le haM hT hU.2.1
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
  unfold exaL
  rw [hat, hρ]
  have h1 : (if UntCL hf Tm r a ∧ ¬ CompOdd hf a then eraseA γ η else 0) = (if ¬ CompOdd hf a then eraseA γ η else 0) := by
    by_cases hc : CompOdd hf a <;> simp [hU, hc]
  have h2 : (if UntCL hf Tm r a then (0:ℝ) else
      η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ)) = 0 := by simp [hU]
  rw [h1, h2]
  congr 3
  ring

theorem dam_comp_boundLE {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type v} [DecidableEq V] [Infinite V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
        {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {Rn R' r : ℕ} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ},
        SubHypL Rn M₀ → RunDataLE L γ η M₀ hf (fun k => k ∈ A) →
        (∀ κ ∈ A, DegenSGT M₀ L γ η (0 : Mom d) κ Tm) →
        (∀ κ ∈ A, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0) →
        (∃ κ, κ ∈ A) → (∀ S, 0 ≤ P S) → (hf.s.M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m → Good R' hf.s →
        ∀ {a : V}, a ∈ (hf.op5 Tm).s.M.atoms → ¬ UntCL hf Tm r a →
        WaveTurbulence.FinalCountG8.MaxLadderGapAdm (compMol (hf.op5 Tm).s.M a) L (0 : Mom d) P (MoleProp.GapScale L)
          (compAdm (hf.op5 Tm) a (fun k => k ∈ A)) →
        (compMol (hf.op5 Tm).s.M a).countA L γ δ C1 (0 : Mom d)
          (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P ≤
        ENNReal.ofReal ((∏ v ∈ (compMol (hf.op5 Tm).s.M a).atoms, (apFactor L γ η (hf.s.cls v))⁻¹) *
          L ^ exaL γ η hf Tm r a) := by
  obtain ⟨Cs, hCs, h⟩ := damaged_component_bound'.{v, u} hd hγ hη hsm hηs
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR⟩ := h m C1 hC1 δ hδ
  refine ⟨max R₀ 1, le_max_right _ _, fun L hL V _ _ D₀ _ _ M₀ hf Tm Rn R' r A P hS hrun hdeg h0 hne hP0 hsz hg a ha hU hML => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hL0 : 0 < L := by linarith
  have hCN : ∀ κ, κ ∈ A → Prop95ConclL L γ η (0 : Mom d) κ Tm Rn hf := fun κ hκ => by
    obtain ⟨C, m', E, Unsel, obl, hT3, -, -, hrC⟩ := hrun κ hκ
    exact FinalMKStep.HRunLE.prop95L hrC.toHRunLE hS (SubproOblGMK.hingeSGP obl) hT3 (hdeg κ hκ) (h0 κ hκ)
  obtain ⟨κ₀, hκ₀⟩ := hne
  obtain ⟨R5, -, hg5⟩ := Op5.good (Tm := Tm) hg
  have hn : NoTripleBond (hf.op5 Tm).s.M := noTriple_eraseSetSt (hCN κ₀ hκ₀).no_triple _
  have himp : ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧ contrib (hf.op5 Tm).s b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hU (by have := perfect_untL hg ha hcon; exact ⟨this.1, this.2.1, fun h => absurd h this.2.2⟩)
  have hshape := Good.damagedShape hg5 hn ha himp
  have hdec := op5_damagedDecL (L := L) (γ := γ) (η := η) (Tm := Tm) (fun x => hg5.1.noloop x) (fun k => k ∈ A) hCN ⟨κ₀, hκ₀⟩ (a₀ := a)
  have hsz' : ((compMol (hf.op5 Tm).s.M a).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m := by
    refine le_trans ?_ hsz
    exact_mod_cast Finset.card_le_card (fun v hv => (Op5.atoms_sub ((mem_compMol _ _).1 hv).1).1)
  have hb := hR L (le_trans (le_max_left _ _) hL) (compMol (hf.op5 Tm).s.M a) (fun v => toCls ((hf.op5 Tm).s.cls v))
    (compAdm (hf.op5 Tm) a (fun k => k ∈ A)) P hshape hdec hsz' hP0 hML
  refine (countA_mono_adm _ L γ δ C1 (0 : Mom d) (proj_adm5_sub hf Tm a A) P).trans (hb.trans (le_of_eq ?_))
  change ENNReal.ofReal (WaveTurbulence.FinalCountG8.damagedRHS (compMol (hf.op5 Tm).s.M a) (cl8 hf) L γ η) = _
  rw [damagedRHS_eq hf _ hL0 γ η]
  unfold exaL
  have h1 : (if UntCL hf Tm r a ∧ ¬ CompOdd hf a then eraseA γ η else 0) = 0 := by simp [hU]
  have h2 : (if UntCL hf Tm r a then (0:ℝ) else
      η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ)) =
      η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ) := by simp [hU]
  rw [h1, h2]
  congr 3
  ring


end WaveTurbulence.Flower.FinalMKChain
