/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm15c
public import WaveTurbulence.Foundations.FinalCount.G3Damaged
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 15d: the bound for a damaged component** (`prop96_damaged`, `Cstar` before `m`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3


universe v u

/-- The inclusion of the `adm5`-projected class into the class of restrictions of the run. -/
theorem proj_adm5_sub {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
    (hf : HSt V D₀) (Tm : V → Prop) (a : V) (A : Set (D₀ → (Fin d → ℤ))) (κ' : PDart (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) → (Fin d → ℤ))
    (h : projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm)) κ') :
    compAdm (hf.op5 Tm) a (fun k => k ∈ A) κ' := by
  obtain ⟨κ5, ⟨κ'', ⟨κs, ⟨k0, hk0, rfl⟩, hκ''⟩, rfl⟩, rfl⟩ := h
  refine ⟨k0, hk0, funext fun x => ?_⟩
  exact hκ'' _


section dam
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {Tm : V → Prop}

/-- Copy of `Op5.damagedDec` with the no-loop property as a hypothesis (the `R` of `Good` there is unrelated to that of `Prop95ConclN`). -/
theorem op5_damagedDec' {h : HSt V D₀} {R : ℕ} (hnl : ∀ x : (h.op5 Tm).s.D, (h.op5 Tm).s.M.atom x ≠ (h.op5 Tm).s.M.atom ((h.op5 Tm).s.M.mate x))
    (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hC : ∀ κ, AdmRun κ → Prop95ConclN L γ η (0 : Mom d) κ Tm R h) (hne : ∃ κ, AdmRun κ) {a₀ : V} :
    G8Copy.DamagedDec (compMol (h.op5 Tm).s.M a₀) (fun a => toCls ((h.op5 Tm).s.cls a)) L γ η
      (compAdm (h.op5 Tm) a₀ AdmRun) where
  labRange := by
    intro a ha hα
    obtain ⟨κ₀, h₀⟩ := hne
    obtain ⟨ρ, kp, e⟩ := toCls_isAlpha.1 hα
    have hl := Op5.label (hC κ₀ h₀) a ((mem_compMol _ _).1 ha).1 ρ kp e
    rw [e]
    exact ⟨hl.2.1, hl.2.2⟩
  epsLG := by
    rintro κ' ⟨κ, hκ, rfl⟩ a ha hε x y hx hy hxy
    have haM := ((mem_compMol _ _).1 ha).1
    have hε' : (h.op5 Tm).s.cls a = .eps := toCls_isEps.1 hε
    have hx' : (h.op5 Tm).s.M.atom x.1 = a := hx
    have hy' : (h.op5 Tm).s.M.atom y.1 = a := hy
    have hlg : ∀ x' y' : (h.op5 Tm).s.D, (h.op5 Tm).s.M.atom x' = a → (h.op5 Tm).s.M.atom y' = a →
        (h.op5 Tm).s.M.out x' = false → (h.op5 Tm).s.M.out y' = true →
        L ^ (-γ + η) < ‖Molecule.kvec L (0 : Mom d) (κ ∘ (h.op5 Tm).s.down) x' -
          Molecule.kvec L (0 : Mom d) (κ ∘ (h.op5 Tm).s.down) y'‖ := by
      intro x' y' h1 h2 o1 o2
      exact lt_norm_of_LG (Op5.epsLG (hC κ hκ) a haM hε' x' y' h1 h2 o1 o2
        (fun e => hnl x' (by rw [← e, h1, h2])))
    have hxy' : (h.op5 Tm).s.M.out x.1 ≠ (h.op5 Tm).s.M.out y.1 := hxy
    cases hox : (h.op5 Tm).s.M.out x.1
    · have hoy : (h.op5 Tm).s.M.out y.1 = true := by
        cases hoy : (h.op5 Tm).s.M.out y.1
        · exact absurd (hox.trans hoy.symm) hxy'
        · rfl
      exact hlg x.1 y.1 hx' hy' hox hoy
    · have hoy : (h.op5 Tm).s.M.out y.1 = false := by
        cases hoy : (h.op5 Tm).s.M.out y.1
        · rfl
        · exact absurd (hox.trans hoy.symm) hxy'
      have := hlg y.1 x.1 hy' hx' hoy hox
      rw [kvec_comp, kvec_comp, norm_sub_rev]
      exact this

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

end WaveTurbulence.FinalCountAsm
