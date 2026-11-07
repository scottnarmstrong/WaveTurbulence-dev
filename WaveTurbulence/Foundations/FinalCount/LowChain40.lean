/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain39
/-! **FINALCOUNT LOW-CHAIN, session 6 (14): the component wrappers `unt_comp_boundL`, `dam_comp_boundL`** (ports of `unt_comp_bound`,
`dam_comp_bound` with `SubHypL`/`RunDataL`/`Prop95ConclL`; the odd-component clause is a component-level hypothesis). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe v u

theorem unt_comp_boundL {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type v} [DecidableEq V] [Infinite V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
        {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {Rn r : ℕ} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ},
        SubHypL Rn M₀ → RunDataL L γ η M₀ hf (fun k => k ∈ A) →
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
  obtain ⟨C, Unsel, obl, hT3, -, hrC⟩ := hrun κ₀ hκ₀
  obtain ⟨R', -, hI⟩ := hrC.toHRunL.inv (InvL.init hS (h0 κ₀ hκ₀))
  have hC : Prop95ConclAtL L γ η (0 : Mom d) κ₀ Rn hf Tm :=
    (hrC.toHRunL.prop95L hS obl hT3 (hdeg κ₀ hκ₀) (h0 κ₀ hκ₀)).toAtL (fun a ha => hI.good.2 a ha)
  have hshape := finalShape_compL' hC haM (hodd) hT hU.2.1
  have hdec := finalDec_compL hS (fun k => k ∈ A) hrun hdeg h0 ⟨κ₀, hκ₀⟩ hL1 hη.le haM hT hU.2.1
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


theorem Op5.epsLGL {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {L γ η : ℝ} {w : Mom d}
    {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {h : HSt V D₀} (hC : Prop95ConclL L γ η w κ Tm R h) :
    ∀ a ∈ (h.op5 Tm).s.M.atoms, (h.op5 Tm).s.cls a = .eps → ∀ x y : (h.op5 Tm).s.D,
      (h.op5 Tm).s.M.atom x = a → (h.op5 Tm).s.M.atom y = a → (h.op5 Tm).s.M.out x = false →
      (h.op5 Tm).s.M.out y = true → y ≠ (h.op5 Tm).s.M.mate x →
      Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ (h.op5 Tm).s.down) x y) = .LG := by
  intro a ha hae x y hx hy hox hoy hxy
  obtain ⟨haM, haT⟩ := Op5.atoms_sub ha
  have hae' : h.s.cls a = .eps := hae
  have hnT : ¬ Tm a := fun hT => haT (tameSet_mem.2 ⟨haM, hae', hT⟩)
  exact (hC.eps_LG a haM hae').resolve_left hnT x.1.1 y.1.1 hx hy hox hoy (by
    intro e; apply hxy; exact Subtype.ext (Subtype.ext e))

theorem Op5.labelL {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ} {L γ η : ℝ} {w : Mom d}
    {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {h : HSt V D₀} (hC : Prop95ConclL L γ η w κ Tm R h) :
    ∀ a ∈ (h.op5 Tm).s.M.atoms, ∀ ρ kp, (h.op5 Tm).s.cls a = .alpha ρ kp → IsLabel L γ η ρ := by
  intro a ha ρ kp hc
  obtain ⟨haM, -⟩ := Op5.atoms_sub ha
  exact (hC.label a haM ρ kp hc).1

section dam
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {Tm : V → Prop}

/-- Copy of `Op5.damagedDec` with the no-loop property as a hypothesis (the `R` of `Good` there is unrelated to that of `Prop95ConclL`). -/
theorem op5_damagedDecL {h : HSt V D₀} {R : ℕ} (hnl : ∀ x : (h.op5 Tm).s.D, (h.op5 Tm).s.M.atom x ≠ (h.op5 Tm).s.M.atom ((h.op5 Tm).s.M.mate x))
    (AdmRun : (D₀ → (Fin d → ℤ)) → Prop)
    (hC : ∀ κ, AdmRun κ → Prop95ConclL L γ η (0 : Mom d) κ Tm R h) (hne : ∃ κ, AdmRun κ) {a₀ : V} :
    G8Copy.DamagedDec (compMol (h.op5 Tm).s.M a₀) (fun a => toCls ((h.op5 Tm).s.cls a)) L γ η
      (compAdm (h.op5 Tm) a₀ AdmRun) where
  labRange := by
    intro a ha hα
    obtain ⟨κ₀, h₀⟩ := hne
    obtain ⟨ρ, kp, e⟩ := toCls_isAlpha.1 hα
    have hl := Op5.labelL (hC κ₀ h₀) a ((mem_compMol _ _).1 ha).1 ρ kp e
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
      exact lt_norm_of_LG (Op5.epsLGL (hC κ hκ) a haM hε' x' y' h1 h2 o1 o2
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

theorem dam_comp_boundL {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type v} [DecidableEq V] [Infinite V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
        {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {Rn R' r : ℕ} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ},
        SubHypL Rn M₀ → RunDataL L γ η M₀ hf (fun k => k ∈ A) →
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
    obtain ⟨C, Unsel, obl, hT3, -, hrC⟩ := hrun κ hκ
    exact hrC.toHRunL.prop95L hS obl hT3 (hdeg κ hκ) (h0 κ hκ)
  obtain ⟨κ₀, hκ₀⟩ := hne
  obtain ⟨R5, -, hg5⟩ := Op5.good (Tm := Tm) hg
  have hn : NoTripleBond (hf.op5 Tm).s.M := noTriple_eraseSetSt (hCN κ₀ hκ₀).no_triple _
  have himp : ∃ b ∈ (hf.op5 Tm).s.M.atoms, (hf.op5 Tm).s.M.SameComponent a b ∧ contrib (hf.op5 Tm).s b ≠ 0 := by
    by_contra hcon
    push_neg at hcon
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


end WaveTurbulence.FinalCountAsm
