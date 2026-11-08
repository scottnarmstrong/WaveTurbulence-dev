/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKChain.Comp
public import WaveTurbulence.Foundations.Flower.FinalMKChain.BPers
public import WaveTurbulence.Foundations.Flower.FinalMKChain.Ph3
public import WaveTurbulence.Foundations.FinalCount.LowChain43

/-! # C1b2 MK-CHAIN (10): the terminal bound with survivors (`hterm_mainLE`, the `no_SGL`-MK step)

Copy-thread of main's LowChain42 (`desig_deg2`, on `HingeSG`) and LowChain43 (`hterm_mainL`): at the end of Step 4 of
the survivor run, `QS ≤ WPot (Ypk … |B| (RofS h)) gExp`. Changes:
- the reach relation is `Reach4LE` (survivor Step 1), with B-persistence `QB_reach4E` (`BHypE`: the loop atoms avoid
  the `CollectedF` objects and the survivors);
- the run data is `RunDataLE` (`Reach4LE.toRunLCE`, whose `rem` clause is on `CollectedF` and the survivors), so the
  component wrappers are `unt_comp_boundLE`/`dam_comp_boundLE` (final decorations from `no_SGLE`);
- the obligations are `SubproOblGMK` with `forb = survAtomsM E`, the pool `UnselOKF`; the run facts read only
  `HingeSG`. -/

@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKChain
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountG8
open WaveTurbulence.FinalCountAsm WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u v

section dd
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- Main's `desig_deg2` (LowChain42) from `subpro` (5) only. -/
theorem desig_deg2H {M₀ : Molecule V D₀} {C : CollData M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {hf : HSt V D₀}
    (hH : HingeSG C L γ η w κ) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s) :
    ∀ a ∈ hf.s.M.atoms, hf.s.cls a = .eps → hf.s.M.deg a = 2 → ∀ x y : hf.s.D, hf.s.M.atom x = a →
      hf.s.M.atom y = a → hf.s.M.out x = false → hf.s.M.out y = true → y ≠ hf.s.M.mate x →
      Desig C (hf.anc a) (hf.s.pr x y) := by
  intro a ha hε hdeg x y hxa hya hxo hyo hne
  have hanc : hf.anc a = a := hA.eps a ha hε
  intro hh
  rw [hanc] at hh
  obtain ⟨f, s, x', y', h1, h2, hx', hy', hne', ho1, ho2, hsg, hset⟩ := hinge_orientedH hH hh
  refine ⟨f, s, by rw [hanc]; exact h1, by rw [hanc]; exact h2, Or.inl ?_⟩
  have hd0 : M₀.deg a = 2 := by rw [← deg_eps_eq hA ha hε]; exact hdeg
  have hxy' : x' ≠ y' := by intro e; rw [e] at ho1; rw [ho1] at ho2; exact absurd ho2 (by simp)
  have hsub : ({x', y'} : Finset D₀) ⊆ M₀.dartsAt a := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact (Mole.mem_dartsAt M₀ a z).2 hx'
    · exact (Mole.mem_dartsAt M₀ a z).2 hy'
  have heq : M₀.dartsAt a = {x', y'} := by
    refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
    rw [Finset.card_pair hxy']
    unfold Molecule.deg at hd0; omega
  have hdx : M₀.atom (hf.s.down x) = a := by rw [hD.eps x (by rw [hxa]; exact hε), hxa]
  have hdy : M₀.atom (hf.s.down y) = a := by rw [hD.eps y (by rw [hya]; exact hε), hya]
  have hxm : hf.s.down x ∈ M₀.dartsAt a := (Mole.mem_dartsAt M₀ a _).2 hdx
  have hym : hf.s.down y ∈ M₀.dartsAt a := (Mole.mem_dartsAt M₀ a _).2 hdy
  rw [heq] at hxm hym
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxm hym
  have hox : M₀.out (hf.s.down x) = false := by rw [hD.out]; exact hxo
  have hoy : M₀.out (hf.s.down y) = true := by rw [hD.out]; exact hyo
  have ex : hf.s.down x = x' := by
    rcases hxm with h | h
    · exact h
    · rw [h] at hox; rw [hox] at ho2; exact absurd ho2 (by simp)
  have ey : hf.s.down y = y' := by
    rcases hym with h | h
    · rw [h] at hoy; rw [hoy] at ho1; exact absurd ho1 (by simp)
    · exact h
  show ({hf.s.down x, hf.s.down y} : Set D₀) = {f, s}
  rw [ex, ey]; exact hset

end dd

theorem hterm_mainLE {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000)
    (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type v} [DecidableEq V] [Infinite V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
        {M₀ : Molecule V D₀} {Rn : ℕ} {B : Finset V} {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollDataMK M₀}
        {mE : ℕ} {E : Fin mE → Object M₀}
        {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} {Tm : V → Prop},
        SubHypL Rn M₀ → LadderHered M₀ P → (∀ S, 0 ≤ P S) →
        (∀ κ ∈ A0, SubproOblGMK C.toCollData E L γ η (0 : Mom d) κ) → TripleDesig C.toCollData →
        (∀ κ ∈ A0, C.UnselOKF L γ η (0 : Mom d) κ (Un κ)) → C.forb = survAtomsM E →
        (∀ κ ∈ A0, DegenSGT M₀ L γ η (0 : Mom d) κ Tm) →
        (∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0) →
        (∀ k0 ∈ A0, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y) →
        (∀ k0 ∈ A0, ∀ x, k0 (M₀.mate x) = k0 x) →
        (∀ b ∈ B, b ∈ M₀.atoms) → (∀ b ∈ B, M₀.deg b ≤ 2) → (∀ b ∈ B, Tm b) →
        (∀ v ∈ M₀.atoms, Tm v → M₀.deg v + (if v ∈ B then 2 else 0) < 4 → ∃ k, ∀ k0 ∈ A0, ∀ x, M₀.atom x = v → k0 x = k) →
        (∀ κ ∈ A0, ∀ U, CollectedF C (Un κ) L γ η (0 : Mom d) κ U → ∀ b ∈ B, b ∉ U.atoms) →
        (∀ κ ∈ A0, ∀ i, ∀ b ∈ B, b ∉ (E i).atoms) →
        (∀ κ ∈ A0, ∀ a, crit a → SGat M₀ L γ η (0 : Mom d) κ a) →
        (((2 * M₀.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m) →
        (∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), A ⊆ A0 → LCtx M₀ h.s → ∀ a : V,
          MaxLadderGapAdm (compMol h.s.M a) L (0 : Mom d) P (MoleProp.GapScale L) (compAdm h a (fun k => k ∈ A))) →
        (∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀), A ⊆ A0 → LCtx M₀ h.s → ∀ a : V,
          MaxLadderGapAdm (compMol (h.op5 Tm).s.M a) L (0 : Mom d) P (MoleProp.GapScale L)
            (compAdm (h.op5 Tm) a (fun k => k ∈ A))) →
        ∀ (A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀),
          Inv3L M₀ Rn (Reach4LE C Un Fst E L γ η (0 : Mom d)) L (0 : Mom d) A0 A h →
          (∀ k ∈ A, NoBetaCut L (0 : Mom d) k h.s) →
          QS L γ δ C1 (0 : Mom d) P h A ≤
            WPot L γ η (Ypk L γ η ((η ^ 5 - 4 * η ^ 6) / 2) (rankFactor d L γ δ C1 (B.card : ℤ)) B.card (RofS h.s))
              (gExp η crit) h := by
  have hγ0 : 0 < γ := by linarith [hγ.1]
  have hγ1 : γ < 1 := hγ.2
  have hg0 : gam0 γ ≤ γ := min_le_left _ _
  have hg0' : 0 < gam0 γ := lt_min hγ0 (by linarith)
  have hη1 : η ≤ gam0 γ / 1000 := le_trans (by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    nlinarith) hsm
  have hη4 : η ≤ 1 / 4 := by linarith
  have hγη : 5 * η ≤ γ := by linarith
  have hC0η : (1 : ℝ) * η ^ 4 ≤ 1 := by
    have h1 : η ≤ 1 := by linarith
    have : η ^ 4 ≤ 1 := pow_le_one₀ hη.le h1
    linarith
  obtain ⟨Cu, hCu1, hUnt⟩ := unt_comp_boundLE.{v, u} hd hγ hη hsm hsm2 hηs
  obtain ⟨Cd, hCd1, hDam⟩ := dam_comp_boundLE.{v, u} hd ⟨hγ0, hγ1⟩ hη hsm hηs
  obtain ⟨Lf, hLf1, hFam⟩ := terminal_familyLU.{u, v} (d := d) hd hγ0 hγ1 hη hη1 (C₀ := 1) zero_le_one hC0η
  refine ⟨max Cu Cd, le_trans hCu1 (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨Ru, hRu1, hUnt'⟩ := hUnt m C1 (le_trans (le_max_left _ _) hC1) δ hδ
  obtain ⟨Rd, hRd1, hDam'⟩ := hDam m C1 (le_trans (le_max_right _ _) hC1) δ hδ
  refine ⟨max Ru (max Rd (max Lf (Real.exp 1))), le_trans hRu1 (le_max_left _ _), fun L hL => ?_⟩
  have hLu : Ru ≤ L := le_trans (le_max_left _ _) hL
  have hLd : Rd ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hLf : Lf ≤ L := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hL
  have hL1 : 1 ≤ L := le_trans (Real.one_le_exp (by norm_num)) hLe
  have hL0 : 0 < L := by linarith
  intro V _ _ D₀ _ _ M₀ Rn B P A0 C mE E Un Fst crit Tm hS hP hP0 hobl hT3 hU hforb hdeg h0 hTame hmate hBsub hBdeg hBT hfixE
    hBsg hBsgE hcrit hcard
    hmaxU hmaxD A h hA hn
  by_cases hAe : A = ∅
  · subst hAe; simp [QS_empty]
  obtain ⟨κ₀, hκ₀⟩ := Set.nonempty_iff_ne_empty.2 hAe
  obtain ⟨hA0, h2⟩ := hA
  rcases h2 with he | ⟨hcAny, hap, hr⟩
  · exact absurd he hAe
  have hκ0 : κ₀ ∈ A0 := hA0 hκ₀
  have hBH : BHypE M₀ B C Un E L γ η (0 : Mom d) κ₀ :=
    ⟨hBsub, hBdeg, fun b hb x y hx hy => hTame κ₀ hκ0 b (hBsub b hb) (hBT b hb) x y hx hy,
      fun U hU' b hb => hBsg κ₀ hκ0 U hU' b hb, hBsgE κ₀ hκ0⟩
  obtain ⟨hanc, ⟨R'', hR'', hI⟩, hbp⟩ := QB_reach4E hS (h0 κ₀ hκ0) hBH (hr κ₀ hκ₀)
  have hg : Good R'' h.s := hI.good
  have hRofS : RofS h.s = R'' := rofS_of_inv hg.1
  have hBT' : ∀ b ∈ B, b ∈ tameSet h Tm := fun b hb => tameSet_mem.2 ⟨(hbp b hb).1, (hbp b hb).2, hBT b hb⟩
  have hBdeg' : ∀ b ∈ B, h.s.M.deg b ≤ 2 := BP.deg_le hbp hanc hBH.toBHyp
  have hkle : B.card ≤ R'' := card_le_of_loops hg (fun b hb => (hbp b hb).1) (fun b hb => (hbp b hb).2) hBdeg'
  obtain ⟨r, hRk⟩ : ∃ r, r + B.card = R'' := ⟨R'' - B.card, by omega⟩
  have hLC : LCtx M₀ h.s := LCtx.of_inv hg.1 ⟨h.anc, hanc⟩ hI.rel
  have hRun : RunDataLE L γ η M₀ h (fun k => k ∈ A) := fun κ hκ =>
    ⟨C, mE, E, Un κ, hobl κ (hA0 hκ), hT3, hU κ (hA0 hκ), hforb, Reach4LE.toRunLCE (hr κ hκ) (hn κ hκ)⟩
  have hCon : Prop95ConclL L γ η (0 : Mom d) κ₀ Tm Rn h :=
    FinalMKStep.HRunLE.prop95L (Reach4LE.toRunLCE (hr κ₀ hκ₀) (hn κ₀ hκ₀)).toHRunLE hS
      (SubproOblGMK.hingeSGP (hobl κ₀ hκ0)) hT3 (hdeg κ₀ hκ0) (h0 κ₀ hκ0)
  have hst := hCon.struct
  have hlab : ∀ v ∈ h.s.M.atoms, ∀ ρ kp, h.s.cls v = .alpha ρ kp → L⁻¹ ≤ ρ ∧ ρ ≤ L ^ (-γ + η) ∧ (kp = 0 ∨ kp = 50) :=
    fun v hv ρ kp hc' => by
      obtain ⟨hl, hk, -⟩ := hCon.label v hv ρ kp hc'
      exact ⟨hl.2.1, hl.2.2, hk⟩
  have hdpos : ∀ a ∈ h.s.M.atoms, 1 ≤ h.s.M.deg a := fun a ha => (hst.deg_range a ha).1
  have hM4 : ∀ a ∈ h.s.M.atoms, h.s.M.deg a ≤ 4 := fun a ha => (hst.deg_range a ha).2
  have hcrit0 : critCount crit h.s = 0 := by
    unfold critCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro a ha ⟨hε, hca⟩
    obtain ⟨h₁, h₂, h₃, h₄, -, -, -, -, -, -, -, hsgl, hj⟩ := hr κ₀ hκ₀
    obtain ⟨-, hε3⟩ := HRunN.eps_back hj a ha hε
    exact hsgl a (HRunN.eps_back hj a ha hε).1 hε3 (hcrit κ₀ hκ0 a hca)
  have hgk : 0 < rankFactor d L γ δ C1 (B.card : ℤ) := by
    have hC11 : 1 ≤ C1 := le_trans hCu1 (le_trans (le_max_left _ _) hC1)
    unfold rankFactor
    have : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := mul_pos (inv_pos.2 (by linarith)) (Real.rpow_pos_of_pos hδ.1 _)
    positivity
  obtain ⟨𝒦, j, Rs, h1, hcl, hrk, hkK, hR, hQ⟩ := hFam L hLf C1 δ (le_trans hCu1 (le_trans (le_max_left _ _) hC1)) hδ.1 hδ.2
    hP hP0 hLC (fun k0 hk0 => hTame k0 (hA0 hk0)) (fun k0 hk0 => hmate k0 (hA0 hk0)) hBdeg
    (fun v hv hT hd4 => by
      obtain ⟨k, hk⟩ := hfixE v hv hT hd4
      exact ⟨k, fun k0 hk0 => hk k0 (hA0 hk0)⟩) hBT' hCon.noloop hM4 hdpos
  have hcardh : (h.s.M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m := by
    refine le_trans ?_ hcard
    have := Inv3L.card_atoms_le hS (⟨hA0, Or.inr ⟨hcAny, hap, hr⟩⟩ : Inv3L M₀ Rn (Reach4LE C Un Fst E L γ η (0 : Mom d)) L (0 : Mom d) A0 A h) hAe
    exact_mod_cast this
  have hcomp : ∀ a ∈ Rs, (compMol (h.op5 Tm).s.M a).countA L γ δ C1 (0 : Mom d)
      (projAdm (h.op5 Tm).s.M (compP (h.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) h.s) h.s.M (tameSet h Tm))) P ≤
      ENNReal.ofReal ((∏ v ∈ (compMol (h.op5 Tm).s.M a).atoms, (apFactor L γ η (h.s.cls v))⁻¹) * L ^ exaL γ η h Tm r a) := by
    intro a ha
    have ha5 := hR.mem a ha
    by_cases hu : UntCL h Tm r a
    · refine hUnt' L hLu hS hRun (fun κ hκ => hdeg κ (hA0 hκ)) (fun κ hκ => h0 κ (hA0 hκ)) ⟨κ₀, hκ₀⟩ hP0 hcardh ha5 hu ?_
        (hmaxU A h hA0 hLC a)
      by_cases hco : CompOdd h a
      · have hr1 := hu.2.2 hco
        have hB : ∀ b ∈ B, ¬ h.s.M.SameComponent a b := fun b hb hsc => hu.1 b (hbp b hb).1 hsc (hbp b hb).2 (hBT b hb)
        have := odd_comp_card_le hg hRk (fun b hb => (hbp b hb).1) (fun b hb => (hbp b hb).2) hBdeg' rfl hB
        omega
      · have : ((compMol h.s.M a).atoms.filter fun b => ¬ Even ((compMol h.s.M a).deg b)) = ∅ :=
          Finset.filter_eq_empty_iff.2 (fun b hb hodd => hco ⟨b, hb, hodd⟩)
        rw [this]; simp
    · exact hDam' L hLd hS hRun (fun κ hκ => hdeg κ (hA0 hκ)) (fun κ hκ => h0 κ (hA0 hκ)) ⟨κ₀, hκ₀⟩ hP0 hcardh hg ha5 hu
        (hmaxD A h hA0 hLC a)
  have hLF1 : r = 1 → tameSet h Tm = ∅ → ∀ e ∈ h.s.M.atoms, h.s.cls e = .eps → 3 ≤ h.s.M.deg e := by
    intro hr1 hT
    have hB0 : B = ∅ := Finset.eq_empty_of_forall_notMem fun b hb => by
      have := hBT' b hb; rw [hT] at this; simp at this
    have hcard0 : B.card = 0 := by rw [hB0]; simp
    have hR1 : R'' = 1 := by omega
    have hg1 : Good 1 h.s := hR1 ▸ hg
    obtain ⟨h₂, hN, hA₂, hD₂, hE⟩ := Reach4LE.d3info hS (h0 κ₀ hκ0) (hr κ₀ hκ₀)
    refine lowFree_r1 (C := C.toCollData) (κ := κ₀) (L := L) (γ := γ) (η := η) (w := (0 : Mom d)) hL0 hg1 hI.bal
      (fun v x₁ x₂ hd => noD3_transfer hA₂ hD₂ hanc hI.rel hE hN hd) ?_
      (desig_deg2H (SubproOblGMK.hingeSGP (hobl κ₀ hκ0)) hanc hI.rel)
    intro a ha hε x y hx hy hox hoy hne
    rcases hCon.eps_LG a ha hε with hT' | hlg
    · exfalso
      have := tameSet_mem.2 (⟨ha, hε, hT'⟩ : a ∈ h.s.M.atoms ∧ h.s.cls a = .eps ∧ Tm a)
      rw [hT] at this; simp at this
    · exact hlg x y hx hy hox hoy hne
  rw [hRofS]
  exact hterm_coreL (A := A) (P := P) (L := L) (γ := γ) (η := η) (δ := δ) (C₁ := C1) (C₀ := 1) (crit := crit) hL1 hg0'.le hη hη4 hγη
    le_rfl hg hRk hBT' hBdeg' rfl hcrit0 hlab hdpos hM4 hcl h1 hrk hkK hR hgk hQ hcomp hLF1

end WaveTurbulence.Flower.FinalMKChain
