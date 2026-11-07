/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTopClass3
public import WaveTurbulence.Foundations.FinalCount.AsmClass3
public import WaveTurbulence.Foundations.FinalCount.AsmLadderHered
/-! **FINALCOUNT-ASSEMBLY (molecule-level REG gate).**  `RegClassHyps` bundles the premises of `reg_class_bound` for one class `A0`.
`reg_class_bound'` is `reg_class_bound` stated with it.  `reg_molecule_bound` splits an admissible set into the classes of `labelSet`
(tame set × common vectors), applies `reg_class_bound'` at `C₁/4` to each class, and absorbs the class factor
`|labelSet| 4^{-χ} ≤ (36R²)^R ≤ L^{(R-1)/20 + (η⁵-4η⁶)/4}`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

section stmts
variable {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The premises of `reg_class_bound` for one class. -/
structure RegClassHyps (M₀ : Molecule V D₀) (Rn : ℕ) (P : Finset V → ℝ) (A0 : Set (D₀ → (Fin d → ℤ))) (C : CollData M₀)
    (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀)) (crit Tm : V → Prop) (L γ η : ℝ) (m : ℕ) : Prop where
  subHyp : SubHyp Rn M₀
  isMol : M₀.IsMolecule
  hP : LadderHered M₀ P
  hP0 : ∀ S, 0 ≤ P S
  pinned : PinnedM0 (fun k => k ∈ A0) L (0 : Mom d) M₀
  obl : ∀ κ ∈ A0, SubproOblG C L γ η (0 : Mom d) κ
  trip : TripleDesig C
  unsel : ∀ κ ∈ A0, C.UnselOK L γ η (0 : Mom d) κ (Un κ)
  degen : ∀ κ ∈ A0, DegenSGT M₀ L γ η (0 : Mom d) κ Tm
  h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 →
    ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L (0 : Mom d) κ x = 0
  tameEq : ∀ k0 ∈ A0, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y
  mate : ∀ k0 ∈ A0, ∀ x, k0 (M₀.mate x) = k0 x
  fix : ∀ v ∈ M₀.atoms, Tm v → M₀.deg v < 4 → ∃ k, ∀ k0 ∈ A0, ∀ x, M₀.atom x = v → k0 x = k
  critSG : ∀ κ ∈ A0, ∀ a, crit a → SGat M₀ L γ η (0 : Mom d) κ a
  card : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m
  srcGaps : ∀ k ∈ A0, SourceLadderGaps M₀ L (0 : Mom d) P k
  dec : ∀ k ∈ A0, ∃ c0, M₀.IsDecoration L (0 : Mom d) c0 k ∧ ∀ x ∈ M₀.atoms, M₀.deg x = 4 → c0 x = 0
  hmem : HmemAt M₀ Rn C L γ η (0 : Mom d) A0 Un Fst crit
  hend : HendAt M₀ Rn C L γ η (0 : Mom d) A0 Un Fst (2 * (Rn : ℝ) - 1)

/-- `reg_class_bound` with the premises bundled. -/
theorem reg_class_bound' {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {Rn : ℕ}
        {P : Finset V → ℝ} {A0 : Set (D₀ → (Fin d → ℤ))} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
        {Fst : Set (Object M₀)} {crit Tm : V → Prop},
        RegClassHyps (d := d) M₀ Rn P A0 C Un Fst crit Tm L γ η m →
        M₀.countA L γ δ C1 (0 : Mom d) (fun k => k ∈ A0) P ≤
          ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
            L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4)) := by
  obtain ⟨Cs, hCs, h⟩ := reg_class_bound hd hγ hη hsm hsm2 hηs
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR₀, h2⟩ := h m C1 hC1 δ hδ
  refine ⟨R₀, hR₀, fun L hL V _ _ D₀ _ _ M₀ Rn P A0 C Un Fst crit Tm H => ?_⟩
  exact h2 L hL H.subHyp H.isMol H.hP H.hP0 H.pinned H.obl H.trip H.unsel H.degen H.h0 H.tameEq H.mate H.fix H.critSG H.card
    H.srcGaps H.dec H.hmem H.hend

/-- **The molecule-level REG bound** (class split, `C₁/4`, absorption). -/
theorem reg_molecule_bound {d : ℕ} (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hsm2 : (d : ℝ) * η ≤ (2 * γ - 1) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M₀ : Molecule V D₀} {Rn : ℕ}
        {P : Finset V → ℝ} {Adm : (D₀ → (Fin d → ℤ)) → Prop} {C : CollData M₀}
        {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {crit : V → Prop} (kFix : Finset (Mom d)),
        SubHyp Rn M₀ → kFix.card ≤ 2 * Rn → (Rn : ℝ) ≤ (1 + Real.log L) ^ c →
        (∀ κ, Adm κ → ∀ x, κ (M₀.mate x) = κ x) →
        (∀ lab ∈ labelSet M₀ kFix, (∃ κ, Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ) →
          RegClassHyps (d := d) M₀ Rn P {κ | Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ} C Un Fst
            crit (fun v => v ∈ lab.1) L γ η m) →
        M₀.countA L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
            L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40))) := by
  obtain ⟨Cs, hCs, hreg⟩ := reg_class_bound' hd hγ hη hsm hsm2 hηs
  have hγ0 : 0 < γ := by linarith [hγ.1]
  have hγ1 : γ < 1 := hγ.2
  have hη40 : η ≤ 1 / 40 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    nlinarith [hsm, min_le_left γ (1 - γ)]
  have hεpos : 0 < (η ^ 5 - 4 * η ^ 6) / 4 := by
    have h5 : 0 < η ^ 5 := by positivity
    have : 4 * η ^ 6 < η ^ 5 := by
      have : η ^ 6 = η * η ^ 5 := by ring
      rw [this]; nlinarith
    linarith
  refine ⟨Cs, hCs, fun m c C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₁, hR₁, h1⟩ := hreg m (C1 / 4) (by linarith) δ hδ
  obtain ⟨L₁, hL₁, h2⟩ := absorb_Rpow 36 (by norm_num) c ((η ^ 5 - 4 * η ^ 6) / 4) hεpos
  refine ⟨max R₁ L₁, le_trans hR₁ (le_max_left _ _), fun L hL V _ _ D₀ _ _ M₀ Rn P Adm C Un Fst crit kFix hS hk hRc hAdm hclass => ?_⟩
  have hLa : R₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLb : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hL1 : 1 ≤ L := le_trans hR₁ hLa
  have hL0 : 0 < L := by linarith
  have hRn : 1 ≤ Rn := hS.one_le
  set S := labelSet M₀ kFix with hSdef
  have hcl : ∀ lab ∈ S, M₀.countA L γ δ (C1 / 4) (0 : Mom d) (fun κ => Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ) P ≤
      ENNReal.ofReal (L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
        L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4)) :=
    fun lab hlab => by
      by_cases hne : ∃ κ, Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ
      · exact h1 L hLa (hclass lab hlab hne)
      · push Not at hne
        have h0 := countA_union_le M₀ L γ δ (C1 / 4) (0 : Mom d) (∅ : Finset Bool)
          (Adm := fun κ => Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ) (fun _ _ => True)
          (fun κ hκ => absurd hκ.2 (hne κ hκ.1)) P
        simp only [Finset.sum_empty] at h0
        exact h0.trans bot_le
  have hB : 0 ≤ L ^ (-4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))) *
        L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4) := by positivity
  have hcover : ∀ κ, Adm κ → ∃ lab ∈ S, Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ := by
    intro κ hκ
    obtain ⟨lab, hl, hc⟩ := exists_classLabel hS L (0 : Mom d) kFix κ (hAdm κ hκ) hL0.ne'
    exact ⟨lab, hl, hκ, hc⟩
  have key := countA_le_sum_classes M₀ L γ δ C1 (0 : Mom d) S (fun lab κ => Adm κ ∧ InClass M₀ L (0 : Mom d) kFix lab.1 lab.2 κ)
    P hcover hB hcl
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the circuit rank
  have hχ : M₀.circuitRank = (M₀.atoms.card : ℤ) - Rn + 1 := by
    unfold Molecule.circuitRank
    rw [numComponents_init hS]
    have := hS.count
    omega
  have hSc : (S.card : ℝ) ≤ (2 : ℝ) ^ M₀.atoms.card * (2 * (Rn : ℝ) + 1) ^ (2 * Rn) := by
    have := labelSet_card_le hS kFix hk
    exact_mod_cast this
  have hfac : (S.card : ℝ) * (4 : ℝ) ^ (-M₀.circuitRank) ≤ (36 * (Rn : ℝ) ^ 2) ^ Rn := by
    rw [hχ]
    refine le_trans (mul_le_mul_of_nonneg_right hSc (by positivity)) ?_
    have := class_factor_le M₀.atoms.card Rn hRn
    convert this using 2
  have habs := h2 L hLb Rn hRn hRc
  set E1 : ℝ := -4 * η ^ 6 * ((M₀.rho : ℝ) + ((M₀.atoms.filter crit).card : ℝ))
  set E2 : ℝ := ((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4
  have hE : (((Rn : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) + E2 = ((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40) := by
    simp only [E2]; ring
  calc (S.card : ℝ) * 4 ^ (-M₀.circuitRank) * (L ^ E1 * L ^ E2)
      ≤ L ^ (((Rn : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) * (L ^ E1 * L ^ E2) := by
        gcongr
        exact hfac.trans habs
    _ = L ^ E1 * L ^ ((((Rn : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) + E2) := by
        rw [Real.rpow_add hL0 (((Rn : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) E2]; ring
    _ = L ^ E1 * L ^ (((Rn : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)) := by rw [hE]


end stmts

end WaveTurbulence.FinalCountAsm
