/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.FinalCount.LowGardenSplit3

/-! # C1c MK-GARDEN / MolMK: the molecule-level LOW bound with survivors, from `LowLoopClassBoundMK`

Copy of main's `lowLoop_molecule_bound_of` (LowGardenSplit3) with the class hypotheses `LowLoopClassHypsMK` over
`CollDataMK` and the extra factor `L^{2m}` carried through. -/

@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.Flower.FinalMKGarden
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount WaveTurbulence.FinalCountAsm WaveTurbulence.Flower.FinalMKDefs

section mol
variable {d : ℕ}

/-- **The molecule-level LOW bound with loops and survivors.** -/
def LowLoopMoleculeBoundMK (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ mm c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type} [DecidableEq V] [Infinite V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {M : Molecule V D₀} {R : ℕ}
      {P0 : Finset V → ℝ} {Adm : (D₀ → (Fin d → ℤ)) → Prop} {C : CollDataMK M.unloop} {m : ℕ}
      {E : Fin m → Object M.unloop}
      {Un : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop)} {Fst : Set (Object M.unloop)} {crit : V → Prop}
      (kFix : Finset (Mom d)),
      SubHypLoop R M → kFix.card ≤ 2 * R → (R : ℝ) ≤ (1 + Real.log L) ^ c →
      (∀ κ, Adm κ → ∀ x, κ (M.mate x) = κ x) →
      (∀ κ₁ κ₂, Adm κ₁ → Adm κ₂ → (∀ x : D₀, M.atom x ≠ M.atom (M.mate x) → κ₁ x = κ₂ x) → κ₁ = κ₂) →
      (∀ S ∈ M.maximalLadders, 0 ≤ P0 S) →
      (∀ lab ∈ labelSet M kFix, (∃ κ, Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) →
        LowLoopClassHypsMK (d := d) M R (heredScale' M.unloop P0)
          {κ' | unloopAdm M (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) κ'} C E Un Fst crit
          (fun v => v ∈ lab.1) L γ η mm) →
      M.countA L γ δ C1 (0 : Mom d) Adm P0 ≤
        ENNReal.ofReal (L ^ (2 * (m : ℝ)) *
          L ^ (-4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)))

theorem lowLoop_molecule_bound_of_MK {d : ℕ} {γ η : ℝ} (hη : 0 < η) (hη40 : η ≤ 1 / 40) (hcl : LowLoopClassBoundMK d γ η) :
    LowLoopMoleculeBoundMK d γ η := by
  obtain ⟨Cs, hCs, hreg⟩ := hcl
  have hεpos : 0 < (η ^ 5 - 4 * η ^ 6) / 4 := by
    have h5 : 0 < η ^ 5 := by positivity
    have : 4 * η ^ 6 < η ^ 5 := by
      have : η ^ 6 = η * η ^ 5 := by ring
      rw [this]; nlinarith
    linarith
  refine ⟨Cs, hCs, fun m c C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₁, hR₁, h1⟩ := hreg m (C1 / 4) (by linarith) δ hδ
  obtain ⟨L₁, hL₁, h2⟩ := absorb_Rpow 36 (by norm_num) c ((η ^ 5 - 4 * η ^ 6) / 4) hεpos
  refine ⟨max R₁ L₁, le_trans hR₁ (le_max_left _ _),
    fun L hL V _ _ D₀ _ _ M R P0 Adm C m E Un Fst crit kFix hS hk hRc hAdm hdet hP0 hclass => ?_⟩
  have hLa : R₁ ≤ L := le_trans (le_max_left _ _) hL
  have hLb : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hL1 : 1 ≤ L := le_trans hR₁ hLa
  have hL0 : 0 < L := by linarith
  have hRn : 1 ≤ R := hS.one_le
  have hb4 : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => deg_le_four M (hS.bounds a ha)
  have hC10' : 0 ≤ C1 / 4 := by linarith
  have hC1pos : 0 < C1 / 4 := by linarith
  have hP0' : ∀ S ∈ M.unloop.maximalLadders, 0 ≤ P0 S := by rw [unloop_maximalLadders]; exact hP0
  set S := labelSet M kFix with hSdef
  have hcl : ∀ lab ∈ S, M.countA L γ δ (C1 / 4) (0 : Mom d) (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) P0 ≤
      ENNReal.ofReal (L ^ (2 * (m : ℝ)) * L ^ (-4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))) *
        L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4)) :=
    fun lab hlab => by
      by_cases hne : ∃ κ, Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ
      · have hdet' : ∀ κ₁ κ₂, (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) κ₁ →
            (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) κ₂ →
            (∀ x : D₀, M.atom x ≠ M.atom (M.mate x) → κ₁ x = κ₂ x) → κ₁ = κ₂ :=
          fun κ₁ κ₂ h₁ h₂ h => hdet κ₁ κ₂ h₁.1 h₂.1 h
        calc M.countA L γ δ (C1 / 4) (0 : Mom d) (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) P0
            ≤ ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * ((C1 / 4)⁻¹ * δ ^ (1 / 2 : ℝ))) ^ M.loopBonds.card) *
                M.unloop.countA L γ δ (C1 / 4) (0 : Mom d)
                  (unloopAdm M (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ)) P0 :=
              countA_unloop_le M hb4 L γ δ (C1 / 4) hL0 hC1pos hδ.1 (0 : Mom d) _ hdet' P0
          _ ≤ ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * ((C1 / 4)⁻¹ * δ ^ (1 / 2 : ℝ))) ^ M.loopBonds.card) *
                M.unloop.countA L γ δ (C1 / 4) (0 : Mom d)
                  (unloopAdm M (fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ)) (heredScale' M.unloop P0) := by
              gcongr
              exact countA_le_hered M.unloop L γ δ (C1 / 4) (0 : Mom d) _ hL0 hδ.1.le hC10' hP0'
          _ ≤ _ := h1 L hLa (hclass lab hlab hne)
      · push Not at hne
        have h0 := countA_union_le M L γ δ (C1 / 4) (0 : Mom d) (∅ : Finset Bool)
          (Adm := fun κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ) (fun _ _ => True)
          (fun κ hκ => absurd hκ.2 (hne κ hκ.1)) P0
        simp only [Finset.sum_empty] at h0
        exact h0.trans bot_le
  have hB : 0 ≤ L ^ (2 * (m : ℝ)) * L ^ (-4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))) *
        L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4) := by positivity
  have hcover : ∀ κ, Adm κ → ∃ lab ∈ S, Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ := by
    intro κ hκ
    obtain ⟨lab, hl, hc⟩ := exists_classLabelLoop hS L (0 : Mom d) kFix κ (hAdm κ hκ) hL0.ne'
    exact ⟨lab, hl, hκ, hc⟩
  have key := countA_le_sum_classes M L γ δ C1 (0 : Mom d) S (fun lab κ => Adm κ ∧ InClass M L (0 : Mom d) kFix lab.1 lab.2 κ)
    P0 hcover hB hcl
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hχ : M.circuitRank = (M.atoms.card : ℤ) - R + 1 := by
    unfold Molecule.circuitRank
    rw [numComponents_initLoop hS]
    have := hS.count
    omega
  have hSc : (S.card : ℝ) ≤ (2 : ℝ) ^ M.atoms.card * (2 * (R : ℝ) + 1) ^ (2 * R) := by
    have := labelSet_card_leLoop hS kFix hk
    exact_mod_cast this
  have hfac : (S.card : ℝ) * (4 : ℝ) ^ (-M.circuitRank) ≤ (36 * (R : ℝ) ^ 2) ^ R := by
    rw [hχ]
    refine le_trans (mul_le_mul_of_nonneg_right hSc (by positivity)) ?_
    have := class_factor_le M.atoms.card R hRn
    convert this using 2
  have habs := h2 L hLb R hRn hRc
  set E1 : ℝ := -4 * η ^ 6 * ((M.unloop.rho : ℝ) + ((M.unloop.atoms.filter crit).card : ℝ))
  set E2 : ℝ := ((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40 - 1 / 20) - (η ^ 5 - 4 * η ^ 6) / 4
  have hE : (((R : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) + E2 = ((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40) := by
    simp only [E2]; ring
  have h3 : (S.card : ℝ) * 4 ^ (-M.circuitRank) * (L ^ E1 * L ^ E2) ≤
      L ^ E1 * L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)) := by
    calc (S.card : ℝ) * 4 ^ (-M.circuitRank) * (L ^ E1 * L ^ E2)
        ≤ L ^ (((R : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) * (L ^ E1 * L ^ E2) := by
          gcongr
          exact hfac.trans habs
      _ = L ^ E1 * L ^ ((((R : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) + E2) := by
          rw [Real.rpow_add hL0 (((R : ℝ) - 1) / 20 + (η ^ 5 - 4 * η ^ 6) / 4) E2]; ring
      _ = L ^ E1 * L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)) := by rw [hE]
  calc (S.card : ℝ) * 4 ^ (-M.circuitRank) * (L ^ (2 * (m : ℝ)) * L ^ E1 * L ^ E2)
      = L ^ (2 * (m : ℝ)) * ((S.card : ℝ) * 4 ^ (-M.circuitRank) * (L ^ E1 * L ^ E2)) := by ring
    _ ≤ L ^ (2 * (m : ℝ)) * (L ^ E1 * L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40))) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

end mol

end WaveTurbulence.Flower.FinalMKGarden
