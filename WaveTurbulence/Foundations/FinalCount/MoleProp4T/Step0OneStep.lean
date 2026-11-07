/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Step0NotRemoved
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.NoBridge
import Mathlib.Tactic

/-! # One (Y2) sequence: the split of `𝕄′` gives the split of `𝕄`

For a 4-regular connected `𝕄` and a (Y) sequence ending in (Y2), with post molecule `𝕄′`: if every bond `ℓ′` of `𝕄′`
admits a split `SplitBound 𝕄′ ℓ′` (LG parameter `η/2`), then every bond `ℓ` of `𝕄` admits one (LG parameter `η`),
with both bounds multiplied by the (Y2) constant `K = 110 |scaleSet L|² (log L)^{12}`. The split of `𝕄` is the pull back
of that of `𝕄′` for `ℓ′ = ℓ` (if `ℓ` survives) or `ℓ′` = the new bond (if the sequence removes `ℓ`).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4

/-- **The split through one (Y2) sequence.** -/
theorem split_transfer_Y2 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2), (∀ v ∈ M.atoms, M.deg v = 4) →
      (∀ u ∈ M.atoms, ∀ v ∈ M.atoms, M.SameComponent u v) → ∀ (C : YChain M) (E : Y2End C),
      (∀ S ∈ MoleProp.ladderCells (E.toTwoExit hcap).post, (E.toTwoExit hcap).c ∈ S →
        GoodCell (E.toTwoExit hcap).post S) →
      ∀ ε₁ ε₂ : ℝ, (∀ e₁, SplitBound (E.toTwoExit hcap).post e₁ d L γ δ (η / 2) C1 ε₁ ε₂) →
      ∀ e : D, SplitBound M e d L γ δ η C1 (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * ε₁)
        (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 * ε₂) := by
  obtain ⟨Cs1, hCs1, h1⟩ := twoExit_bound_adm d hd γ hγ η hη hηmax
  obtain ⟨Cs2, hCs2, h2⟩ := ylem2_second_adm d hd γ hγ η hη hηmax
  refine ⟨max Cs1 Cs2, hCs1.trans (le_max_left _ _), fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R1, hR1⟩ := h1 C1 (by linarith [le_max_left Cs1 Cs2]) δ hδ
  obtain ⟨R2, hR2⟩ := h2 C1 (by linarith [le_max_right Cs1 Cs2]) δ hδ
  refine ⟨max (max R1 R2) (max (Real.exp 1) ((11 : ℝ) ^ (2 / η))), fun L hL => ?_⟩
  intro V D _ _ _ M hcap h4 hconn C E hgood ε₁ ε₂ hpost e
  classical
  have hLR1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLR2 : R2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL11' : (11 : ℝ) ^ (2 / η) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hL11 : 11 ≤ L ^ (η / 2) := by
    calc (11 : ℝ) = ((11 : ℝ) ^ (2 / η)) ^ (η / 2) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ L ^ (η / 2) := Real.rpow_le_rpow (by positivity) hL11' (by positivity)
  set K := 110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6
  have hK0 : 0 ≤ K := by positivity
  have heven : ∀ v ∈ M.atoms, Even (M.deg v) := fun v hv => by rw [h4 v hv]; exact ⟨2, rfl⟩
  have hconnN := eraseBond_connected_of_even M heven hconn e
  have hTY := E.toTwoExit_Y hcap
  have hdegY : ∀ v ∈ (E.toTwoExit hcap).Y, M.deg v = 4 := by rw [hTY]; exact E.deg_four
  have hpiece : ∀ u ∈ (E.toTwoExit hcap).Y, ∀ v ∈ (E.toTwoExit hcap).Y,
      (piece M (E.toTwoExit hcap).Y).SameComponent u v := by rw [hTY]; exact C.piece_connected
  have hY2M : ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) → _ := fun P hP =>
    hR1 L hLR1 M hcap (E.toTwoExit hcap) hdegY hpiece hgood P hP
  have hmul : ∀ ε : ℝ, ENNReal.ofReal K * ENNReal.ofReal ε = ENNReal.ofReal (K * ε) := fun ε =>
    (ENNReal.ofReal_mul hK0).symm
  by_cases hrem : M.atom e ∈ C.set ∨ M.atom (M.mate e) ∈ C.set
  · -- `ℓ` removed: pull back the split of `𝕄′` at the new bond
    obtain ⟨Q₁, hQ₁a, hQ₁b⟩ := hpost (Sum.inr true)
    refine ⟨(E.toTwoExit hcap).pullQ L γ η Q₁, fun P hP => ?_, fun P hP => ?_⟩
    · rw [← hmul]
      exact (E.toTwoExit hcap).split_first_Y2 hcap hL1 hL11 P (hY2M P hP) Q₁ hQ₁a
    · rw [← hmul]
      refine E.split_second_removed hcap e hrem P ?_ Q₁ hQ₁b
      intro Adm hAdm Φ hΦ
      exact hR2 L hLR2 M hcap C E e hrem hconnN P hP hrem Adm hAdm Φ hΦ
  · -- `ℓ` kept
    push Not at hrem
    have heY : M.atom e ∉ (E.toTwoExit hcap).Y ∧ M.atom (M.mate e) ∉ (E.toTwoExit hcap).Y := by
      rw [hTY]; exact hrem
    obtain ⟨Q₁, hQ₁a, hQ₁b⟩ := hpost (Sum.inl ⟨e, heY.1, heY.2⟩)
    refine ⟨(E.toTwoExit hcap).pullQ L γ η Q₁, fun P hP => ?_, fun P hP => ?_⟩
    · rw [← hmul]
      exact (E.toTwoExit hcap).split_first_Y2 hcap hL1 hL11 P (hY2M P hP) Q₁ hQ₁a
    · rw [← hmul]
      have hcapN := caps_eraseBond M e hcap
      obtain ⟨hu, hw⟩ := hrem
      refine E.split_second_kept hcap e heY hu hw hconnN P Q₁ ?_ hQ₁b
      intro T' hgood' Adm hAdm W hW
      have hYo : T'.Y = (C.outChain e hu hw).set := (E.outEnd e hu hw).toTwoExit_Y hcapN
      have hP' : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond M e), 0 ≤ P S := hP
      refine hR1 L hLR1 (MoleProp.eraseBond M e) hcapN T' ?_ ?_ hgood' P hP' Adm hAdm W hW
      · rw [hYo]
        intro v hv
        rw [deg_eraseBond_of_ne M e (fun h => hu (h ▸ hv)) (fun h => hw (h ▸ hv))]
        exact E.deg_four v hv
      · rw [hYo]; exact (C.outChain e hu hw).piece_connected

end WaveTurbulence.MoleProp4
