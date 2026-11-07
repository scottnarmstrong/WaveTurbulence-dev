/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeFiberEncard
public import WaveTurbulence.Foundations.FinalCount.PairGain
import Mathlib.Tactic

/-! # `MergeInput` (DH23 L1977): merging a double pair without a small gap

`Δχ = −1`; the fibre of the restriction to the merged molecule is the two-vector count of Lemma A.3(1)
(`MergeFiberBound`); the cells through the merged atom get scales from `scaleFam`. Deviation `L^{−η/2}`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4 WaveTurbulence.CountLemmas

theorem mergeAt {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ} (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) {δ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) {C1 : ℝ} (hC1 : 0 < C1) :
    ∃ K B R : ℝ, ∀ L ≥ R, MergeAt.{u, v} d L γ δ η C1 K B := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cp, hCp0, hCp⟩ := pairSet_card_le m γ η hγ hη hηmax
  refine ⟨50 * (Cp * δ⁻¹ + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)), 10, Real.exp 1, fun L hL => ?_⟩
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hL
  have hl10 : Real.log L ^ (10 : ℝ) = Real.log L ^ 10 := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  intro V D _ _ _ M hcap hloop v₁ v₂ hv₁ hv₂ hne hbb h1 h2 hconn hgood P hP Adm hAdm
  classical
  obtain ⟨x, y, r₁, r₂, s₁, s₂, hxy, hxr1, hxr2, hyr1, hyr2, hrr, _, _, _, _, _, _, hxa, hxb, hya, hyb, hA, hB, hpair⟩ :=
    stars44 M hne h1 h2 hbb
  have hdegM : ∀ w ∈ M.atoms, M.deg w ≤ 4 := fun w hw => by
    have h := hcap w hw
    have hsum := Mole.outdeg_add_indeg M w
    omega
  set N := mergePair M v₁ v₂ hv₁ hne with hN
  have hloopN := Merge.loopFree (M := M) (v₁ := v₁) (v₂ := v₂) (hv₁ := hv₁) (hne := hne) hloop
  have hdegN : ∀ a ∈ N.atoms, N.deg a ≤ 4 := by
    intro a ha
    by_cases hav : a = v₁
    · subst hav
      have : N.deg a = 4 := MergeSum.merge_deg_v₁ (hv₁ := hv₁) (hne := hne) hloop h1 h2 hbb
      omega
    · rw [Merge.deg_of_ne (M := M) (hv₁ := hv₁) (hne := hne) hav (mem_erase.mp ha).1]
      exact hdegM a (mem_erase.mp ha).2
  have hopen : ∀ S ∈ MoleProp.ladderCells N, v₁ ∈ S → GoodCell N S := fun S hS _ => hgood S hS
  set Φ : ℕ∞ := (⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ∞) with hΦ
  have hfib : ∀ (c : V → Mom (m + 2)) (β : V → ℝ) (k0 : D → Mom (m + 2)) (κ₀ : D → (Fin (m + 2) → ℤ)),
      M.IsDecoration L (0 : Mom (m + 2)) c κ₀ → M.IsRestricted L γ δ (0 : Mom (m + 2)) β k0 κ₀ → Adm κ₀ →
      {κ | (M.IsDecoration L (0 : Mom (m + 2)) c κ ∧ M.IsRestricted L γ δ (0 : Mom (m + 2)) β k0 κ ∧ Adm κ) ∧
        (fun y : OffPair M v₁ v₂ => κ y.val) = fun y => κ₀ y.val}.encard ≤ Φ := by
    intro c β k0 κ₀ hdec hres hadm
    exact MergeSum.merge_fiber_encard m (fun a b nk β ε hg => hCp L hL1 δ hδ a b nk β ε hg) hLp hv₁ hxy hxr1 hxr2 hyr1 hyr2 hrr
      hxa hxb hya hyb hne hA hpair Adm c β k0 κ₀ hdec hres (hAdm κ₀ hadm).1.1
  have hE := MergeSum.countEFree_le_merge (hv₁ := hv₁) (hne := hne) hv₂ hloopN hdegN hopen hL1 hδ.1 P Adm hAdm Φ hfib
  set fam := MergeSum.scaleFam M v₁ v₂ hv₁ hne L P with hfam
  have hfamcard := MergeSum.card_scaleFam_le (hv₁ := hv₁) (hne := hne) hloopN hdegN L P
  have hPN : ∀ S ∈ MoleProp.ladderCells N, v₁ ∉ S → 0 ≤ P S := by
    intro S hS h1S
    have hSsub := (mem_filter.mp hS).1
    have hc := (mem_filter.mp hS).2
    have h2S : v₂ ∉ S := fun h => (mem_erase.mp (mem_powerset.mp hSsub h)).1 rfl
    have := (MergeSum.isLadderCell_merge_iff (hv₁ := hv₁) (hne := hne) h1S h2S).mp hc
    exact hP S (mem_filter.mpr ⟨mem_powerset.mpr (fun a ha => (mem_erase.mp (mem_powerset.mp hSsub ha)).2), this⟩)
  rw [MoleProp.countAFree_eq_normalization]
  set G := fun P' => MoleProp.countEFree N L γ δ (0 : Mom (m + 2))
    (fun κ' => lgAdm N L γ η P' κ' ∧ mergeAdm M v₁ v₂ Adm κ') with hG
  have hsupeq : (⨆ P' ∈ fam, G P') = fam.sup G := by rw [Finset.sup_eq_iSup]
  rw [hsupeq] at hE
  rcases fam.eq_empty_or_nonempty with hfe | hfne
  · rw [hfe, Finset.sup_empty, bot_eq_zero, mul_zero] at hE
    rw [nonpos_iff_eq_zero.mp hE]
    simp
  obtain ⟨P0, hP0, hmax⟩ := exists_mem_eq_sup fam hfne G
  rw [hmax] at hE
  have hP0nn := MergeSum.scaleFam_nonneg hP0 hPN
  have hagree := MergeSum.scaleFam_agree hP0
  have hcellsM := MergeSum.cellProduct_le_merge (hv₁ := hv₁) (hne := hne) (γ := γ) hv₂ hloop hdegM hLp.le hδ.1.le hlog P P0 hP hP0nn hagree
  have hrk := MergeSum.merge_circuitRank (hv₁ := hv₁) (hne := hne) hv₂ hloop h1 h2 hbb hconn
  have hbne : (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ≠ 0 := by have := hδ.1; positivity
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  have nq := MoleProp.freeNormalization_pos N (d := m + 2) (γ := γ) hLp hδ.1 hC1 hlog0 P0 hP0nn
  have hnorm : MoleProp.freeNormalization M (d := m + 2) L γ δ C1 P ≤
      (L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 * (Real.log L ^ 2) ^ 4) *
        MoleProp.freeNormalization N (d := m + 2) L γ δ C1 P0 := by
    unfold MoleProp.freeNormalization
    have hrk' : M.circuitRank = N.circuitRank + ((1 : ℕ) : ℤ) := by rw [hrk]; rfl
    have hsplit := norm_split (L := L) (a := ((m + 2 : ℕ) : ℝ) - γ) hLp hbne hrk' (MoleProp.cellProduct N L γ δ P0 * 1)
      (MoleProp.cellProduct N L γ δ P0) 1 (by ring)
    have hAN : 0 ≤ L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * (M.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank := by
      have := hδ.1; positivity
    calc L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * (M.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
          MoleProp.cellProduct M L γ δ P
        ≤ L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * (M.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
          (MoleProp.cellProduct N L γ δ P0 * (Real.log L ^ 2) ^ 4) := mul_le_mul_of_nonneg_left hcellsM hAN
      _ = (L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * (M.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ M.circuitRank *
          (MoleProp.cellProduct N L γ δ P0 * 1)) * (Real.log L ^ 2) ^ 4 := by ring
      _ = _ := by rw [hsplit]; simp only [mul_one, Int.cast_natCast, zpow_natCast]; ring
  have hsup : MoleProp.countAFree N L γ δ C1 (0 : Mom (m + 2)) (fun κ' => lgAdm N L γ η P0 κ' ∧ mergeAdm M v₁ v₂ Adm κ') P0 ≤
      AFreeSupAdm N (m + 2) L γ δ C1 (fun P' κ' => lgAdm N L γ η P' κ' ∧ mergeAdm M v₁ v₂ Adm κ') :=
    le_iSup₂_of_le (f := fun P'' (_ : ∀ S ∈ MoleProp.ladderCells N, 0 ≤ P'' S) =>
      MoleProp.countAFree N L γ δ C1 (0 : Mom (m + 2)) (fun κ' => lgAdm N L γ η P'' κ' ∧ mergeAdm M v₁ v₂ Adm κ') P'')
      P0 hP0nn le_rfl
  have hreal : (2 * (fam.card : ℝ)) * ((⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ) : ℝ) *
      (L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 * (Real.log L ^ 2) ^ 4) ≤
      50 * (Cp * δ⁻¹ + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 10 * L ^ (-(η / 2)) := by
    have hcard : (fam.card : ℝ) ≤ 25 * Real.log L ^ 2 := by
      have h1 : ((scaleSet L).card : ℝ) ≤ 5 * Real.log L := card_scaleSet_le_log hlog
      have h2 : (fam.card : ℝ) ≤ ((scaleSet L).card : ℝ) ^ 2 := by exact_mod_cast hfamcard
      nlinarith [Nat.cast_nonneg (α := ℝ) (scaleSet L).card]
    have hexp : 0 ≤ ((m + 2 : ℕ) : ℝ) - γ - η / 2 := by
      have : (3 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast hd
      linarith [hγ.2, min_le_right γ (1 - γ), min_le_left γ (1 - γ)]
    have hc := ceil_mul_le (c := Cp * δ⁻¹) (L := L) (by have := hδ.1; positivity) hL1 hexp
    have hpow : L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) * L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) = L ^ (-(η / 2)) := by
      rw [← Real.rpow_add hLp]; congr 1; push_cast; ring
    have hb0 : 0 ≤ (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 := by have := hδ.1; positivity
    have hCn : 0 ≤ Cp * δ⁻¹ + 1 := by have := hδ.1; positivity
    calc (2 * (fam.card : ℝ)) * ((⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ) : ℝ) *
          (L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 * (Real.log L ^ 2) ^ 4)
        ≤ (2 * (25 * Real.log L ^ 2)) * ((Cp * δ⁻¹ + 1) * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)) *
          (L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 * (Real.log L ^ 2) ^ 4) := by
          have hA0 : 0 ≤ L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 * (Real.log L ^ 2) ^ 4 := by
            have := Real.rpow_nonneg hLp.le (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)); positivity
          refine mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) hc (Nat.cast_nonneg _) (by positivity)) hA0
      _ = 50 * (Cp * δ⁻¹ + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 10 *
          (L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) * L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ))) := by ring
      _ = _ := by rw [hpow]
  calc (MoleProp.countEFree M L γ δ (0 : Mom (m + 2)) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := m + 2) L γ δ C1 P)
      ≤ (((2 * fam.card : ℕ∞) * Φ * G P0 : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal ((L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) *
        (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 * (Real.log L ^ 2) ^ 4) * MoleProp.freeNormalization N (d := m + 2) L γ δ C1 P0) :=
        mul_le_mul' (ENat.toENNReal_mono hE) (ENNReal.ofReal_le_ofReal hnorm)
    _ = ENNReal.ofReal ((2 * (fam.card : ℝ)) * ((⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ) : ℝ) *
          (L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 * (Real.log L ^ 2) ^ 4)) *
        MoleProp.countAFree N L γ δ C1 (0 : Mom (m + 2)) (fun κ' => lgAdm N L γ η P0 κ' ∧ mergeAdm M v₁ v₂ Adm κ') P0 := by
        rw [MoleProp.countAFree_eq_normalization]
        have hA0 : 0 ≤ L ^ (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ 1 * (Real.log L ^ 2) ^ 4 := by
          have := Real.rpow_nonneg hLp.le (-(((m + 2 : ℕ) : ℝ) - γ) * ((1 : ℕ) : ℝ))
          have := hδ.1
          positivity
        have e1 : ((2 * fam.card : ℕ∞) : ℝ≥0∞) = 2 * (fam.card : ℝ≥0∞) := by
          rw [ENat.toENNReal_mul]; simp
        have e2 : ((Φ : ℕ∞) : ℝ≥0∞) = ((⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ) : ℝ≥0∞) := by
          rw [hΦ]; simp
        have hT : ENNReal.ofReal (2 * (fam.card : ℝ) * ((⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ) : ℝ)) =
            2 * (fam.card : ℝ≥0∞) * ((⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast,
            ENNReal.ofReal_natCast]
          simp
        have hX : (((2 * fam.card : ℕ∞) * Φ * G P0 : ℕ∞) : ℝ≥0∞) =
            2 * (fam.card : ℝ≥0∞) * ((⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ) : ℝ≥0∞) * ((G P0 : ℕ∞) : ℝ≥0∞) := by
          rw [ENat.toENNReal_mul, ENat.toENNReal_mul, e1, e2]
        rw [hX, ENNReal.ofReal_mul hA0, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 * (fam.card : ℝ) *
          ((⌈Cp * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2)⌉₊ : ℕ) : ℝ)), hT]
        simp only [hG]
        ring
    _ ≤ ENNReal.ofReal (50 * (Cp * δ⁻¹ + 1) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 10 * L ^ (-(η / 2))) *
          AFreeSupAdm N (m + 2) L γ δ C1 (fun P' κ' => lgAdm N L γ η P' κ' ∧ mergeAdm M v₁ v₂ Adm κ') :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) hsup
    _ = _ := by
        rw [hl10]

/-- **`MergeInput`** (DH23 L1977), for `γ > 1/2`, `0 < η ≤ min γ (1-γ)/2`. -/
theorem mergeInput {d : ℕ} (hd : 3 ≤ d) (γ η : ℝ) (hγ1 : γ < 1) : MergeInput.{u, v} d γ η :=
  fun hγ12 hη hηmax => ⟨1, le_rfl, fun C1 hC1 δ hδ => mergeAt.{u, v} hd ⟨hγ12, hγ1⟩ hη hηmax hδ (by linarith)⟩

end WaveTurbulence.FinalCountG8
