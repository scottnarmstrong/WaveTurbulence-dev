/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeInput
import Mathlib.Tactic

/-! # The merge provider for every `γ ∈ (0, 1)` (packet L6-COUNT, item C; M2 Lemma 2.3(1), §5.3)

DH23 L1977, case (IV) of Prop 10.4(2)′: merging a double pair `v₁ = v₂` without small gap. The fibre of the
restriction to the merged molecule is the two-vector count of Lemma A.3(1) at `v₁`:
* same direction (`(+,+)`): `positive_atom_shell_threshold_bound` with `U = δ⁻¹ L^g`, `g = max(2−2γ, (4−2γ)/3)`. Its
  budget hypotheses (`1 ≤ τL²`, `τL² ≤ U`, `L²·τL² ≤ U³`, `τ = δ⁻¹L^{−2γ}`) hold for every `γ ∈ (0,1)`; at `γ ≤ 1/2`,
  `g = 2 − 2γ` and the bound is the volume count `δ⁻¹ L^{d−2γ}` of the thin shell (M2 Lemma 2.0(b), Lemma 2.3(1) first
  system). `g ≤ 2 − γ − η/2` needs only `η/2 ≤ γ`.
* opposite direction (`(+,−)`): `negative_atom_large_bound` with the LG gap at `v₁` (`η ≤ 1 − γ`), all γ.

So main's `pairSet_card_le` and `mergeAt` hold verbatim for `γ ∈ (0,1)`: their hypothesis `1/2 < γ` was used only
through `0 < γ` (M2 §5.3). The proofs below are main's, with `hγ : γ ∈ Ioo 0 1`.

* `pairSet_card_le_all`: main's `pairSet_card_le` for `γ ∈ (0,1)`.
* `mergeAt_all`: main's `mergeAt` for `γ ∈ (0,1)`; the provider of `MergeAt` at `γ ≤ 1/2`.

Copied from main `FinalCount/MergeFiberBound.lean`, `FinalCount/MergeInput.lean` (sha256 in COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Count
universe u v
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas WaveTurbulence.FinalCountG8

/-- **The two-vector count for the double bond of a merge, every `γ ∈ (0,1)`** (DH23 Lemma A.3(1); M2 Lemma 2.3(1)):
main's `pairSet_card_le` with `γ ∈ (0,1)`. -/
theorem pairSet_card_le_all (m : ℕ) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 < η) (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L ≥ (1 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ (a b : Mom (m + 2)) (nk : Fin (m + 2) → ℤ) (β : ℝ)
      (ε : ℤˣ), (ε = -1 → L ^ (-γ + η) ≤ ‖latticePoint L nk‖) →
      ((atomPairSet L a b nk β (δ⁻¹ * L ^ (-2 * γ)) ε).ncard : ℝ) ≤ C * δ⁻¹ * L ^(((m + 2 : ℕ) : ℝ) - γ - η / 2) := by
  refine ⟨max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)), by positivity, ?_⟩
  intro L hL δ hδ a b nk β ε hgap
  have hLp : 0 < L := by linarith
  have hδ0 := hδ.1
  have hδi : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ0).mpr hδ.2
  rcases Int.units_eq_one_or ε with rfl | rfl
  · -- same sign
    set g : ℝ := max (2 - 2 * γ) ((4 - 2 * γ) / 3) with hg
    set τ := δ⁻¹ * L ^ (-2 * γ) with hτ
    have hτL : τ * L ^ 2 = δ⁻¹ * L ^ (2 - 2 * γ) := by
      rw [hτ, mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hLp]; congr 2; push_cast; ring
    have h1 : 1 ≤ τ * L ^ 2 := by
      rw [hτL]
      have := Real.one_le_rpow hL (show 0 ≤ 2 - 2 * γ by linarith [hγ.2])
      nlinarith
    have hU1 : τ * L ^ 2 ≤ δ⁻¹ * L ^ g := by
      rw [hτL]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _)) (by positivity)
    have hU2 : L ^ 2 * (τ * L ^ 2) ≤ (δ⁻¹ * L ^ g) ^ 3 := by
      have e1 : L ^ 2 * (δ⁻¹ * L ^ (2 - 2 * γ)) = δ⁻¹ * L ^ (4 - 2 * γ) := by
        rw [mul_left_comm, ← Real.rpow_natCast L 2, ← Real.rpow_add hLp]; congr 2; push_cast; ring
      have e2 : (δ⁻¹ * L ^ g) ^ 3 = δ⁻¹ ^ 3 * L ^ (3 * g) := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ g) 3, ← Real.rpow_mul hLp.le]; congr 2; push_cast; ring
      rw [hτL, e1, e2]
      have h3 : 4 - 2 * γ ≤ 3 * g := by have := le_max_right (2 - 2 * γ) ((4 - 2 * γ) / 3); linarith
      have h4 : L ^ (4 - 2 * γ) ≤ L ^ (3 * g) := Real.rpow_le_rpow_of_exponent_le hL h3
      have h5 : δ⁻¹ ≤ δ⁻¹ ^ 3 := by nlinarith [pow_le_pow_right₀ hδi (show 1 ≤ 3 by norm_num)]
      exact mul_le_mul h5 h4 (by positivity) (by positivity)
    have hb := positive_atom_shell_threshold_bound (d := m) hLp (by positivity) h1 hU1 hU2 a b nk β
    refine hb.trans ?_
    have hgle : g ≤ 2 - γ - η / 2 := by
      rw [hg]; refine max_le ?_ ?_
      · nlinarith [hγ.1, min_le_left γ (1 - γ)]
      · nlinarith [hγ.2, min_le_right γ (1 - γ)]
    have hpow : L ^ ((m : ℝ) + g) ≤ L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) :=
      Real.rpow_le_rpow_of_exponent_le hL (by push_cast; linarith)
    have hLm : L ^ m * L ^ g = L ^ ((m : ℝ) + g) := by
      rw [Real.rpow_add hLp, Real.rpow_natCast]
    have h2L : (2 * L + 1) ^ m ≤ 3 ^ m * L ^ m := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have hK : 0 ≤ 6 * Real.pi + 1924002 := by positivity
    calc (2 * L + 1) ^ m * (6 * Real.pi + 1924002) * (δ⁻¹ * L ^ g)
        ≤ (3 ^ m * L ^ m) * (6 * Real.pi + 1924002) * (δ⁻¹ * L ^ g) := by gcongr
      _ = (3 ^ m * (6 * Real.pi + 1924002)) * δ⁻¹ * L ^ ((m : ℝ) + g) := by rw [← hLm]; ring
      _ ≤ max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)) * δ⁻¹ *
          L ^ ((m : ℝ) + g) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
      _ ≤ max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)) * δ⁻¹ *
          L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) := mul_le_mul_of_nonneg_left hpow (by positivity)
  · have hgap' := hgap rfl
    have hη' : η ≤ 1 - γ := by linarith [min_le_right γ (1 - γ)]
    have hb := negative_atom_large_bound (d := m + 2) (by omega) hL hδ hη' a b nk β hgap'
    refine hb.trans ?_
    have hpow : L ^ (((m + 2 : ℕ) : ℝ) - γ - η) ≤ L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) :=
      Real.rpow_le_rpow_of_exponent_le hL (by linarith)
    have hc : 3 ^ (m + 2 - 1) * (((m + 2 : ℕ) : ℝ) + 1) = 3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1) := by
      rw [show m + 2 - 1 = m + 1 by omega]
    rw [hc]
    calc 3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1) * δ⁻¹ * L ^ (((m + 2 : ℕ) : ℝ) - γ - η)
        ≤ max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)) * δ⁻¹ *
          L ^ (((m + 2 : ℕ) : ℝ) - γ - η) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)) (by positivity)
      _ ≤ max (3 ^ m * (6 * Real.pi + 1924002)) (3 ^ (m + 1) * (((m + 2 : ℕ) : ℝ) + 1)) * δ⁻¹ *
          L ^ (((m + 2 : ℕ) : ℝ) - γ - η / 2) := mul_le_mul_of_nonneg_left hpow (by positivity)


/-- **`MergeAt` for every `γ ∈ (0,1)`** (DH23 L1977; M2 §5.3): main's `mergeAt` with `pairSet_card_le_all`. -/
theorem mergeAt_all {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) {δ : ℝ} (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) {C1 : ℝ} (hC1 : 0 < C1) :
    ∃ K B R : ℝ, ∀ L ≥ R, MergeAt.{u, v} d L γ δ η C1 K B := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  obtain ⟨Cp, hCp0, hCp⟩ := pairSet_card_le_all m γ η hγ hη hηmax
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


end WaveTurbulence.GammaLow.FinalCount.Count
