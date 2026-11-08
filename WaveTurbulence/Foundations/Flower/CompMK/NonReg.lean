/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Sum
public import WaveTurbulence.Foundations.Flower.CompMK.Card
public import WaveTurbulence.Foundations.Flower.CompMK.Restrict
public import WaveTurbulence.Foundations.Flower.CompMK.Numerics
public import WaveTurbulence.Foundations.Spine.StageOrderGrowth

/-! # C5b COMP-MK: the non-regular component bound at fixed parameters

`nonreg_at`: main's chain `stage1_type_bound → stage1_core_bound(_int) → stage1_sum_bound_int` for capped components:
1. B4's gate (`Stage1ReductionAtMKSel`, at `base = 0`) gives the pieces; `sum_compValue_eq_sum_pieces` identifies the
   component sum with the sum of the piece values (summability: `summable_kgTerm_capWt_gen`);
2. the pieces of nonzero value are grouped by their residual selected trees `V ⊆ T = {kSel ≠ none}`
   (`sum_eq_sum_powerset`, at most `2^{#T}` groups);
3. each group is a Stage-1′ family to which D7's class sum `MarkedSumBoundSelAtT` applies, with uniform mass
   `selMass N b Rs kSel V`, uniform extra `X = 25R·(cP d + 840d + 40)` (`card_protI_le`, `markedExtra_le`) and the
   inherited class counts (`stage1Counts_restrict`);
4. `selMass_mul_prod`, `bracket_le` and `budget_le` turn the group bound into the target right side. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

namespace WaveTurbulence.Flower.CompMK

/-- **The non-regular part of `MarkedComponentBoundAtI` at fixed parameters**, from B4's gate and D7's class sum
at `P`, under the numerical conditions that the prefix provides. -/
theorem nonreg_at {C₀ : ℕ} {cP cθ B : ℝ} (hcP : 0 ≤ cP) (hcθ : 1 ≤ cθ) {Pm : ℕ} {P : WTParams}
    (hd : 1 ≤ P.d) (hs : PieceSmall P) (habs : FinalAbsorptionAt (6 * C₀) P) (hlog : 1 ≤ Real.log P.L)
    (hθδ : cθ ^ (40 * P.ν) * P.δ ^ P.ν ≤ 1)
    (hNL : ∀ p, p < P.D → ((P.N (p + 1) ^ 4 : ℕ) : ℝ) + 1 ≤ P.L)
    (hRP : ∀ p, p < P.D → 2 * Pm ≤ 10 * P.R (p + 1))
    (hbud : 25 * (cP * P.d + 840 * P.d + 40) + 800 * P.d + 2 ≤ 2 * B * P.d)
    (hB4 : Stage1ReductionAtMKSel C₀ cP cθ P) (hD7 : ∀ X : ℝ, MarkedSumBoundSelAtT cP cθ X P) :
    NonregComponentBoundAtI B Pm P := by
  intro _hγ p hp R hR1 hR2 n hn1 hn2 t ht s hs' J roots hJ pat kSel A hA hplain hTC h b hb hh Rf σ Rs dag hRf hRs
    hhigh
  have hL0 : 0 < P.L := by linarith [hs.L_ge]
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hδ0 := hs.delta_pos
  have hRmax : R ≤ 10 * P.R (p + 1) := by have := hRP p hp; omega
  obtain ⟨S, Cl, hCl, cls, members, sel, selR, hpart, hpc, hsound, hord, hcnt⟩ :=
    hB4 p hp R hR1 hRmax n hn1 hn2 J hJ pat kSel t ht s hs' A
      (fun LG hLG => ⟨(hA LG hLG).1, (hA LG hLG).2.2.2.2.2, (hA LG hLG).2.1, (hA LG hLG).2.2.1,
        (hA LG hLG).2.2.2.1, (hA LG hLG).2.2.2.2.1⟩) hplain hTC roots h b Rf σ Rs dag hb hh hRf hRs hhigh
  letI := S.fin
  letI := hCl
  -- 1. the component sum is the sum of the piece values
  have hsum : ∑ LG ∈ A, compValue P LG (fixCap LG J pat t s) (offCap LG J dag.isSome)
        (fun k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k) t roots =
      ∑ π, S.val π :=
    sum_compValue_eq_sum_pieces P roots A members cls sel hpart t (fun LG => fixCap LG J pat t s)
      (fun LG => offCap LG J dag.isSome)
      (fun LG k => selOK LG J kSel * markedWeight LG J p P.L Rf σ (selCap LG J kSel) Rs h dag k) S.val
      (fun π => (hpc π).1)
      (fun LG hLG => summable_kgTerm_capWt_gen P hL0 LG (hA LG hLG).1.1.1 (layer_le_of_mkCarries (hA LG hLG).1) J
        (hA LG hLG).2.2.1 roots _ _ _ kSel Rf σ Rs h dag b hb hh)
  rw [hsum]
  -- 2. grouping by residual selected trees
  set T : Finset (Fin (2 * R)) := univ.filter fun j => (kSel j).isSome with hT
  have hUT : ∀ π, ((selR π).image fun v => v.1.1) ⊆ T := by
    intro π j hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hj
    exact Finset.mem_filter.2 ⟨mem_univ _, ((hpc π).2.2.2.1 v hv).1⟩
  rw [sum_eq_sum_powerset S.val (fun π => (selR π).image fun v => v.1.1) T (fun π _ => hUT π)]
  -- the common bound of a group
  set Qp0 : ℝ := ∏ j : Fin (2 * R), (if (kSel j).isSome then (Rs j)⁻¹ * (Rs j) ^ (-(1 / 18 : ℝ)) else 1) with hQp0
  have hRs0 : ∀ j, 0 < Rs j := fun j => lt_of_lt_of_le hL0 (hRs j)
  have hQp0nn : 0 ≤ Qp0 := Finset.prod_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (inv_nonneg.2 (hRs0 j).le) (Real.rpow_nonneg (hRs0 j).le _)
    · exact zero_le_one
  set X : ℝ := ((25 * R : ℕ) : ℝ) * (cP * P.d + 840 * P.d + 40) with hX
  set Gb : ℝ := b ^ n * Qp0 * (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ))) * P.δ ^ (7 * P.ν * n) with hGb
  have hb0 : 0 ≤ b ^ n := pow_nonneg (by linarith) _
  have hGb0 : 0 ≤ Gb := by rw [hGb]; positivity
  have hgroup : ∀ V ∈ T.powerset,
      ‖∑ π ∈ univ.filter (fun π => S.val π ≠ 0 ∧ ((selR π).image fun v => v.1.1) = V), S.val π‖ ≤ Gb := by
    intro V hV
    have hVT : V ⊆ T := Finset.mem_powerset.1 hV
    set q : S.Pc → Prop := fun π => S.val π ≠ 0 ∧ ((selR π).image fun v => v.1.1) = V with hq
    have hres := sum_restrictData S q
    by_cases hne : ∃ π, q π
    swap
    · push_neg at hne
      have : univ.filter q = ∅ := Finset.filter_eq_empty_iff.2 fun π _ => hne π
      change ‖∑ π ∈ univ.filter q, S.val π‖ ≤ Gb
      rw [this, Finset.sum_empty, norm_zero]
      exact hGb0
    obtain ⟨π₀, hπ₀⟩ := hne
    -- `R ≤ 2n` and `n ≤ (log L)^K`: the absorption conditions
    have hR2n : R ≤ 2 * n := by
      have h1 := (hsound π₀).bond_count
      have h2 := hord π₀
      omega
    have hnlog : (n : ℝ) ≤ Real.log P.L ^ (4 * (40 * P.d) ^ (2 * P.D + 2)) := by
      have h1 : (n : ℝ) ≤ (P.N (p + 1) : ℝ) ^ 4 := by exact_mod_cast hn2
      exact h1.trans (N_quartic_le_log_pow P hd hlog (p + 1))
    obtain ⟨hT2, hS2, hLabs⟩ := habs.2 n R hR1 hR2n hnlog
    have hnL : (n : ℝ) + 1 ≤ P.L := by
      have h1 : (n : ℝ) ≤ ((P.N (p + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hn2
      linarith [hNL p hp]
    -- the uniform extra
    have hXπ : ∀ π, markedExtra cP (S.piece π) ≤ X := by
      intro π
      obtain ⟨LG, hLG, hle⟩ := (hpc π).2.2.1
      have hLGA : LG ∈ A := (hpart.1 LG).2 ⟨cls π, hLG⟩
      have hc := card_protI_le LG J hJ (hA LG hLGA).2.2.1 pat t s kSel
      exact markedExtra_le hcP (S.piece π) (hsound π).toSoundMK (le_trans hle hc)
    have hspos : 0 < selMass n b Rs kSel V := by
      unfold selMass
      refine mul_pos (pow_pos (by linarith) _) (Finset.prod_pos fun j _ => ?_)
      split_ifs <;> first
        | exact one_pos
        | exact mul_pos (inv_pos.2 (hRs0 j)) one_pos
        | exact mul_pos (inv_pos.2 (hRs0 j)) (Real.rpow_pos_of_pos (hRs0 j) _)
    have hD := hD7 X (p := p) (R := R) (n := n) hp hR1 hRmax (restrictData S q) (fun π => selR π.1) V Rs
      (fun _ => t) 0 roots C₀ Cl hCl (fun π => cls π.1) (selMass n b Rs kSel V) hspos
      (fun j _ => hRs j) (fun π => π.2.2) (fun π v hv => ((hpc π.1).2.2.2.1 v hv).2)
      (fun π => (hpc π.1).2.2.2.2.1) (fun π => (hpc π.1).2.2.2.2.2) (fun π => hsound π.1) (fun π => hord π.1) hnL
      (fun π => by
        have h := (hpc π.1).2.1
        rw [π.2.2] at h
        exact h)
      (fun π => hXπ π.1) (stage1Counts_restrict S q hCl cls hcnt) hT2 hS2
    rw [hres] at hD
    have hfeq : (univ.filter fun π => S.val π ≠ 0 ∧ ((selR π).image fun v => v.1.1) = V) =
        @Finset.filter _ q (Classical.decPred q) univ :=
      Finset.ext fun π => by simp only [Finset.mem_filter]; rfl
    rw [hfeq]
    refine hD.trans ?_
    -- the group bound is the common bound
    have hVsel : ∀ j ∈ V, (kSel j).isSome := fun j hj => (Finset.mem_filter.1 (hVT hj)).2
    have hmass := selMass_mul_prod n b Rs kSel V hVsel
    have hbr := bracket_le hs (cθ := cθ) (by linarith) hR1 habs.1 hθδ hLabs
    have hCV : P.L ^ (400 * (P.d : ℝ) * (V.card : ℝ)) ≤ P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      have : (V.card : ℝ) ≤ T.card := by exact_mod_cast Finset.card_le_card hVT
      have hd0 : (0 : ℝ) ≤ P.d := Nat.cast_nonneg _
      nlinarith
    set Br : ℝ := 4 * (P.C₂ * (cθ ^ (40 * P.ν) * P.C₁ ^ 6 * P.δ ^ (10 * P.ν)) ^ n *
        P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 60)) * ((6 * C₀ : ℕ) : ℝ) ^ n *
        ((((6 * C₀) * R).factorial : ℕ) : ℝ) *
        ((((6 * C₀) * n : ℕ) : ℝ) ^ (6 * C₀) * P.C₂ * P.L ^ (-P.η ^ 6 / 4))) with hBr
    have hBr0 : 0 ≤ Br := by
      have hC₂ : 0 ≤ P.C₂ := by linarith [hs.c1_ge, hs.c1_le_c2]
      have hC₁ : 0 ≤ P.C₁ := by linarith [hs.c1_ge]
      rw [hBr]; positivity
    have hLX : 0 ≤ P.L ^ X := Real.rpow_nonneg hL0.le _
    calc selMass n b Rs kSel V * P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (V.card : ℝ)) *
          (∏ j ∈ V, Rs j ^ (-(1 / 18 : ℝ))) * Br
        = (selMass n b Rs kSel V * ∏ j ∈ V, Rs j ^ (-(1 / 18 : ℝ))) *
            (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (V.card : ℝ))) * Br := by ring
      _ = b ^ n * Qp0 * (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (V.card : ℝ))) * Br := by rw [hmass]
      _ ≤ b ^ n * Qp0 * (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ))) * P.δ ^ (7 * P.ν * n) := by
          apply mul_le_mul _ hbr hBr0 (by positivity)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCV hLX) (mul_nonneg hb0 hQp0nn)
  -- 3. sum over the groups and the budget
  have hTc : T.card ≤ 2 * R := by
    calc T.card ≤ (univ : Finset (Fin (2 * R))).card := Finset.card_le_univ _
      _ = 2 * R := by simp
  have hsumV := norm_sum_le_of_le T.powerset hgroup
  rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul] at hsumV
  refine hsumV.trans ?_
  have hbudL := budget_le hs.L_ge (cP := cP) (B := B) (R := R) hTc hcP hbud
  have hδ7 : 0 ≤ P.δ ^ (7 * P.ν * n) := Real.rpow_nonneg hδ0.le _
  calc ((2 ^ T.card : ℕ) : ℝ) * Gb
      = ((2 : ℝ) ^ T.card * (P.L ^ X * P.L ^ (400 * (P.d : ℝ) * (T.card : ℝ)))) *
          (P.δ ^ (7 * P.ν * n) * b ^ n * Qp0) := by rw [hGb]; push_cast; ring
    _ ≤ P.L ^ (B * P.d * ((2 * R : ℕ) : ℝ)) * (P.δ ^ (7 * P.ν * n) * b ^ n * Qp0) :=
        mul_le_mul_of_nonneg_right hbudL (by positivity)
    _ = _ := by rw [hQp0]; ring

end WaveTurbulence.Flower.CompMK
