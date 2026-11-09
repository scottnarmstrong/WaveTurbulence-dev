/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone7
/-! **L6E GHOST, part 18: `triangle_excess_cone`** — M1-R2 Theorem 6.1 (e) at an Op-2 creation step.

A triangle step creating `α`-atoms is the creation step `s(P)` of `k ∈ {1, 2}` NC critical pairs when the created atoms
carry the cone hypothesis of the (f′) class NC (`CreationCone`): one created atom (`κ = 0`, critical label) whose gap is
in the cone around a centre fixed in the parameter class (Lemma 6.2(iii): a present atom's parameter), or both created
atoms of one pair with the relative cone (`gap₁` around `gap₀`), or (`k = 2`) both created atoms, each with its own cone.
Then the charged bound of the step holds with the extra factor `L^{-5ηk}` (the cone gains `L^{-12η}` per cone,
Lemma 5.2; transfer `τ₀ = 5η`).

**Export.** `Tri.triangle_excess_cone`: `IsDeviation … (ofReal (triRHSCone … k))` with
`triRHSCone = 9·25^d · L^{-5ηk} · triRHS0` (`triRHS0` the right-hand side of `triangle_excess_ghost_low` at `ν = 0`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCount.TriData

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- A **critical label** (M1-R2 §6): `R ≥ L^{-γ₀-4η}`. -/
def Crit (L γ η R : ℝ) : Prop := L ^ (-(min γ (1 - γ)) - 4 * η) ≤ R

/-- The cone factor `3·5^{d-1} θ₀^{d-1}`, `θ₀ = L^{-6η}`. -/
noncomputable def coneX (d : ℕ) (L η : ℝ) : ℝ := 3 * 5 ^ (d - 1) * (L ^ (-6 * η)) ^ (d - 1)

/-- **The cone data of a creation step** (the (f′) class NC at `s(P)`, `k` pairs). -/
def CreationCone {M : Molecule V D} (T : TriData M) (L γ δ η : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (k : ℕ) : Prop :=
  (k = 1 ∧ ((T.IsA0 ∧ κ₀ = 0 ∧ Crit L γ η R₀ ∧ ConeAt T L γ δ η w Adm 0) ∨
      (T.IsA1 ∧ κ₁ = 0 ∧ Crit L γ η R₁ ∧ ConeAt T L γ δ η w Adm 1) ∨
      (T.IsA0 ∧ T.IsA1 ∧ κ₁ = 0 ∧ Crit L γ η R₁ ∧ ConeRel T L η w Adm))) ∨
  (k = 2 ∧ T.IsA0 ∧ T.IsA1 ∧ κ₀ = 0 ∧ κ₁ = 0 ∧ Crit L γ η R₀ ∧ Crit L γ η R₁ ∧
      ConeAt T L γ δ η w Adm 0 ∧ ConeAt T L γ δ η w Adm 1)

/-- The right-hand side of a creation step with `k` cones. -/
noncomputable def triRHSCone {M : Molecule V D} (T : TriData M) (d c : ℕ) (L γ η δ : ℝ) (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ)
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (k : ℕ) : ℝ :=
  9 * 25 ^ d * L ^ (-5 * η * (k : ℝ)) * triRHS0 T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg

theorem coneX_nonneg (d : ℕ) {L η : ℝ} (hL : 0 < L) : 0 ≤ coneX d L η := by
  unfold coneX; have := Real.rpow_nonneg hL.le (-6 * η); positivity

theorem coneX_le (d : ℕ) {L η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η) (hd : 3 ≤ d) :
    coneX d L η ≤ 3 * 5 ^ d * L ^ (-12 * η) := by
  unfold coneX
  have h5 : (5 : ℝ) ^ (d - 1) ≤ 5 ^ d := pow_le_pow_right₀ (by norm_num) (by omega)
  have h := coneFactor_le hL hη hd
  have hL0 : 0 < L := by linarith
  have h0 : 0 ≤ (L ^ (-6 * η)) ^ (d - 1) := by have := Real.rpow_nonneg hL0.le (-6 * η); positivity
  calc 3 * 5 ^ (d - 1) * (L ^ (-6 * η)) ^ (d - 1) ≤ 3 * 5 ^ d * (L ^ (-6 * η)) ^ (d - 1) := by gcongr
    _ ≤ 3 * 5 ^ d * L ^ (-12 * η) := by gcongr

theorem rpow_le_transfer {L η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η) (k : ℕ) (hk : k ≤ 2) :
    L ^ (-12 * η) ≤ L ^ (-5 * η * (k : ℝ)) :=
  Real.rpow_le_rpow_of_exponent_le hL (by
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    nlinarith)

/-- **The cone ratio**: the cone count of a critical gap ball is `≤ coneX` times main's ball count. -/
theorem cone_ratio {L γ η R : ℝ} (hL : 1 ≤ L) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hη1 : 200 * η ≤ γ)
    (hη2 : 200 * η ≤ 1 - γ) (hd : 1 ≤ d) (hRl : L⁻¹ ≤ R) (hcrit : Crit L γ η R) :
    (coneCount d L η R : ℝ) ≤ coneX d L η * ((⌊2 * (if (0 : ℕ) = 0 then 2 * R else L ^ (-50 * η) * R) * L⌋₊ + 1 : ℕ) : ℝ) ^ d := by
  have hL0 : 0 < L := by linarith
  simp only [↓reduceIte]
  have hRL : 1 ≤ 2 * R * L := by
    have := mul_le_mul_of_nonneg_right hRl hL0.le
    rw [inv_mul_cancel₀ hL0.ne'] at this; linarith
  have hθ := theta_rho_ge_one hL hγ0 hγ1 hη hη1 hη2 hcrit
  have h := coneSet_ratio (d := d) L (2 * R) (L ^ (-6 * η)) hRL hθ (Real.rpow_nonneg hL0.le _) hd
  unfold coneCount coneX
  exact h

namespace Tri
variable {M : Molecule V D} (T : TriData M)

/-- **The repaired charged bound at an Op-2 creation step with `k` cones** (M1-R2 Theorem 6.1 (e)). -/
theorem triangle_excess_cone {L γ η δ C₁ : ℝ} (H : TriReal d L γ η δ C₁)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (PDart T.m3 T.TP → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x => κ x.1))
    (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S)
    (hP1 : ∀ S' ∈ T.m1.maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (hP2 : ∀ S' ∈ T.m2.maximalLadders, ∀ S ∈ T.m1.maximalLadders, S' ⊆ S → P S' = P S)
    (hP3 : ∀ S' ∈ T.m3.maximalLadders, ∀ S ∈ T.m2.maximalLadders, S' ⊆ S → P S' = P S)
    (hnz : ∀ κ, Adm κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0)
    (R₀ R₁ : ℝ) (κ₀ κ₁ : ℕ) (hκ₀ : κ₀ = 0 ∨ κ₀ = 50) (hκ₁ : κ₁ = 0 ∨ κ₁ = 50)
    (hR₀l : L⁻¹ ≤ R₀) (hR₀u : R₀ ≤ L ^ (-γ + η)) (hR₁l : L⁻¹ ≤ R₁) (hR₁u : R₁ ≤ L ^ (-γ + η))
    (hgap0 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0)‖ ≤ 2 * R₀)
    (hball0 : κ₀ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 0) (T.b 0) - r₀‖ ≤ L ^ (-50 * η) * R₀)
    (hgap1 : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1)‖ ≤ 2 * R₁)
    (hb1 : κ₁ = 50 → (∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' (T.a 1) (T.b 1) - r₀‖ ≤ L ^ (-50 * η) * R₁) ∨
      T.SiblingReading L w Adm (L ^ (-50 * η) * R₁))
    (gh ag : Fin 3 → Prop) [DecidablePred gh] [DecidablePred ag] (hag : ∀ j, ag j → gh j)
    (hgd : ∀ j, gh j → M.deg (T.t j) ≤ 2)
    (Qg : Fin 3 → ℝ) (kg : Fin 3 → ℕ) (hQl : ∀ j, ag j → L⁻¹ ≤ Qg j) (hQu : ∀ j, ag j → Qg j ≤ L ^ (-γ + η))
    (hlow : ∀ j, ag j → ∀ κ', Adm κ' → Qg j / 2 ≤ ‖Molecule.gapAt L w κ' (T.a j) (T.b j)‖)
    (k : ℕ) (hcone : CreationCone T L γ δ η w Adm R₀ R₁ κ₀ κ₁ k) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
      (ENNReal.ofReal (triRHSCone T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg k)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans H.hL
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hR₀ : 0 ≤ R₀ := (inv_pos.2 hL0).le.trans hR₀l
  have hR₁ : 0 ≤ R₁ := (inv_pos.2 hL0).le.trans hR₁l
  have hX0 := coneX_nonneg d (η := η) hL0
  have hT0 := triRHS0_nonneg T (d := d) (γ := γ) hL0 H.hη H.hδ0 c R₀ R₁ κ₀ κ₁ hR₀ hR₁ gh ag Qg kg
    (fun j h => lt_of_lt_of_le (inv_pos.2 hL0) (hQl j h))
  have hk2 : k ≤ 2 := by rcases hcone with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have hk1 : 1 ≤ k := by rcases hcone with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  -- the final comparison of factors
  have hfin : ∀ X : ℝ, X ≤ 9 * 25 ^ d * L ^ (-5 * η * (k : ℝ)) →
      IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
        (ENNReal.ofReal (X * triRHS0 T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg)) →
      IsDeviation (M.countA L γ δ C₁ w Adm P) (T.kept.countA L γ δ C₁ w Adm' P)
        (ENNReal.ofReal (triRHSCone T d c L γ η δ R₀ R₁ κ₀ κ₁ gh ag Qg kg k)) := by
    intro X hX dev
    refine isDeviation_mono dev (ENNReal.ofReal_le_ofReal ?_)
    unfold triRHSCone
    exact mul_le_mul_of_nonneg_right hX hT0
  have hX1 : coneX d L η ≤ 9 * 25 ^ d * L ^ (-5 * η * (k : ℝ)) := by
    have h1 := coneX_le d hL1 H.hη.le H.hd
    have h2 := rpow_le_transfer hL1 H.hη.le k hk2
    have h3 : (3 : ℝ) * 5 ^ d ≤ 9 * 25 ^ d := by
      have : (5 : ℝ) ^ d ≤ 25 ^ d := pow_le_pow_left₀ (by norm_num) (by norm_num) d
      nlinarith [pow_pos (show (0 : ℝ) < 5 by norm_num) d]
    calc coneX d L η ≤ 3 * 5 ^ d * L ^ (-12 * η) := h1
      _ ≤ 9 * 25 ^ d * L ^ (-5 * η * (k : ℝ)) := by
          gcongr
  -- providers
  have Pb0 := gapProv_ball T (γ := γ) (η := η) (δ := δ) hL0 w Adm 0 R₀ κ₀ hκ₀ hgap0 hball0
  have hr0 : ((⌊2 * (if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀) * L⌋₊ + 1) ^ d : ℕ) =
      ((⌊2 * (if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀) * L⌋₊ + 1) ^ d : ℕ) := rfl
  rcases hcone with ⟨hk, hc⟩ | ⟨hk, hα0, hα1, h0, h1, hc0, hc1, hC0, hC1⟩
  · rcases hc with ⟨hα0, h0, hcr, hC⟩ | ⟨hα1, h1, hcr, hC⟩ | ⟨hα0, hα1, h1, hcr, hrel⟩
    · -- cone at the new atom `f0`
      have Pc := gapProv_cone T hL0 H.hη w Adm 0 R₀ hR₀ hgap0 hC
      have hrat := cone_ratio (d := d) hL1 H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 hd1 hR₀l hcr
      subst h0
      refine hfin _ hX1 ?_
      by_cases hα1 : T.IsA1
      · -- `α α`: the second gap by its ball or by the sibling reading
        by_cases h50 : κ₁ = 50
        · rcases hb1 h50 with hball1 | hsib
          · have Pb1 := gapProv_ball T (γ := γ) (η := η) (δ := δ) hL0 w Adm 1 R₁ κ₁ hκ₁ hgap1 (fun _ => hball1)
            refine cone_aa T H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ 0 κ₁ (Or.inl rfl) hκ₁ hR₀l hR₀u hR₁l hR₁u
              gh ag hag hgd Qg kg _ (pairProv_prod T w Adm _ _ Pc Pb1) _ hX0 ?_ hα0 hα1
            push_cast
            have hb : (0 : ℝ) ≤ ((⌊2 * (if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁) * L⌋₊ : ℝ) + 1) ^ d := by
              positivity
            push_cast at hrat
            nlinarith [mul_le_mul_of_nonneg_right hrat hb]
          · obtain ⟨s, -, hs⟩ := hsib
            have hρ1 : 0 ≤ L ^ (-50 * η) * R₁ := mul_nonneg (Real.rpow_nonneg hL0.le _) hR₁
            refine cone_aa T H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ 0 κ₁ (Or.inl rfl) hκ₁ hR₀l hR₀u hR₁l hR₁u
              gh ag hag hgd Qg kg _ (pairProv_sib T hL0 w Adm _ Pc _ hρ1 s hs) _ hX0 ?_ hα0 hα1
            rw [if_neg (by omega : κ₁ ≠ 0)]
            push_cast
            have hb : (0 : ℝ) ≤ ((⌊2 * (L ^ (-50 * η) * R₁) * L⌋₊ : ℝ) + 1) ^ d := by positivity
            push_cast at hrat
            nlinarith [mul_le_mul_of_nonneg_right hrat hb]
        · have Pb1 := gapProv_ball T (γ := γ) (η := η) (δ := δ) hL0 w Adm 1 R₁ κ₁ hκ₁ hgap1
            (fun h => absurd h h50)
          refine cone_aa T H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ 0 κ₁ (Or.inl rfl) hκ₁ hR₀l hR₀u hR₁l hR₁u
            gh ag hag hgd Qg kg _ (pairProv_prod T w Adm _ _ Pc Pb1) _ hX0 ?_ hα0 hα1
          push_cast
          have hb : (0 : ℝ) ≤ ((⌊2 * (if κ₁ = 0 then 2 * R₁ else L ^ (-50 * η) * R₁) * L⌋₊ : ℝ) + 1) ^ d := by
            positivity
          push_cast at hrat
          nlinarith [mul_le_mul_of_nonneg_right hrat hb]
      · exact cone_ab T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ R₁ 0 κ₁ (Or.inl rfl) hR₀l hR₀u hR₁
          gh ag hag hgd Qg kg hQl hQu hlow _ Pc _ hX0 hrat hα0 hα1
    · -- cone at the new atom `f1`
      have Pc := gapProv_cone T hL0 H.hη w Adm 1 R₁ hR₁ hgap1 hC
      have hrat := cone_ratio (d := d) hL1 H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 hd1 hR₁l hcr
      subst h1
      refine hfin _ hX1 ?_
      by_cases hα0 : T.IsA0
      · refine cone_aa T H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ 0 hκ₀ (Or.inl rfl) hR₀l hR₀u hR₁l hR₁u
          gh ag hag hgd Qg kg _ (pairProv_prod T w Adm _ _ Pb0 Pc) _ hX0 ?_ hα0 hα1
        push_cast
        have hb : (0 : ℝ) ≤ ((⌊2 * (if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀) * L⌋₊ : ℝ) + 1) ^ d := by
          positivity
        push_cast at hrat
        nlinarith [mul_le_mul_of_nonneg_left hrat hb]
      · exact cone_ba T H hM c hn w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 hnz R₀ R₁ κ₀ 0 (Or.inl rfl) hR₁l hR₁u hR₀
          gh ag hag hgd Qg kg hQl hQu hlow _ Pc _ hX0 hrat hα0 hα1
    · -- both new, relative cone
      have hrat := cone_ratio (d := d) hL1 H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 hd1 hR₁l hcr
      subst h1
      refine hfin _ hX1 ?_
      refine cone_aa T H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ κ₀ 0 hκ₀ (Or.inl rfl) hR₀l hR₀u hR₁l hR₁u
        gh ag hag hgd Qg kg _ (pairProv_rel T hL0 H.hη w Adm _ Pb0 R₁ hR₁ (fun κ hκ => hnz κ hκ 0) hgap1 hrel)
        _ hX0 ?_ hα0 hα1
      push_cast
      have hb : (0 : ℝ) ≤ ((⌊2 * (if κ₀ = 0 then 2 * R₀ else L ^ (-50 * η) * R₀) * L⌋₊ : ℝ) + 1) ^ d := by
        positivity
      push_cast at hrat
      nlinarith [mul_le_mul_of_nonneg_left hrat hb]
  · -- two cones
    subst h0; subst h1
    have Pc0 := gapProv_cone T hL0 H.hη w Adm 0 R₀ hR₀ hgap0 hC0
    have Pc1 := gapProv_cone T hL0 H.hη w Adm 1 R₁ hR₁ hgap1 hC1
    have hrat0 := cone_ratio (d := d) hL1 H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 hd1 hR₀l hc0
    have hrat1 := cone_ratio (d := d) hL1 H.hγ0 H.hγ1 H.hη H.hη1 H.hη2 hd1 hR₁l hc1
    have hX2 : coneX d L η * coneX d L η ≤ 9 * 25 ^ d * L ^ (-5 * η * (k : ℝ)) := by
      have h1 := coneX_le d hL1 H.hη.le H.hd
      have hk' : (k : ℝ) = 2 := by rw [hk]; norm_num
      have h12 : 0 ≤ 3 * (5 : ℝ) ^ d * L ^ (-12 * η) := by positivity
      calc coneX d L η * coneX d L η ≤ (3 * 5 ^ d * L ^ (-12 * η)) * (3 * 5 ^ d * L ^ (-12 * η)) :=
            mul_le_mul h1 h1 hX0 h12
        _ = 9 * ((5 : ℝ) ^ d * 5 ^ d) * (L ^ (-12 * η) * L ^ (-12 * η)) := by ring
        _ = 9 * 25 ^ d * L ^ (-24 * η) := by
            have e1 : (5 : ℝ) ^ d * 5 ^ d = 25 ^ d := by rw [← mul_pow]; norm_num
            have e2 : L ^ (-12 * η) * L ^ (-12 * η) = L ^ (-24 * η) := by
              rw [← Real.rpow_add hL0]; congr 1; ring
            rw [e1, e2]
        _ ≤ 9 * 25 ^ d * L ^ (-5 * η * (k : ℝ)) := by
            rw [hk']
            exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [H.hη]))
              (by positivity)
    refine hfin _ hX2 ?_
    refine cone_aa T H hM c w Adm Adm' hAdm' P hP0 hP1 hP2 hP3 R₀ R₁ 0 0 (Or.inl rfl) (Or.inl rfl) hR₀l hR₀u hR₁l hR₁u
      gh ag hag hgd Qg kg _ (pairProv_prod T w Adm _ _ Pc0 Pc1) _ (mul_nonneg hX0 hX0) ?_ hα0 hα1
    simp only [↓reduceIte] at hrat0 hrat1 ⊢
    push_cast at hrat0 hrat1 ⊢
    have hb0 : (0 : ℝ) ≤ (coneCount d L η R₁ : ℝ) := Nat.cast_nonneg _
    have hB0 : (0 : ℝ) ≤ ((⌊2 * (2 * R₀) * L⌋₊ : ℝ) + 1) ^ d := by positivity
    nlinarith [mul_le_mul hrat0 hrat1 hb0 (mul_nonneg hX0 hB0)]

end Tri
end WaveTurbulence.GammaLow.FinalCount.Ghost
