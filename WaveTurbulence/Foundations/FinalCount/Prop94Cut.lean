/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RealBounds3
/-! DH23 Prop 9.4 (L1784--L1802) for a single cut (FINALCOUNT-G2 steps 3--4): the `α`- and `β`-cut cases of
the first paragraph of the proof (L1789, `Steps 3--4`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCount
open WaveTurbulence

/-- **The right-hand side of (excesseqn2)** (DH23 L1785--L1786): `L^{-η³} · ∏^{(α)}_v L^{(γ+3η)/2-κ_vη} R_v ·
L^{(2γ₀+5η²)ΔF-(γ₀+2η²)ΔV_β}`, the product over the newly created α-atoms (labels `(R_v, κ_v)`),
`γ₀ = min(γ, 1-γ)`. -/
noncomputable def excessRHS (L γ η : ℝ) (αs : List (ℝ × ℕ)) (ΔF ΔVβ : ℤ) : ℝ :=
  L ^ (-η ^ 3) * (αs.map fun p => L ^ ((γ + 3 * η) / 2 - (p.2 : ℝ) * η) * p.1).prod *
    L ^ ((2 * min γ (1 - γ) + 5 * η ^ 2) * (ΔF : ℝ) - (min γ (1 - γ) + 2 * η ^ 2) * (ΔVβ : ℝ))

theorem isDeviation_mono {a b I I' : ℝ≥0∞} (h : IsDeviation a b I) (hI : I ≤ I') : IsDeviation a b I' :=
  h.trans (mul_le_mul_left hI b)

theorem excessRHS_alpha (L γ η R : ℝ) (κ : ℕ) :
    excessRHS L γ η [(R, κ), (R, κ)] 0 0 = L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - (κ : ℝ) * η) * R) ^ 2 := by
  unfold excessRHS
  simp [pow_two]

theorem excessRHS_beta (L γ η : ℝ) (hL : 0 < L) :
    excessRHS L γ η [] 1 2 = L ^ (-η ^ 3 + η ^ 2) := by
  unfold excessRHS
  simp only [List.map_nil, List.prod_nil, mul_one, Int.cast_one, Int.cast_ofNat]
  rw [← Real.rpow_add hL]; congr 1; ring

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- **DH23 Prop 9.4, `α`-cut case (L1789--L1792).** For an `α`-cut at `v` along `x₁, x₂` whose gap has size
`≤ 2R`, `R ∈ [L⁻¹, L^{-γ+η}]` (with `κ = 0`), or lies in a ball of radius `L^{-50η} R` determined by the
parameters (`κ = 50`, the case `ι_v ≠ 0`, L1801), the deviation is at most `C · L^{-η³} (L^{(γ+3η)/2-κη} R)²`,
the two new α-atoms both labelled `(R, κ)`; `C = 26 · 5^d ((8/η)⁴ + (8/(1-γ))⁴)`. -/
theorem alphaCut_excess (hd : 3 ≤ d) (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hα : M.IsAlphaCut v v₂ x₁ x₂)
    (L γ η δ C₁ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η) (hηγ : η ≤ γ) (hη1 : η ≤ (1 - γ) / 200)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (hRl : L⁻¹ ≤ R) (hRu : R ≤ L ^ (-γ + η)) (κ : ℕ) (hκ : κ = 0 ∨ κ = 50)
    (hgap : ∀ κ', Adm κ' → ‖Molecule.gapAt L w κ' x₁ x₂‖ ≤ 2 * R)
    (hball : κ = 50 → ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
      ∃ r₀ : Mom d, ∀ κ' ∈ decSet M L γ δ w Adm c β k0,
        ‖Molecule.gapAt L w κ' x₁ x₂ - r₀‖ ≤ L ^ (-50 * η) * R) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((M.cut v v₂ x₁ x₂).countA L γ δ C₁ w Adm P)
      (ENNReal.ofReal ((26 * 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4)) *
        excessRHS L γ η [(R, κ), (R, κ)] 0 0)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have hR0 : 0 ≤ R := (inv_nonneg.2 hL0.le).trans hRl
  have hη2 : η ≤ 1 / 2 := by linarith
  rw [excessRHS_alpha]
  have hNx : ∀ (n : ℕ) (x : ℝ), ((n : ℕ) : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal ((n : ℝ) * x) := by
    intro n x
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hg8 : 0 ≤ (8 / (1 - γ)) ^ 4 := by
    have : 0 < 1 - γ := by linarith
    positivity
  rcases hκ with rfl | rfl
  · have h := alphaCut_isDeviation M hcd hdeg hM hα L γ δ C₁ w Adm P hL hδ0 (by linarith) hP0 hPinh R (2 * R)
      hR0 (by linarith) hgap (fun c β k0 _ => ⟨0, fun κ' hκ' => by simpa using hgap κ' hκ'.2.2⟩)
    refine isDeviation_mono h ?_
    rw [hNx]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := alphaDev_kappa0 d (L := L) (γ := γ) (δ := δ) (C₁ := C₁) (R := R) hd hη hη2 hL hδ0 hδ1 hC hRl hRu hηγ
    refine hb.trans ?_
    have hnn : 0 ≤ L ^ (-η ^ 3) * (L ^ ((γ + 3 * η) / 2 - ((0 : ℕ) : ℝ) * η) * R) ^ 2 := by positivity
    have : (26 * 5 ^ d * (8 / η) ^ 4) ≤ 26 * 5 ^ d * ((8 / η) ^ 4 + (8 / (1 - γ)) ^ 4) := by
      have : 0 ≤ (26 : ℝ) * 5 ^ d := by positivity
      nlinarith
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    exact mul_le_mul_of_nonneg_right this (by simpa using hnn)
  · have hρ : 0 ≤ L ^ (-50 * η) * R := mul_nonneg (Real.rpow_nonneg hL0.le _) hR0
    have h := alphaCut_isDeviation M hcd hdeg hM hα L γ δ C₁ w Adm P hL hδ0 (by linarith) hP0 hPinh R
      (L ^ (-50 * η) * R) hR0 hρ hgap (hball rfl)
    refine isDeviation_mono h ?_
    rw [hNx]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb := alphaDev_kappa50 d (L := L) (γ := γ) (δ := δ) (C₁ := C₁) (R := R) hd hη hη2 hη1 hγ1 hL hδ0 hδ1 hC hRl hRu hηγ
    refine hb.trans (le_of_eq ?_)
    norm_num


/-- A power of the logarithm is dominated by any power of `L`. -/
theorem log_pow_le (m : ℕ) (hm : 0 < m) (L ε : ℝ) (hL : 1 ≤ L) (hε : 0 < ε) :
    Real.log L ^ m ≤ ((m : ℝ) / ε) ^ m * L ^ ε := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 : 0 ≤ Real.log L := Real.log_nonneg hL
  have h1 : Real.log L ≤ L ^ (ε / m) / (ε / m) :=
    Real.log_le_rpow_div (by linarith) (by positivity)
  have h2 : Real.log L ^ m ≤ (L ^ (ε / m) / (ε / m)) ^ m := pow_le_pow_left₀ h0 h1 m
  refine h2.trans (le_of_eq ?_)
  rw [div_pow, ← Real.rpow_natCast (L ^ (ε / m)) m, ← Real.rpow_mul (by linarith)]
  have : ε / m * (m : ℝ) = ε := by field_simp
  rw [this]
  have : (ε / m) ^ m = ((m : ℝ) / ε)⁻¹ ^ m := by rw [inv_div]
  rw [this, inv_pow]; field_simp

/-- **DH23 Prop 9.4, `β`-cut case (L1789).** For a `β`-cut (`ΔF = 1`, `ΔV_β = 2`, no new α-atoms) of a
molecule with `|𝕄| ≤ (log L)^c` atoms (`n_sub ≤ (log L)^C`, L1789), the deviation is at most
`C · L^{-η³} L^{(2γ₀+5η²) - 2(γ₀+2η²)} = C L^{η²-η³}`, with `C = 10 ((c+4)/(η²-η³))^{c+4}`. -/
theorem betaCut_excess (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hβ : ¬ M.IsAlphaCut v v₂ x₁ x₂)
    (L γ η δ C₁ : ℝ) (hη : 0 < η) (hη1 : η < 1) (c : ℕ) (hn : (M.atoms.card : ℝ) ≤ Real.log L ^ c)
    (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L)
    (hδ0 : 0 < δ) (hC : 0 ≤ C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((M.cut v v₂ x₁ x₂).countA L γ δ C₁ w Adm P)
      (ENNReal.ofReal ((10 * (((c + 4 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (c + 4)) *
        excessRHS L γ η [] 1 2)) := by
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hL0 : 0 < L := by linarith
  have h := betaCut_isDeviation M hcd hdeg hM hβ L γ δ C₁ w Adm P hL hδ0 hC hP0 hPinh
  refine isDeviation_mono h ?_
  rw [excessRHS_beta L γ η hL0]
  have hlog1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  have hε : 0 < η ^ 2 - η ^ 3 := by
    have : η ^ 3 < η ^ 2 := by nlinarith [pow_pos hη 2]
    linarith
  have hbound : ((4 * M.atoms.card + 6 : ℕ) : ℝ) * Real.log L ^ 4 ≤
      10 * (((c + 4 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (c + 4) * L ^ (-η ^ 3 + η ^ 2) := by
    have h1 : ((4 * M.atoms.card + 6 : ℕ) : ℝ) ≤ 10 * Real.log L ^ c := by
      push_cast
      have : (1 : ℝ) ≤ Real.log L ^ c := one_le_pow₀ hlog1
      linarith
    have h2 : Real.log L ^ (c + 4) ≤ (((c + 4 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (c + 4) * L ^ (η ^ 2 - η ^ 3) :=
      log_pow_le (c + 4) (by omega) L _ hL1 hε
    have h3 : ((4 * M.atoms.card + 6 : ℕ) : ℝ) * Real.log L ^ 4 ≤ 10 * Real.log L ^ (c + 4) := by
      rw [pow_add]
      have : 0 ≤ Real.log L ^ 4 := by positivity
      nlinarith
    calc _ ≤ 10 * Real.log L ^ (c + 4) := h3
      _ ≤ 10 * ((((c + 4 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (c + 4) * L ^ (η ^ 2 - η ^ 3)) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = _ := by rw [show -η ^ 3 + η ^ 2 = η ^ 2 - η ^ 3 by ring]; ring
  have : ((4 * M.atoms.card + 6 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.log L ^ 4) =
      ENNReal.ofReal (((4 * M.atoms.card + 6 : ℕ) : ℝ) * Real.log L ^ 4) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  rw [this]
  exact ENNReal.ofReal_le_ofReal hbound

end WaveTurbulence.FinalCount
