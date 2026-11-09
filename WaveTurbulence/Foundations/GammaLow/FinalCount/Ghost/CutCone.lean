/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.Prop94Cut
public import WaveTurbulence.Foundations.FinalCount.AsmPot3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone8
/-! **Ghost assembly: the creation cone at an `α`-cut** (M1-R2 §11a: "Theorem 6.1 (e) would cover such atoms anyway").

Main's formal Phase 1 also cuts triple bonds (`nodesT`), and these `α`-cuts create `α`-atoms before Operation 2, so a
later group-D pair may have its later ghost created at an `α`-cut. Main's `α`-cut count (`alphaCut_isDeviation`,
`AlphaDev.lean`) has the factor `alphaN' d L τ R ρ = (⌊2ρL⌋₊+1)^d · 2(⌈8R/τ⌉₊+4)` (lattice points of the gap ball ×
the per-point classes). Under a cone condition on the gap (`CutCone`, aperture `θ`, centre per parameter class) the
classes are counted over `coneSet` instead of the ball (`countE_le_alpha_cut_cone`: main's `alpha_cover` on each
fixed-gap piece, `ρ = 0`), and `#coneSet ≤ 3·5^{d-1} θ^{d-1} (ρL)^d` gives the factor `3·5^{d-1}θ₀^{d-1} ≤ 3·5^d L^{-12η}`
over main's `κ = 0` bound (`alphaCut_excess_cone`). Main's lemmas are used as black boxes (no copied proofs). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **The cut cone**: in each parameter class the gap of the cut lies in the cone of aperture `θ` around a fixed nonzero
centre. -/
def CutCone (M : Molecule V D) (x₁ x₂ : D) (L γ δ θ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
    ∃ ctr : Mom d, ctr ≠ 0 ∧ ∀ κ ∈ decSet M L γ δ w Adm c β k0, InCone θ (Molecule.gapAt L w κ x₁ x₂) ctr

theorem gapAt_eq_latticePoint (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (x₁ x₂ : D) :
    Molecule.gapAt L w κ x₁ x₂ = latticePoint L (κ x₁ - κ x₂) := by
  unfold Molecule.gapAt Molecule.kvec
  rw [latticePoint_sub]; abel

/-- The class multiplier of the cone count (a natural number). -/
noncomputable def coneCutN (d : ℕ) (L τ R θ : ℝ) : ℕ :=
  ((2 * ⌊2 * R * L⌋₊ + 1) * (⌊4 * θ * (2 * R * L)⌋₊ + 1) ^ (d - 1)) * alphaN' d L τ R 0

variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- **The `α`-cut count under the cut cone.** -/
theorem countE_le_alpha_cut_cone (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (L γ δ θ : ℝ) (hδ : 0 < δ) (hL : 0 < L) (hθ : 0 ≤ θ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (R : ℝ)
    (hR : 0 ≤ R) (hgap : ∀ κ, Adm κ → ‖Molecule.gapAt L w κ x₁ x₂‖ ≤ 2 * R)
    (hcone : CutCone M x₁ x₂ L γ δ θ w Adm) :
    M.countE L γ δ w Adm ≤
      ((coneCutN d L (δ⁻¹ * L ^ (-2 * γ)) R θ : ℕ) : ℕ∞) * (M.cut v v₂ x₁ x₂).countE L γ δ w Adm := by
  have hτ : 0 < δ⁻¹ * L ^ (-2 * γ) := by positivity
  refine countE_le_mul_of_cover M (M.cut v v₂ x₁ x₂) L γ δ w Adm Adm _ ?_
  intro c β k0 hP
  obtain ⟨ctr, hctr, hc⟩ := hcone c β k0 hP
  refine ⟨(Fin d → ℤ) × ℤ × ℤ, (coneSet d L (2 * R) θ ctr).biUnion
      (fun n => alphaIndex d L (δ⁻¹ * L ^ (-2 * γ)) R (k0 x₁ + k0 x₂) (latticePoint L n) 0),
    fun i => alphaParams v v₂ L (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2.1 i.2.2, ?_, ?_, ?_⟩
  · refine card_biUnion_le.trans ?_
    calc ∑ n ∈ coneSet d L (2 * R) θ ctr,
          (alphaIndex d L (δ⁻¹ * L ^ (-2 * γ)) R (k0 x₁ + k0 x₂) (latticePoint L n) 0).card
        ≤ ∑ _n ∈ coneSet d L (2 * R) θ ctr, alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R 0 :=
          sum_le_sum fun n _ => card_alphaIndex_le L _ R hL hτ hR _ _ 0 le_rfl
      _ = (coneSet d L (2 * R) θ ctr).card * alphaN' d L (δ⁻¹ * L ^ (-2 * γ)) R 0 := by
          rw [sum_const, smul_eq_mul]
      _ ≤ coneCutN d L (δ⁻¹ * L ^ (-2 * γ)) R θ := by
          unfold coneCutN
          refine Nat.mul_le_mul_right _ ?_
          have := card_coneSet L hL (2 * R) θ (by positivity) hθ ctr hctr
          simpa only [show 2 * R * L = 2 * R * L from rfl] using this
  · intro i _
    exact alpha_paramOK M hcd hdeg _ _ c β k0 hP i.1 i.2.1 i.2.2
  · intro κ hκ
    have hg : Molecule.gapAt L w κ x₁ x₂ = latticePoint L (κ x₁ - κ x₂) := gapAt_eq_latticePoint L w κ x₁ x₂
    have hn : κ x₁ - κ x₂ ∈ coneSet d L (2 * R) θ ctr :=
      mem_coneSet_of L hL _ _ ctr _ (by rw [← hg]; exact hgap κ hκ.2.2) (by rw [← hg]; exact hc κ hκ)
    have hsub := alpha_cover M hcd L γ δ hδ hL w (fun κ' => Adm κ' ∧ κ' x₁ - κ' x₂ = κ x₁ - κ x₂) R
      (fun κ' h => hgap κ' h.1) c β k0 (latticePoint L (κ x₁ - κ x₂)) 0
      (fun κ' hκ' => by rw [gapAt_eq_latticePoint, hκ'.2.2.2, sub_self, norm_zero])
    have hmem : κ ∈ decSet M L γ δ w (fun κ' => Adm κ' ∧ κ' x₁ - κ' x₂ = κ x₁ - κ x₂) c β k0 :=
      ⟨hκ.1, hκ.2.1, hκ.2.2, rfl⟩
    obtain ⟨i, hi, hκi⟩ := Set.mem_iUnion₂.1 (hsub hmem)
    exact Set.mem_iUnion₂.2 ⟨i, mem_biUnion.2 ⟨_, hn, hi⟩, ⟨hκi.1, hκi.2.1, hκi.2.2.1⟩⟩

/-- **The `α`-cut deviation under the cut cone** (main's `alphaCut_isDeviation` with the cone count). -/
theorem alphaCut_isDeviation_cone (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hα : M.IsAlphaCut v v₂ x₁ x₂)
    (L γ δ C₁ θ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (P : Finset V → ℝ) (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) (hC : 0 < C₁) (hP0 : ∀ S, 0 ≤ P S)
    (hPinh : ∀ S' ∈ (M.cut v v₂ x₁ x₂).maximalLadders, ∀ S ∈ M.maximalLadders, S' ⊆ S → P S' = P S)
    (R : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hgap : ∀ κ, Adm κ → ‖Molecule.gapAt L w κ x₁ x₂‖ ≤ 2 * R)
    (hcone : CutCone M x₁ x₂ L γ δ θ w Adm) :
    IsDeviation (M.countA L γ δ C₁ w Adm P) ((M.cut v v₂ x₁ x₂).countA L γ δ C₁ w Adm P)
      (((coneCutN d L (δ⁻¹ * L ^ (-2 * γ)) R θ : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ 4)) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hE := countE_le_alpha_cut_cone M hcd hdeg L γ δ θ hδ hL0 hθ w Adm R hR hgap hcone
  have hc₀ : 0 ≤ L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) :=
    mul_nonneg (Real.rpow_nonneg hL0.le _) (mul_nonneg (inv_nonneg.2 hC.le) (Real.rpow_nonneg hδ.le _))
  have key := countA_cut_dev M hcd hdeg hM L γ δ C₁ w Adm P hL hδ.le hC.le hP0 hPinh
    ((coneCutN d L (δ⁻¹ * L ^ (-2 * γ)) R θ : ℕ) : ℕ∞) _ hc₀ hE (by
      have h := circuitRank_cut_alpha M hcd hα
      have e : M.circuitRank = (M.cut v v₂ x₁ x₂).circuitRank + 1 := by rw [h]; ring
      rw [e, rankFactor_succ d hL0 hδ hC.ne']
      exact le_of_eq (mul_comm _ _))
  rw [ENat.toENNReal_coe] at key
  exact key

/-- `coneCutN ≤ 3·5^{d-1} θ^{d-1} · alphaN'(2R)` (real form; `ρ = 2R`, `ρL ≥ 1`, `θρL ≥ 1`). -/
theorem coneCutN_le (L τ R θ : ℝ) (hL : 0 < L) (hRL : 1 ≤ 2 * R * L) (hθρ : 1 ≤ θ * (2 * R * L)) (hθ0 : 0 ≤ θ)
    (hd : 1 ≤ d) :
    (coneCutN d L τ R θ : ℝ) ≤ 3 * 5 ^ (d - 1) * θ ^ (d - 1) * (alphaN' d L τ R (2 * R) : ℝ) := by
  have hρL0 : 0 ≤ 2 * R * L := by linarith
  have h1 : ((2 * ⌊2 * R * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * (2 * R * L) := by
    push_cast; have := Nat.floor_le hρL0; linarith
  have h2 : ((⌊4 * θ * (2 * R * L)⌋₊ + 1 : ℕ) : ℝ) ≤ 5 * (θ * (2 * R * L)) := by
    push_cast
    have := Nat.floor_le (show 0 ≤ 4 * θ * (2 * R * L) by positivity)
    nlinarith
  have h3 : (2 * R * L) ^ d ≤ ((⌊2 * (2 * R) * L⌋₊ + 1 : ℕ) : ℝ) ^ d := by
    refine pow_le_pow_left₀ hρL0 ?_ d
    push_cast
    have := Nat.lt_floor_add_one (2 * (2 * R) * L)
    nlinarith
  have hA : (alphaN' d L τ R (2 * R) : ℝ) = ((⌊2 * (2 * R) * L⌋₊ + 1 : ℕ) : ℝ) ^ d * (alphaN' d L τ R 0 : ℝ) := by
    unfold alphaN'; push_cast; simp
  have hX : (0 : ℝ) ≤ alphaN' d L τ R 0 := Nat.cast_nonneg _
  unfold coneCutN
  push_cast
  calc ((2 * (⌊2 * R * L⌋₊ : ℝ) + 1) * ((⌊4 * θ * (2 * R * L)⌋₊ : ℝ) + 1) ^ (d - 1)) * (alphaN' d L τ R 0 : ℝ)
      ≤ ((3 * (2 * R * L)) * (5 * (θ * (2 * R * L))) ^ (d - 1)) * (alphaN' d L τ R 0 : ℝ) := by
        refine mul_le_mul_of_nonneg_right ?_ hX
        exact mul_le_mul (by exact_mod_cast h1) (pow_le_pow_left₀ (by positivity) (by exact_mod_cast h2) _)
          (by positivity) (by positivity)
    _ = 3 * 5 ^ (d - 1) * θ ^ (d - 1) * ((2 * R * L) ^ (1 + (d - 1)) * (alphaN' d L τ R 0 : ℝ)) := by
        rw [pow_add, mul_pow, mul_pow]; ring
    _ = 3 * 5 ^ (d - 1) * θ ^ (d - 1) * ((2 * R * L) ^ d * (alphaN' d L τ R 0 : ℝ)) := by
        congr 3; congr 1; omega
    _ ≤ 3 * 5 ^ (d - 1) * θ ^ (d - 1) * (alphaN' d L τ R (2 * R) : ℝ) := by
        rw [hA]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hX) (by positivity)
        exact_mod_cast h3

end WaveTurbulence.GammaLow.FinalCount.Ghost
