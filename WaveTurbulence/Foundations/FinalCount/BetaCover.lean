/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.BetaCount
/-! The covering of `β`-cut decorations by `4n+6` post classes (FINALCOUNT-HALF M2e). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Finset
namespace WaveTurbulence.FinalCount
open WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

/-- The index set of grid classes. -/
def betaIndex (n : ℕ) : Finset (ℤ × ℤ) := Finset.Icc (-((n : ℤ) + 1)) ((n : ℤ) + 1) ×ˢ ({-1, 1} : Finset ℤ)

theorem betaIndex_card (n : ℕ) : (betaIndex n).card = 2 * (2 * n + 3) := by
  unfold betaIndex
  rw [Finset.card_product, Int.card_Icc]
  simp only [Finset.card_pair (by norm_num : (-1 : ℤ) ≠ 1)]
  omega

theorem beta_cover (hcd : M.IsCutData v v₂ x₁ x₂) (hsep : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂)
    (L γ δ : ℝ) (hδ : 0 < δ) (hL : 0 < L) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) :
    decSet M L γ δ w Adm c β k0 ⊆
      ⋃ i ∈ betaIndex M.atoms.card, decSet (M.cut v v₂ x₁ x₂) L γ δ w Adm
        (betaParams M v v₂ x₁ x₂ (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2).1
        (betaParams M v v₂ x₁ x₂ (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2).2.1
        (betaParams M v v₂ x₁ x₂ (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2).2.2 := by
  classical
  intro κ ⟨hdec, hres, hadm⟩
  set T := δ⁻¹ * L ^ (-2 * γ) with hT
  have hTpos : 0 < T := by positivity
  set S' := betaSide M v v₂ x₁ x₂ with hS'
  have hsub := betaSide_sub M hcd hsep
  have hv₂ : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
  have hvmem : v ∈ M.atoms := hcd.1
  have hcard : S'.card ≤ M.atoms.card :=
    (Finset.card_le_card hsub).trans (Finset.card_erase_le)
  have hΓ₂ := beta_gamma_side M hcd hsep L w κ hdec.1
  set Bβ := ∑ a ∈ S', β a with hBβ
  set Bc := ∑ a ∈ S', c a with hBc
  set y : ℝ := (M.cut v v₂ x₁ x₂).Gamma L w κ v₂ + Bβ with hy
  have hy_bound : |y| ≤ S'.card * T := by
    have : y = - ∑ a ∈ S', (M.Gamma L w κ a - β a) := by
      rw [hy, hΓ₂, hBβ, Finset.sum_sub_distrib]; ring
    rw [this, abs_neg]
    calc |∑ a ∈ S', (M.Gamma L w κ a - β a)| ≤ ∑ a ∈ S', |M.Gamma L w κ a - β a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a ∈ S', T := Finset.sum_le_sum fun a ha => hres.1 a (Finset.mem_erase.mp (hsub ha)).2
      _ = S'.card * T := by simp
  set j : ℤ := round (y / T) with hj
  have hj1 : |y / T - j| ≤ 1 / 2 := abs_sub_round _
  have hyT : |y / T| ≤ S'.card := by
    rw [abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos]; exact hy_bound
  have hjle : (j : ℝ) ≤ M.atoms.card + 1 := by
    have h1 := (abs_le.mp hj1).2
    have h2 := (abs_le.mp hyT).1
    have : (S'.card : ℝ) ≤ M.atoms.card := by exact_mod_cast hcard
    linarith [(abs_le.mp hyT).2, (abs_le.mp hj1).1]
  have hjge : -((M.atoms.card : ℝ) + 1) ≤ j := by
    have : (S'.card : ℝ) ≤ M.atoms.card := by exact_mod_cast hcard
    linarith [(abs_le.mp hyT).1, (abs_le.mp hj1).2]
  have hyj : |y - j * T| ≤ T / 2 := by
    have : y - j * T = (y / T - j) * T := by field_simp
    rw [this, abs_mul, abs_of_pos hTpos]
    nlinarith
  set u : ℝ := (M.Gamma L w κ v - β v) - (y - j * T) with hu
  have hΓv := hres.1 v hvmem
  have hu_bound : |u| ≤ T + T / 2 := by
    calc |u| ≤ |M.Gamma L w κ v - β v| + |y - j * T| := abs_sub _ _
      _ ≤ T + T / 2 := add_le_add hΓv hyj
  set e : ℤ := if 0 ≤ u then 1 else -1 with he
  have he_mem : e ∈ ({-1, 1} : Finset ℤ) := by
    simp only [he]; split_ifs <;> simp
  have hue : |u - e * T / 2| ≤ T := by
    simp only [he]
    split_ifs with hu0
    · rw [abs_le] at hu_bound ⊢; constructor <;> push_cast <;> linarith [hu_bound.1, hu_bound.2]
    · rw [abs_le] at hu_bound ⊢; push Not at hu0; constructor <;> push_cast <;> linarith [hu_bound.1, hu_bound.2]
  rw [Set.mem_iUnion₂]
  refine ⟨(j, e), ?_, ?_⟩
  · unfold betaIndex
    rw [Finset.mem_product]
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, he_mem⟩
    · exact_mod_cast hjge
    · exact_mod_cast hjle
  · have hvne : v ≠ v₂ := hv₂.symm
    refine ⟨⟨hdec.1, fun a ha => ?_⟩, ⟨fun a ha => ?_, hres.2⟩, hadm⟩
    · by_cases h2 : a = v₂
      · simp only [betaParams, h2, ite_true]
        exact beta_c_side M hcd hsep L w c κ hdec
      by_cases h1 : a = v
      · simp only [betaParams, h1, hvne, ite_true, ite_false]
        have hs := cut_sum_split M hcd (fun x => M.dartSign x • Molecule.kvec L w κ x)
        have e1 := hdec.2 v hvmem
        have e2 := beta_c_side M hcd hsep L w c κ hdec
        have e3 : ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v, (M.cut v v₂ x₁ x₂).dartSign x • Molecule.kvec L w κ x =
            ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v, M.dartSign x • Molecule.kvec L w κ x := rfl
        rw [e3]
        rw [e1] at hs
        have : ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v, M.dartSign x • Molecule.kvec L w κ x =
            c v - ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂, M.dartSign x • Molecule.kvec L w κ x := by
          rw [hs]; abel
        rw [this, e2]; abel
      · simp only [betaParams, h1, h2, ite_false]
        have haM : a ∈ M.atoms := (Finset.mem_insert.mp ha).resolve_left h2
        rw [show (M.cut v v₂ x₁ x₂).dartsAt a = M.dartsAt a from cut_dartsAt_other M hcd h1 h2]
        exact hdec.2 a haM
    · by_cases h2 : a = v₂
      · simp only [betaParams, h2, ite_true]
        have : (M.cut v v₂ x₁ x₂).Gamma L w κ v₂ - (-Bβ + j * T) = y - j * T := by rw [hy]; ring
        rw [this]; exact hyj.trans (by linarith)
      by_cases h1 : a = v
      · simp only [betaParams, h1, hvne, ite_true, ite_false]
        have hsp := cut_gamma_split M hcd L w κ
        have : (M.cut v v₂ x₁ x₂).Gamma L w κ v - (β v + Bβ - j * T + e * T / 2) = u - e * T / 2 := by
          have : (M.cut v v₂ x₁ x₂).Gamma L w κ v = M.Gamma L w κ v - (M.cut v v₂ x₁ x₂).Gamma L w κ v₂ := by
            linarith
          rw [this, hu, hy]; ring
        rw [this]; exact hue
      · simp only [betaParams, h1, h2, ite_false]
        have haM : a ∈ M.atoms := (Finset.mem_insert.mp ha).resolve_left h2
        rw [cut_gamma_other M hcd L w κ h1 h2]
        exact hres.1 a haM

/-- **β-cut count bound** (DH23 L1784, first case of Prop 9.4): if the cut separates `v` from `v₂`, then
`𝔈(𝕄) ≤ (4|𝕄|+6) · 𝔈(𝕄_cut)` (any admissibility predicate, same on both sides). -/
theorem countE_le_beta_cut (hcd : M.IsCutData v v₂ x₁ x₂) (hdeg : M.deg v ≤ 4)
    (hsep : ¬ (M.cut v v₂ x₁ x₂).SameComponent v v₂)
    (L γ δ : ℝ) (hδ : 0 < δ) (hL : 0 < L) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    M.countE L γ δ w Adm ≤
      ((2 * (2 * M.atoms.card + 3) : ℕ) : ℕ∞) * (M.cut v v₂ x₁ x₂).countE L γ δ w Adm := by
  refine countE_le_mul_of_cover M (M.cut v v₂ x₁ x₂) L γ δ w Adm Adm _ ?_
  intro c β k0 hP
  refine ⟨ℤ × ℤ, betaIndex M.atoms.card,
    fun i => betaParams M v v₂ x₁ x₂ (δ⁻¹ * L ^ (-2 * γ)) c β k0 i.1 i.2, ?_, ?_, ?_⟩
  · rw [betaIndex_card]
  · intro i _
    exact beta_paramOK M hcd hdeg _ c β k0 hP i.1 i.2
  · exact beta_cover M hcd hsep L γ δ hδ hL w Adm c β k0

end WaveTurbulence.FinalCount
