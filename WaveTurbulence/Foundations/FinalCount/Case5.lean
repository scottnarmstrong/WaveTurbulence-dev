/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Case5S2
public import WaveTurbulence.Foundations.FinalCount.OpD
public import WaveTurbulence.Foundations.FinalCount.EvenCase96
public import WaveTurbulence.Foundations.FinalCount.Odd96
public import WaveTurbulence.Foundations.FinalCount.Prop102Bridge
import Mathlib.Tactic

/-! # Prop 9.6, case (5): `V_α = V_β = 1` (DH23 L1887)

CONDITIONAL on `Case5VineS2` (distinct name; not a source result): in the two-chain branch the post molecule is not the
half-closure of a vine (II), because otherwise `M₀` would be a vine (II) with joints `α, β`, which is LG (Prop 9.5),
contradicting `alphaSG`.  OPEN: the proof of `Case5VineS2` (see PROGRESS.md).
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8.P101

/-- **OPEN (named input).** In the two-chain branch of case (5), the post molecule is not a half-closed vine (II). -/
def Case5VineS2.{u', v'} (d : ℕ) (γ η : ℝ) : Prop :=
  ∀ (L : ℝ) {V : Type u'} {D : Type v'} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
    (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop),
    FinalShape M cls odd → FinalDec M cls L γ η Adm → (∃ κ, Adm κ) → ¬ odd → (∃ w, w ∉ M.atoms) →
    ∀ {a₀ b₀ : V}, a₀ ∈ M.atoms → b₀ ∈ M.atoms → a₀ ≠ b₀ → (cls a₀).IsAlpha → (cls b₀).IsBeta →
      M.deg a₀ = 2 → M.deg b₀ = 2 → (∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → M.deg v = 4) →
      IsChainSet M cls {a₀} → IsChainSet M cls {b₀} →
      ∀ T : TwoExit (Degen.eraseAtoms M {a₀}), T.Y = {b₀} → ¬ IsVineIIHalfClosure T.post


theorem chain_single_b {M : Molecule V D} {cls : V → Cls} {a₀ b₀ : V} {K : Finset V}
    (hb₀ : b₀ ∈ M.atoms) (hbn : ¬ (cls b₀).IsEps) (hK : IsChainSet M cls K)
    (hchar : ∀ v ∈ M.atoms, ¬ (cls v).IsEps ↔ (v = a₀ ∨ v = b₀)) (hbK : b₀ ∉ K) (ha₀K : a₀ ∈ K) :
    IsChainSet M cls {b₀} := by
  classical
  refine ⟨⟨b₀, mem_singleton_self _⟩, by simpa using hb₀, fun v hv => by rw [mem_singleton.mp hv]; exact hbn, ?_, ?_⟩
  · intro u hu w hw hn
    rw [mem_singleton.mp hu] at hw
    rcases (hchar w (by obtain ⟨z, _, hz⟩ := hw; rw [← hz]; exact M.atom_mem _)).mp hn with rfl | rfl
    · exfalso
      exact hbK (hK.2.2.2.1 w ha₀K b₀ (Mole.adj_symmetric M hw) hbn)
    · exact mem_singleton_self _
  · intro u hu w hw
    rw [mem_singleton.mp hu, mem_singleton.mp hw]; exact Relation.EqvGen.refl _


theorem ofReal_mul3 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal x * (ENNReal.ofReal y * ENNReal.ofReal z) = ENNReal.ofReal (x * y * z) := by
  rw [← ENNReal.ofReal_mul hy, ← ENNReal.ofReal_mul hx, mul_assoc]

/-- **Case (5): `V_α = V_β = 1`**, conditional on `Case5VineS2`. -/
theorem case_five_of_vine (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1)
    (hv : Case5VineS2.{u, v} d γ η) :
    EvenCaseAt.{u, v} d γ η (fun a b => a = 1 ∧ b = 1) := by
  classical
  have hγ0 : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
  rw [hγ0] at hsm
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  obtain ⟨s1, s2, s3, s4⟩ := small_facts hd hγ.1 hγ.2 hη hsm
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hη2max : η / 2 ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  have hη4 : 0 < η / 2 / 2 := by positivity
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨Cd, hCd, hopd⟩ := opDInput.{u, v} d γ η hη
  obtain ⟨Cp, hCp, h104⟩ := prop104_one.{u, v} d hd γ hγ01 (η / 2) (by positivity) hη2max
    (prop102InputSz.{u, v} d hd γ (η / 2 / 2) hγ01 hη4 (by rw [hγ0]; linarith) (by linarith))
  refine ⟨max (max C₀ Cd) (2 * Cp), le_trans hC₀ ((le_max_left _ _).trans (le_max_left _ _)), fun m C1 hC1 δ hδ => ?_⟩
  have hC1a : C₀ ≤ C1 := (le_max_left _ _).trans ((le_max_left _ _).trans hC1)
  have hC1b : Cd ≤ C1 := (le_max_right _ _).trans ((le_max_left _ _).trans hC1)
  have hC1c : C1 ≥ 2 * Cp := (le_max_right _ _).trans hC1
  have hC11 : 1 ≤ C1 := le_trans hC₀ hC1a
  have hδ0 := hδ.1
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 hC1a
  obtain ⟨Kd, Bd, Rd, hRd⟩ := hopd C1 hC1b δ hδ
  obtain ⟨R104, hR104⟩ := h104 m C1 hC1c δ hδ
  set K : ℝ := max Kd 0 + 1 with hK
  set B : ℝ := max Bd 0 with hB
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨R3, hR31, hR3⟩ := const_log_le_rpow (C := 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * K) (8 + B) (ε := η ^ 2 / 8)
    (by positivity)
  refine ⟨max (max (max L₀ Rd) (max R104 R3)) (Real.exp 1), le_trans hL₀1 (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)), ?_⟩
  intro L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcnd
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLRd : Rd ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLR104 : R104 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLR3 : R3 ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans hL))
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  by_cases hA : ∃ κ, Adm κ
  swap
  · push Not at hA
    rw [countA_zero_of_noAdm M L γ δ C1 Adm P hA]; exact bot_le
  obtain ⟨κ0, hκ0⟩ := hA
  obtain ⟨hα, hβ⟩ := hcnd
  obtain ⟨a₀, b₀, ha₀, hb₀, hαa, hβb, hab, hchar, hdeg2a, hdeg2b, hdeg4⟩ := c5_atoms hS hnodd hα hβ
  have hEps : ∀ v ∈ M.atoms, v ≠ a₀ → v ≠ b₀ → (cls v).IsEps := by
    intro v hv h1 h2
    by_contra hn
    rcases (hchar v hv).mp hn with h | h
    · exact h1 h
    · exact h2 h
  have han : ¬ (cls a₀).IsEps := alpha_not_eps hαa
  have hbn : ¬ (cls b₀).IsEps := beta_not_eps hβb
  obtain ⟨K0, hK0c, ha₀K⟩ := exists_chainSet M cls ha₀ han
  have hKsub : ∀ v ∈ K0, v = a₀ ∨ v = b₀ := fun v hv => (hchar v (hK0c.2.1 hv)).mp (hK0c.2.2.1 v hv)
  -- the gap of the α-atom
  have hlab := hF.labRange a₀ ha₀ hαa
  set R0 := (cls a₀).lab with hR0
  have hR0pos : 0 < R0 := lt_of_lt_of_le (inv_pos.mpr hLp) hlab.1
  have hdv : M.deg a₀ = 2 := hdeg2a
  have hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ K0 ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
      R0 / 2 ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := by
    intro κ hκ
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_darts M hdv
    exact ⟨x, y, hx ▸ ha₀K, hy.trans hx.symm, hxy, (hF.alphaGap κ hκ a₀ ha₀ hαa x y hx hy hxy).1⟩
  have hNB : ∀ v ∈ M.atoms, (cls v).IsEps → ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ → M.IsAlphaCut v v₂ x₁ x₂ :=
    fun v hv hε v₂ x₁ x₂ hc => noBeta_eps hS hF hLp hκ0 hv hε hc
  have hconst : 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * (K * Real.log L ^ B) ≤ L ^ (η ^ 2 / 8) := by
    have h := hR3 L hLR3
    have hl0 : 0 < Real.log L := by linarith
    rw [Real.rpow_add hl0] at h
    calc _ = 3 ^ d * (2 * (d : ℝ) * δ⁻¹ + 1) * K * (Real.log L ^ (8 : ℝ) * Real.log L ^ B) := by ring
      _ ≤ _ := h
  have hKge : 1 ≤ K * Real.log L ^ B := by
    have h1 : 1 ≤ K := by rw [hK]; have := le_max_right Kd 0; linarith
    have h2 : 1 ≤ Real.log L ^ B := Real.one_le_rpow hlog (le_max_right Bd 0)
    linarith [mul_le_mul h1 h2 zero_le_one (by linarith : (0 : ℝ) ≤ K)]
  -- the common bound
  have hbound : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal
      (3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) *
        (K * Real.log L ^ B) * L ^ (-(4 / 7 * min γ (1 - γ)))) := by
    have hcost0 : 0 ≤ 3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ) := by
      have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ Real.log L) (8 : ℝ)
      positivity
    have hKc0 : 0 ≤ K * Real.log L ^ B := by linarith
    have hP104 : P104At.{u, v} d γ δ (η / 2) C1 L m := hR104 L hLR104
    by_cases hb : b₀ ∈ K0
    · have hKeq : K0 = {a₀, b₀} := by
        ext x; constructor
        · intro hx; rcases hKsub x hx with rfl | rfl <;> simp
        · intro hx; rcases mem_insert.mp hx with rfl | h
          · exact ha₀K
          · rw [mem_singleton.mp h]; exact hb
      have := s1_key (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) (ρ := R0 / 2) hγ01 hL1 hlog hδ hC11
        (half_pos hR0pos) hP104 M cls odd Adm P hS hF hnodd hnc hη hP hMA hsz ha₀ hb₀ hab hdeg2a hdeg2b hdeg4 hEps
        hK0c hKeq hAdm hfr hNB
      refine this.trans ?_
      rw [← ENNReal.ofReal_mul hcost0]
      refine ENNReal.ofReal_le_ofReal ?_
      have hX := Real.rpow_nonneg hLp.le (-(4 / 7 * min γ (1 - γ)))
      linarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKge hcost0) hX]
    · have hKeq : K0 = {a₀} := by
        ext x; constructor
        · intro hx; rcases hKsub x hx with rfl | rfl
          · simp
          · exact absurd hx hb
        · intro hx; rw [mem_singleton.mp hx]; exact ha₀K
      have hKb : IsChainSet M cls {b₀} := chain_single_b hb₀ hbn hK0c hchar hb ha₀K
      have hK1 : IsChainSet M cls {a₀} := hKeq ▸ hK0c
      have hAdm' : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ ({a₀} : Finset V) ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧
          R0 / 2 ≤ ‖Molecule.kvec L (0 : Mom d) κ y - Molecule.kvec L (0 : Mom d) κ y'‖ := by
        intro κ hκ; rw [hKeq] at hAdm; exact hAdm κ hκ
      have := s2_key (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) (ρ := R0 / 2) (Kd := Kd) (Bd := Bd) hγ01 hL1 hlog hδ
        hC11 (half_pos hR0pos) hP104 (hRd L hLRd) M cls odd Adm P hS hF hnodd hnc hη hP hMA hsz ha₀ hb₀ hab hdeg2a
        hdeg2b hdeg4 hEps hK1 hKb hAdm' hfr hNB
        (hv L M cls odd Adm hS hF ⟨κ0, hκ0⟩ hnodd hfr ha₀ hb₀ hab hαa hβb hdeg2a hdeg2b hdeg4 hK1 hKb)
      refine this.trans ?_
      have hl : Real.log L ^ Bd ≤ Real.log L ^ B := Real.rpow_le_rpow_of_exponent_le hlog (le_max_left Bd 0)
      have hl0 : 0 ≤ Real.log L ^ Bd := Real.rpow_nonneg (by linarith) _
      have hKd : Kd * Real.log L ^ Bd ≤ K * Real.log L ^ B := by
        have h1 : Kd * Real.log L ^ Bd ≤ max Kd 0 * Real.log L ^ Bd := mul_le_mul_of_nonneg_right (le_max_left _ _) hl0
        have h2 : max Kd 0 * Real.log L ^ Bd ≤ max Kd 0 * Real.log L ^ B :=
          mul_le_mul_of_nonneg_left hl (le_max_right _ _)
        have h3 : max Kd 0 * Real.log L ^ B ≤ K * Real.log L ^ B :=
          mul_le_mul_of_nonneg_right (by rw [hK]; linarith) (Real.rpow_nonneg (by linarith) _)
        linarith
      calc _ ≤ ENNReal.ofReal (3 ^ d * ((d : ℝ) * δ⁻¹ * (R0 / 2)⁻¹ * L ^ (-γ) + L ^ (γ - 1)) * Real.log L ^ (8 : ℝ)) *
            (ENNReal.ofReal (K * Real.log L ^ B) * ENNReal.ofReal (L ^ (-(4 / 7 * min γ (1 - γ))))) :=
            mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hKd) le_rfl)
        _ = _ := ofReal_mul3 hcost0 hKc0
  -- the final interpolation
  have hA1 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hcard : (M.atoms.filter fun a => M.deg a ≠ 4).card = 2 := by
    rw [card_deg_ne_four_even hS hnodd, card_nonEps, hα, hβ]
  have hsplit := finalRHS_ge_split M cls odd hL1 hη.le hF.labRange (v₀ := a₀) (mem_filter.mpr ⟨ha₀, hαa⟩)
  rw [hγ0] at hbound
  refine case5_finish hd hγ.1 hγ.2 hη hsm hδ0 hL1 hlog ⟨hlab.1, hlab.2⟩ hK0 hconst
    (ρ := (M.rho : ℝ)) (c := 2) (Nat.cast_nonneg _) (le_refl _) ?_ hbound ?_
  · refine hA1.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    congr 1
    rw [hcard]; push_cast; ring
  · refine le_trans (le_of_eq ?_) hsplit
    rw [hR0]
    congr 2
    rw [hα, hβ, if_neg hnodd, hγ0]; push_cast; ring

end WaveTurbulence.FinalCountG8
