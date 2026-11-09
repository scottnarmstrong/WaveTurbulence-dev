/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Odd96
import Mathlib.Tactic

/-! # Prop 9.6 at `0 < γ ≤ 1/2`, case (1): the odd component (DH23 L1874–L1877; M2 §4.5)

Port of main's `FinalCountG8.case_odd` (`FinalCount/Odd96.lean`) to `γ ≤ 1/2`, where `γ₀ = min γ (1 - γ) = γ`.
The structure (Prop 10.1′ `proposition_one_off_bound`, Prop 10.2(1) `prop102InputSz`, roughbd `rough96`, all for
`γ ∈ (0, 1)`) is main's verbatim; only the exponent arithmetic changes (`odd_arith_low`, `odd0_arith_q`). Margins
(M2 §4.5): `(τ − 4C₀η³)w` for `w = V_α + V_β ≥ 1`, and `(3γ/5)(1 − η³) − 3C₀η³` for `w = 0`. -/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp WaveTurbulence.FinalCountG8.P101

/-- `min γ (1 - γ) = γ` for `γ ≤ 1/2`. -/
theorem min_gamma_low {γ : ℝ} (hγ : γ ≤ 1 / 2) : min γ (1 - γ) = γ := min_eq_left (by linarith)

/-- Exponent arithmetic of case (1) at `γ ≤ 1/2`: `η³(16d+28)(p+3) ≤ V_α(γ-5η)/2 + (γ₀+2η²)V_β`, `γ₀ = γ`. -/
theorem odd_arith_low {d : ℕ} {γ η Va Vb : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1 / 2) (hη : 0 < η)
    (hη1 : η ≤ γ / 200) (hηd : (d : ℝ) * η ≤ γ / 4) (hVa : 0 ≤ Va) (hVb : 0 ≤ Vb)
    (hp : 1 ≤ Va + Vb) :
    η ^ 3 * (16 * (d : ℝ) + 28) * ((Va + Vb + 2) + 1) ≤ Va * ((γ - 5 * η) / 2) + (γ + 2 * η ^ 2) * Vb := by
  have hη3 : η ≤ 1 / 100 := by linarith
  have h1 : η ^ 3 * (16 * (d : ℝ) + 28) ≤ γ / 40 := by
    have e : η ^ 3 * (16 * (d : ℝ) + 28) = η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) := by ring
    rw [e]
    have h2 : 16 * ((d : ℝ) * η) + 28 * η ≤ 4 * γ + 28 * (γ / 200) := by nlinarith
    have h3 : η ^ 2 ≤ 1 / 10000 := by nlinarith
    calc η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) ≤ (1 / 10000) * (4 * γ + 28 * (γ / 200)) :=
          mul_le_mul h3 h2 (by positivity) (by norm_num)
      _ ≤ γ / 40 := by nlinarith
  have h4 : γ / 10 ≤ (γ - 5 * η) / 2 := by nlinarith
  have h5 : γ / 10 ≤ γ + 2 * η ^ 2 := by nlinarith [pow_pos hη 2]
  have hq : ((Va + Vb + 2) + 1) ≤ 4 * (Va + Vb) := by linarith
  have hc : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
  calc η ^ 3 * (16 * (d : ℝ) + 28) * ((Va + Vb + 2) + 1) ≤ η ^ 3 * (16 * (d : ℝ) + 28) * (4 * (Va + Vb)) :=
        mul_le_mul_of_nonneg_left hq hc
    _ ≤ (γ / 40) * (4 * (Va + Vb)) := mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ Va * ((γ - 5 * η) / 2) + (γ + 2 * η ^ 2) * Vb := by
        nlinarith [mul_le_mul_of_nonneg_left h4 hVa, mul_le_mul_of_nonneg_left h5 hVb]

/-- Exponent arithmetic of case (1) with `V_α = V_β = 0`, for a general exponent `q = γ₀ > 0`
(main's `odd0_arith` is the instance `q = 1 - γ`). -/
theorem odd0_arith_q {η q ρ K c : ℝ} (hq : 0 < q) (hK : η ^ 3 * K ≤ q / 40) (hη3 : η ^ 3 ≤ 1 / 2)
    (hc : c ≤ 2) (_hc0 : 0 ≤ c) (hη : 0 ≤ η) (hK0 : 0 ≤ K) :
    η ^ 3 * (-η ^ 2 * ρ + K * (c + 1)) + (1 - η ^ 3) * (-(3 / 5 * q)) ≤
      (0 : ℝ) * ((q - 5 * η) / 2) + ((q + 2 * η ^ 2) * 0 - (2 * q + 5 * η ^ 2) * 0) +
        (-(η ^ 5) * ρ) := by
  have h1 : η ^ 3 * K * (c + 1) ≤ 3 * (q / 40) :=
    (mul_le_mul_of_nonneg_left (by linarith : c + 1 ≤ 3) (mul_nonneg (pow_nonneg hη 3) hK0)).trans (by linarith)
  have h2 : (1 / 2) * (3 / 5 * q) ≤ (1 - η ^ 3) * (3 / 5 * q) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e : η ^ 3 * (-η ^ 2 * ρ) = -(η ^ 5) * ρ := by ring
  have e2 : η ^ 3 * (-η ^ 2 * ρ + K * (c + 1)) = η ^ 3 * (-η ^ 2 * ρ) + η ^ 3 * K * (c + 1) := by ring
  rw [e2, e]
  nlinarith [h1, h2]

section
variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

open Classical in
/-- **Case (1) at `γ ≤ 1/2`: the odd component.** -/
theorem case_odd_low (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 2)) (η : ℝ) (hη : 0 < η)
    (hη1 : η ≤ min γ (1 - γ) / 200) (hηd : (d : ℝ) * η ≤ min γ (1 - γ) / 4) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → odd →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (finalRHS M cls odd L γ η) := by
  classical
  have hγ0 : min γ (1 - γ) = γ := min_gamma_low hγ.2
  rw [hγ0] at hη1 hηd
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hγ.1, by linarith [hγ.2]⟩
  have hηγ : η ≤ min γ (1 - γ) := by rw [hγ0]; linarith
  have hηmax : η ≤ min γ (1 - γ) / 2 := by rw [hγ0]; linarith
  obtain ⟨C₀, hC₀, hrough⟩ := rough96.{u, v} d hd γ η hγ01 hη hηγ hηs
  obtain ⟨Cs, hCs, hP1⟩ := proposition_one_off_bound.{u, v} d hd γ hγ01 η hη hηmax
  obtain ⟨C102, hC102, h102⟩ := prop102InputSz.{u, v} d hd γ η hγ01 hη hηγ hηs
  refine ⟨max (max C₀ Cs) C102, le_trans hC₀ ((le_max_left _ _).trans (le_max_left _ _)), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 (((le_max_left _ _).trans (le_max_left _ _)).trans hC1)
  obtain ⟨Rp, hRp⟩ := hP1 C1 (((le_max_right _ _).trans (le_max_left _ _)).trans hC1) δ hδ
  obtain ⟨R102, hR102⟩ := h102 m C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max (max L₀ Rp) R102) (Real.exp 1),
    le_trans hL₀1 (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro L hL V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hodd
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLRp : Rp ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hL))
  have hLR102 : R102 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  obtain ⟨u, hu, w, hw, huw, hu1, hw3, hrest⟩ := hS.oddDeg hodd
  have hM : M.IsMolecule := hS.isMolecule
  have hA2 := hL₀ L hLL₀ M cls odd Adm P hS hF hsz hP hMA
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le (by linarith)
  have hcR : ((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) ≤
      ((alphaAtoms M.atoms cls).card : ℝ) + ((betaAtoms M.atoms cls).card : ℝ) + 2 := by
    have := card_deg_ne_four_odd hS hodd
    rw [card_nonEps] at this; exact_mod_cast this
  by_cases hp0 : (nonEps M.atoms cls).Nonempty
  · -- step A: 𝔄 ≲ 1
    have hPM := pmol_nonEps hS hu hu1
    have hLG : ∀ κ, (Adm κ ∧ CellGapRestriction M L (0 : Mom d) (fun S => P (Mole.appbLinkParent M S)) (GapScale L) κ) →
        P101.LargeGapOff (nonEps M.atoms cls) M L γ η (0 : Mom d) κ := by
      intro κ hκ v hvB x y hx hy hxy
      have hv : v ∈ M.atoms := hx ▸ M.atom_mem x
      have hε : (cls v).IsEps := by
        by_contra hne; exact hvB (mem_filter.mpr ⟨hv, hne⟩)
      exact (hF.epsLG κ hκ.1 v hv hε x y hx hy hxy).le
    have hA1 : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ 1 :=
      (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans
        (hRp L hLRp hlog (nonEps M.atoms cls) M hPM (fun x hx => hS.noLoop x) _ _ hLG (fun κ hκ => hκ.2)
          (fun S _ => hP _))
    have hA1' : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (0 : ℝ)) := by
      rw [Real.rpow_zero, ENNReal.ofReal_one]; exact hA1
    have hi := interp_L hL1 hA2 hA1' hθ0 hθ1
    refine hi.trans (ENNReal.ofReal_le_ofReal ?_)
    refine le_trans ?_ (finalRHS_ge M cls odd hL1 hη.le hF.labRange)
    refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
    rw [if_pos hodd]
    have hp : 1 ≤ ((alphaAtoms M.atoms cls).card : ℝ) + ((betaAtoms M.atoms cls).card : ℝ) := by
      have : 1 ≤ (nonEps M.atoms cls).card := card_pos.mpr hp0
      rw [card_nonEps] at this; exact_mod_cast this
    have hA := odd_arith_low (d := d) (γ := γ) (η := η) (Va := ((alphaAtoms M.atoms cls).card : ℝ))
      (Vb := ((betaAtoms M.atoms cls).card : ℝ)) hγ.1 hγ.2 hη hη1 hηd (Nat.cast_nonneg _) (Nat.cast_nonneg _) hp
    have hc0 : 0 ≤ η ^ 3 * (16 * (d : ℝ) + 28) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hcR hc0
    rw [hγ0]
    nlinarith [hA, hmul]
  · -- p = 0: both odd atoms have degree 3; Prop 10.2 gives `L^{-3γ₀/5}`
    have hall : ∀ a ∈ M.atoms, (cls a).IsEps := by
      intro a ha; by_contra hn; exact hp0 ⟨a, mem_filter.mpr ⟨ha, hn⟩⟩
    have hdeg4 : ∀ a ∈ M.atoms, a ≠ u → a ≠ w → M.deg a = 4 := by
      intro a ha h1 h2
      have := (hS.classes a ha).not.mpr (fun h => h (hall a ha))
      rcases hrest a ha h1 h2 with h | h <;> omega
    have hdu : M.deg u = 3 := by
      have := (hS.classes u hu).not.mpr (fun h => h (hall u hu)); omega
    have hdw : M.deg w = 3 := by
      have := (hS.classes w hw).not.mpr (fun h => h (hall w hw)); omega
    have hsum := Mole.sum_degrees_eq_two_mul_bonds M
    have hsub : ({u, w} : Finset V) ⊆ M.atoms := by
      intro x hx; rcases mem_insert.mp hx with rfl | h
      · exact hu
      · rw [mem_singleton.mp h]; exact hw
    rw [← sum_sdiff hsub] at hsum
    have e1 : ∑ x ∈ M.atoms \ {u, w}, M.deg x = 4 * (M.atoms.card - 2) := by
      rw [sum_congr rfl (fun x hx => hdeg4 x (mem_sdiff.mp hx).1 (fun h => (mem_sdiff.mp hx).2 (by simp [h]))
        (fun h => (mem_sdiff.mp hx).2 (by simp [h])))]
      rw [sum_const, card_sdiff_of_subset hsub, card_pair huw, smul_eq_mul]; ring
    rw [e1, sum_pair huw, hdu, hdw] at hsum
    have h2V : 2 ≤ M.atoms.card := by have := card_le_card hsub; rw [card_pair huw] at this; exact this
    have hE : (M.bonds.card : ℤ) = 2 * M.atoms.card - 1 := by omega
    set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
    have hA3 : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(3 / 5 * min γ (1 - γ)))) := by
      refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
      refine le_trans (WaveTurbulence.MoleProp4.countAFree_mono_adm M (B := WaveTurbulence.MoleProp4.lgAdm M L γ η P')
        (fun κ hκ => ⟨fun x y hxy hdir => ?_, hκ.2⟩)) ?_
      · have hv : M.atom x ∈ M.atoms := M.atom_mem x
        exact (hF.epsLG κ hκ.1 _ hv (hall _ hv) x y rfl hxy.symm hdir).le
      · exact hR102 L hLR102 M hM hS.conn (fun a b => hS.noTriple a b) hE hsz P' (fun S _ => hP _)
    have hVa : (alphaAtoms M.atoms cls).card = 0 := by
      have : nonEps M.atoms cls = ∅ := not_nonempty_iff_eq_empty.mp hp0
      have h := card_nonEps M cls; rw [this] at h; simp at h; omega
    have hVb : (betaAtoms M.atoms cls).card = 0 := by
      have : nonEps M.atoms cls = ∅ := not_nonempty_iff_eq_empty.mp hp0
      have h := card_nonEps M cls; rw [this] at h; simp at h; omega
    have hA3' : M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (1 * L ^ (-(3 / 5 * γ))) := by
      rw [one_mul]; rwa [hγ0] at hA3
    have hcR2 : ((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) ≤ 2 := by
      rw [hVa, hVb] at hcR; simpa using hcR
    have hq : 0 < γ := hγ.1
    have hη3 : η ^ 3 * (16 * (d : ℝ) + 28) ≤ γ / 40 := by
      have e : η ^ 3 * (16 * (d : ℝ) + 28) = η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) := by ring
      rw [e]
      have h2 : 16 * ((d : ℝ) * η) + 28 * η ≤ 4 * γ + 28 * (γ / 200) := by nlinarith
      have h3 : η ^ 2 ≤ 1 / 10000 := by nlinarith
      calc η ^ 2 * (16 * ((d : ℝ) * η) + 28 * η) ≤ (1 / 10000) * (4 * γ + 28 * (γ / 200)) :=
            mul_le_mul h3 h2 (by positivity) (by norm_num)
        _ ≤ γ / 40 := by nlinarith
    have he := odd0_arith_q (η := η) (q := γ) (ρ := (M.rho : ℝ)) (K := 16 * (d : ℝ) + 28)
      (c := ((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ)) hq hη3 (by
        have h : η ≤ 1 / 2 := by linarith [hγ.1, hγ.2]
        nlinarith [pow_pos hη 2, mul_pos hη hη]) hcR2 (Nat.cast_nonneg _) hη.le (by positivity)
    have hend := endgame hL1 le_rfl hA2 hA3' hθ0 hθ1 he
    refine hend.trans (ENNReal.ofReal_le_ofReal ?_)
    have hfin := finalRHS_ge M cls odd hL1 hη.le hF.labRange
    rw [hVa, hVb, if_pos hodd] at hfin
    rw [hγ0] at hfin
    simpa using hfin

end

end WaveTurbulence.GammaLow.FinalCount
