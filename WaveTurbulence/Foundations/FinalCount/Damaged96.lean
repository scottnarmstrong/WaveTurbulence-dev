/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Damaged96Statement
public import WaveTurbulence.Foundations.FinalCount.Rough96
public import WaveTurbulence.Foundations.FinalCount.Interp96
public import WaveTurbulence.Foundations.FinalCount.Odd96
public import WaveTurbulence.Foundations.FinalCount.P101.Main
import Mathlib.Tactic

/-! # The damaged-component bound DCB (R29 item 5), proof

`𝔄 ≤ 1` (Prop 10.1' with protected set the `α`/`β`-atoms, `P101.proposition_one_off_bound`) and
`𝔄 ≤ L^{-η²ρ + (16d+28)(w+1)}` (the `rough96` argument, with `DamagedShape` instead of `FinalShape`), interpolated at
`θ = η³`.  Closing arithmetic: `2(16d+28)η³ ≤ η`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.Mole.AppbAlgorithm WaveTurbulence.FinalCountG8.P101

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- `rough96` for a `DamagedShape`/`DamagedDec`. -/
theorem rough96D (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1 - γ)) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ m : ℕ, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∀ C1 ≥ C₀, ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
        (cls : V → Cls) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
        DamagedShape M cls → DamagedDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal
          (L ^ (-η ^ 2 * (M.rho : ℝ) + (16 * (d : ℝ) + 28) * (((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) + 1))) := by
  classical
  obtain ⟨C₀, hC₀, h⟩ := dh23_prop_10_2.{v, u} d hd γ η hγ hη hηγ hηs 2 (by norm_num)
  refine ⟨C₀, hC₀, fun m δ hδ C1 hC1 => ?_⟩
  obtain ⟨L₀, hL₀⟩ := h m δ hδ C1 hC1
  refine ⟨max L₀ 1, le_max_right _ _, fun L hL V D _ _ _ M cls Adm P hS hF hsz hP hMA => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLL : L ≥ L₀ := le_trans (le_max_left _ _) hL
  have hLp : 0 < L := by linarith
  have hM : M.IsMolecule := hS.isMolecule
  set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
  refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
  have heq : MoleProp.countAFree M L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧
      CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ) P' =
      MoleProp.countAFree M L γ δ C1 (0 : Mom d) (sgAdm M L Adm P) (cellScale M P') := by
    unfold MoleProp.countAFree
    rw [cellProduct_cellScale]
    congr 2
    refine countEFree_congr M L γ δ 0 _ _ fun κ hκ => ?_
    exact ⟨fun h => ⟨h, hκ⟩, fun h => h.1⟩
  rw [heq]
  by_cases hex : ∃ κ0, sgAdm M L Adm P κ0
  swap
  · push Not at hex
    have : MoleProp.countAFree M L γ δ C1 (0 : Mom d) (sgAdm M L Adm P) (cellScale M P') = 0 := by
      unfold MoleProp.countAFree
      rw [countEFree_eq_zero M L γ δ 0 _ fun κ _ => hex κ]
      simp
    rw [this]; exact bot_le
  obtain ⟨κ0, hκ0⟩ := hex
  have hsub : (nonEps M.atoms cls) ⊆ M.atoms.filter (fun a => M.deg a ≠ 4) := by
    intro a ha
    obtain ⟨h1, h2⟩ := mem_filter.mp ha
    refine mem_filter.mpr ⟨h1, ?_⟩
    have := hS.abLow a h1 h2
    omega
  let wn : ℕ := (M.atoms.filter fun a => M.deg a ≠ 4).card
  let pSG : ProblemSG.{v, u} V d L 0 2 (L ^ (-γ + η)) wn :=
    { state := ofMolecule M
      admissible := sgAdm M L Adm P
      scales := cellScale M P'
      molecule := hM
      noLoops := hS.noLoop
      scales_nonneg := pf_nonneg M P' (fun S _ => hP _)
      validLinkScales := sgAdm_valid M hL1 Adm P hκ0
      mateLabels := fun κ h x => h.2 x
      largeGap := fun κ hκ => ⟨nonEps M.atoms cls, by intro a ha; exact (mem_filter.mp ha).1,
        (card_le_card hsub), by
          intro v hv hvS x hx y hy hxy _
          have hε : (cls v).IsEps := by
            by_contra hne
            exact hvS (mem_filter.mpr ⟨hv, hne⟩)
          exact (hF.epsLG κ hκ.1.1 v hv hε x y ((Mole.mem_dartsAt M v x).mp hx) ((Mole.mem_dartsAt M v y).mp hy) hxy).le⟩ }
  have hb := ((hL₀ V 0 L hLL).2 wn pSG ⟨fun a _ b _ _ => hS.noTriple a b, hsz⟩ hS.conn hS.nonempty le_rfl)
  have hrho : sourceRho (pSG.state.graph) = M.rho := (rho_eq_sourceRho M).symm
  rw [hrho] at hb
  exact hb

/-- `PMol` for an imperfect component, protected set the `α`/`β`-atoms. -/
theorem pmol_damaged {M : Molecule V D} {cls : V → Cls} (hS : DamagedShape M cls) :
    PMol (nonEps M.atoms cls) M := by
  classical
  obtain ⟨u, hu, hu'⟩ := hS.imperf
  refine ⟨hS.isMolecule.1, fun v hv hvB => ?_, fun v hv => ⟨u, hu, hS.conn v hv u hu, ?_⟩⟩
  · exact hS.abLow v hv (mem_filter.mp hvB).2
  · unfold cap
    by_cases huB : u ∈ nonEps M.atoms cls
    · rw [if_pos huB]
      have h2 := (mem_filter.mp huB).2
      rcases hu' with h | h
      · exact absurd h.1 h2
      · exact h.2
    · rw [if_neg huB]
      have h2 : (cls u).IsEps := by
        by_contra hne; exact huB (mem_filter.mpr ⟨hu, hne⟩)
      rcases hu' with h | h
      · exact h.2
      · exact absurd h2 h.1

open Classical in
theorem damagedRHS_ge (M : Molecule V D) (cls : V → Cls) {L γ η : ℝ} (hL : 1 ≤ L) (hη : 0 ≤ η)
    (hlab : ∀ a ∈ M.atoms, (cls a).IsAlpha → L⁻¹ ≤ (cls a).lab ∧ (cls a).lab ≤ L ^ (-γ + η)) :
    L ^ (((alphaAtoms M.atoms cls).card : ℝ) * ((γ - 5 * η) / 2) +
      (min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ) +
      (-(η ^ 5) * (M.rho : ℝ) + η * (epsDefect M cls : ℝ))) ≤ damagedRHS M cls L γ η := by
  have hL0 : 0 < L := by linarith
  unfold damagedRHS
  simp only []
  rw [Real.rpow_add hL0, Real.rpow_add hL0]
  have h := alphaProd_ge M cls hL hη hlab
  have h1 := Real.rpow_nonneg hL0.le ((min γ (1 - γ) + 2 * η ^ 2) * ((betaAtoms M.atoms cls).card : ℝ))
  have h2 := Real.rpow_nonneg hL0.le (-(η ^ 5) * (M.rho : ℝ) + η * (epsDefect M cls : ℝ))
  have hnn : 0 ≤ ∏ v ∈ alphaAtoms M.atoms cls, (L ^ (-(γ + 3 * η) / 2 + ((cls v).kap : ℝ) * η) * ((cls v).lab)⁻¹) := by
    refine Finset.prod_nonneg fun v hv => ?_
    have hv' := mem_filter.mp hv
    have := hlab v hv'.1 hv'.2
    exact mul_nonneg (Real.rpow_nonneg hL0.le _) (inv_nonneg.mpr ((inv_pos.mpr hL0).le.trans this.1))
  exact mul_le_mul (mul_le_mul h le_rfl h1 hnn) le_rfl h2 (mul_nonneg hnn h1)

/-- The exponent arithmetic of the interpolation at `θ = η³`. -/
theorem damaged_arith {η γ γ0 ρ Va Vb Z w K : ℝ} (hη : 0 < η) (hK : 2 * K * η ^ 2 ≤ 1) (hK0 : 0 ≤ K)
    (hγ : 7 * η ≤ γ) (hγ0 : η ≤ γ0) (hVa : 0 ≤ Va) (hVb : 0 ≤ Vb) (hw1 : 1 ≤ w)
    (hw : w ≤ Va + Vb + Z) :
    η ^ 3 * (-η ^ 2 * ρ + K * (w + 1)) + (1 - η ^ 3) * 0 ≤
      Va * ((γ - 5 * η) / 2) + (γ0 + 2 * η ^ 2) * Vb + (-(η ^ 5) * ρ + η * Z) := by
  have h1 : K * (w + 1) ≤ 2 * K * w := by nlinarith
  have h2 : η ^ 3 * (K * (w + 1)) ≤ η ^ 3 * (2 * K * w) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : η ^ 3 * (2 * K * w) ≤ η * w := by
    have : η ^ 3 * (2 * K * w) = η * w * (2 * K * η ^ 2) := by ring
    rw [this]
    nlinarith [mul_pos hη (by linarith : (0 : ℝ) < w)]
  have h4 : η * w ≤ η * (Va + Vb + Z) := mul_le_mul_of_nonneg_left hw hη.le
  have h5 : η * Va ≤ Va * ((γ - 5 * η) / 2) := by nlinarith
  have h6 : η * Vb ≤ (γ0 + 2 * η ^ 2) * Vb := by nlinarith [sq_nonneg η]
  have e : η ^ 3 * (-η ^ 2 * ρ + K * (w + 1)) + (1 - η ^ 3) * 0 =
      -(η ^ 5) * ρ + η ^ 3 * (K * (w + 1)) := by ring
  rw [e]
  nlinarith [h2, h3, h4, h5, h6]

end

/-- **DCB**: `Prop96DamagedAt` for `d ≥ 3`, `0 < γ < 1`, under `d η ≤ min γ (1-γ)/1000` and `4·1440061 η ≤ 1`. -/
theorem prop96_damaged (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    Prop96DamagedAt.{u, v} d γ η := by
  classical
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < min γ (1 - γ) := lt_min hγ.1 (by linarith [hγ.2])
  have hmγ : min γ (1 - γ) ≤ γ := min_le_left _ _
  have hm12 : min γ (1 - γ) ≤ 1 / 2 := by
    rcases le_total γ (1 - γ) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith [hγ.1]
  have hηm : η ≤ min γ (1 - γ) / 1000 := by nlinarith
  have hηγ : η ≤ min γ (1 - γ) := by linarith
  have hηmax : η ≤ min γ (1 - γ) / 2 := by linarith
  obtain ⟨C₀, hC₀, hrough⟩ := rough96D.{u, v} d hd γ η hγ hη hηγ hηs
  obtain ⟨Cs, hCs, hP1⟩ := proposition_one_off_bound.{u, v} d hd γ hγ η hη hηmax
  refine ⟨max C₀ Cs, le_trans hC₀ (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨L₀, hL₀1, hL₀⟩ := hrough m δ hδ C1 ((le_max_left _ _).trans hC1)
  obtain ⟨Rp, hRp⟩ := hP1 C1 ((le_max_right _ _).trans hC1) δ hδ
  refine ⟨max (max L₀ Rp) (Real.exp 1), ?_⟩
  intro L hL V D _ _ _ M cls Adm P hS hF hsz hP hMA
  have hLL₀ : L₀ ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLRp : Rp ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hLp : 0 < L := by linarith
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hM : M.IsMolecule := hS.isMolecule
  have hA2 := hL₀ L hLL₀ M cls Adm P hS hF hsz hP hMA
  have hθ0 : 0 ≤ η ^ 3 := by positivity
  have hη1 : η ≤ 1 := by nlinarith
  have hθ1 : η ^ 3 ≤ 1 := pow_le_one₀ hη.le hη1
  have hPM := pmol_damaged hS
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
  refine le_trans ?_ (damagedRHS_ge M cls hL1 hη.le hF.labRange)
  refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
  have hcard : (M.atoms.filter fun a => M.deg a ≠ 4).card ≤
      (alphaAtoms M.atoms cls).card + (betaAtoms M.atoms cls).card + epsDefect M cls := by
    rw [← card_nonEps]
    unfold epsDefect
    refine le_trans (card_le_card ?_) (card_union_le _ _)
    intro a ha
    obtain ⟨h1, h2⟩ := mem_filter.mp ha
    by_cases he : (cls a).IsEps
    · exact mem_union_right _ (mem_filter.mpr ⟨h1, he, h2⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨h1, he⟩)
  have hw1 : 1 ≤ (M.atoms.filter fun a => M.deg a ≠ 4).card := by
    obtain ⟨u, hu, hu'⟩ := hS.imperf
    refine card_pos.mpr ⟨u, mem_filter.mpr ⟨hu, ?_⟩⟩
    rcases hu' with h | h
    · exact h.2
    · have := hS.abLow u hu h.1; omega
  have hcR : ((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ) ≤
      ((alphaAtoms M.atoms cls).card : ℝ) + ((betaAtoms M.atoms cls).card : ℝ) + (epsDefect M cls : ℝ) := by
    exact_mod_cast hcard
  have hdη : (d : ℝ) * η ≤ 1 / 2000 := by linarith
  have hK : 2 * (16 * (d : ℝ) + 28) * η ^ 2 ≤ 1 := by
    have h1 : 2 * (16 * (d : ℝ) + 28) * η ^ 2 = 2 * η * (16 * ((d : ℝ) * η) + 28 * η) := by ring
    rw [h1]
    have h2 : 16 * ((d : ℝ) * η) + 28 * η ≤ 1 := by nlinarith
    have h3 : 2 * η ≤ 1 := by linarith
    have h4 : 0 ≤ 16 * ((d : ℝ) * η) + 28 * η := by positivity
    nlinarith
  have := damaged_arith (η := η) (γ := γ) (γ0 := min γ (1 - γ)) (ρ := (M.rho : ℝ))
    (Va := ((alphaAtoms M.atoms cls).card : ℝ)) (Vb := ((betaAtoms M.atoms cls).card : ℝ))
    (Z := (epsDefect M cls : ℝ)) (w := ((M.atoms.filter fun a => M.deg a ≠ 4).card : ℝ))
    (K := 16 * (d : ℝ) + 28) hη hK (by positivity) (by nlinarith) hηγ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast hw1) hcR
  linarith

end WaveTurbulence.FinalCountG8
