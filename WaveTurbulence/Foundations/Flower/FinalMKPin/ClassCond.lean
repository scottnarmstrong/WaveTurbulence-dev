/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.RungCount
public import WaveTurbulence.Foundations.Flower.FinalMKPin.Arith
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the class condition on the clocks

`class_condI` is main's `class_cond` (Final3f) for the face domain: the class integral times `#Sigs · 2^{4|Iv|}` is at
most `C₁ ((C₁ δ^{-1/2-5ν})^n Lam^ρ ∏ ladderWeight^{len}) (Lam Λ²)^{|E₀|}`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LadderDisjoint
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ} {G : Garden w}
variable {fix : GBranch G.tree → Option ℝ} {face : GBranch G.tree → Option (GBranch G.tree)}

/-- The class bound (real form). -/
noncomputable def TrMK (G : Garden w) (scales : Finset (GBranch G.tree) → ℝ) (L γ δ ν Lam C1 : ℝ) (e0 : ℕ) : ℝ :=
  C1 * ((C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * Lam ^ G.molecule.rho *
    (∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S) *
    (Lam * Real.log L ^ 2) ^ e0)

/-- The arithmetic of one class (main's `class_real_ineq`, the ladder part). -/
theorem arith_classI {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d) {hp : G.IsPlain}
    (scales : Finset (GBranch G.tree) → ℝ) (γ δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ν : ℝ) (hν : 0 ≤ ν)
    {base : Mom d} {roots : Fin w → (Fin d → ℤ)} (Dt Lam C1 : ℝ) (hDt0 : 0 ≤ Dt)
    (hΛ : 1 ≤ Real.log L) (hbig : Real.log L ^ 2 < 1 + δ * L ^ (2 * γ))
    (hY : 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) ≤ 180 * d * Real.log L)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4) ≤ Lam)
    (hΛLam : (Real.log L) ^ 2 ≤ Lam) (hfree : 256 * (180 * d * Real.log L) ≤ Lam)
    (hC : 256 * (180 * d) * (64 * (1 + d * (2 : ℝ) ^ (d - 1))) ≤ C1) (hC1 : 1 ≤ C1) (hd1 : 1 ≤ d)
    (π0 : PF G) (hP0 : ∀ S : LQ G, 0 ≤ scales S.1) (hP1 : ∀ S : LQ G, scales S.1 ≤ 1)
    (cd : CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1)) :
    (∏ S : LQ G, ∏ k : Fin (π0.m S + 1), (8 * rhoS d L γ δ (scales S.1) * Dt) ^
        (Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩) /
        (Nat.factorial (Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩) : ℝ)) * 256 ^ G.order *
      (3 * (2 * (2 * Real.arsinh (Mv d L) + 1))) ^
        (G.order - ∑ S : LQ G, ∑ k : Fin (π0.m S + 1), Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩) ≤
      (C1 * δ ^ (-1 / 2 - 5 * ν)) ^ G.order * Lam ^ G.molecule.rho *
        (∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S) *
        (Lam * Real.log L ^ 2) ^ (E0 fix face).card := by
  have hJS := cd_hJS cd (smallP scales L γ δ)
  have hc : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ.le (Real.rpow_nonneg hL.le _)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have ha1 : 1 ≤ 1 + d * (2 : ℝ) ^ (d - 1) := by
    have : (0 : ℝ) ≤ d * (2 : ℝ) ^ (d - 1) := by positivity
    linarith
  have harsinh : 0 ≤ Real.arsinh (Mv d L) :=
    Real.arsinh_nonneg_iff.mpr (by linarith [one_le_Mv d hL.le])
  have hY1 : 1 ≤ 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) := by linarith
  have hn' : G.order = G.molecule.numFree + ∑ S : LQ G, (2 * π0.m S + 2) := by
    rw [card_atoms_decomp G]
    congr 1
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have := ladderAtoms_card (π0.ladder S).2.1
    rw [π0.atoms S] at this; omega
  have hKq0 : ∀ S, ¬ smallP scales L γ δ S → ∀ k, Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩ = 0 := by
    intro S hS k
    have h0 := cd.Kn_zero (smallP scales L γ δ) S hS
    unfold CD.Kn at h0
    have : Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩ ≤ (cd.JS (smallP scales L γ δ) S).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    omega
  have hKs : ∀ S, smallP scales L γ δ S → π0.m S ≤
      (∑ k : Fin (π0.m S + 1), Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩) + d + 1 + hS fix face π0 S := by
    intro S hS
    have h1 := cd.m_le_Kn (smallP scales L γ δ) S hS
    have h2 := card_JS_le (fix := fix) (face := face) hJS S
    unfold CD.Kn at h1
    omega
  have harith := arith_totalMK (fun S : LQ G => π0.m S)
    (fun S k => Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩) (hS fix face π0) (smallP scales L γ δ)
    (fun S => Molecule.ladderWeight L γ δ (scales S.1)) (fun S => rhoS d L γ δ (scales S.1))
    G.molecule.numFree G.order d (δ := δ) (ν := ν) (Dt := Dt) (Y := 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)))
    (Λ := Real.log L) (a := 1 + d * (2 : ℝ) ^ (d - 1)) (dR := (d : ℝ)) (Lam := Lam) (C1 := C1)
    hn' (fun S => sum_Kq_le hJS S) hKs hKq0 (fun S => card_seg_nonzero_le hJS S)
    (fun S hS => by
      rw [lw_small hS.2]
      have := mul_nonneg hc (hP0 S)
      linarith)
    (fun S => by unfold rhoS; positivity)
    (fun S hS => by
      rw [lw_small hS.2]
      exact rhoS_le rfl hc (hP0 S) ha1)
    (fun S hS => lw_large (hP1 S) (hP0 S) hbig hc hS)
    hΛ hδ hδ1 hν hDt0 hY1 hY ha1 hdR hexp hΛLam hfree hC hC1
  have hrho : Fintype.card (LQ G) + G.molecule.numFree = G.molecule.rho := by
    unfold Molecule.rho Molecule.numLadders; simp
  have hprod : ∏ S : LQ G, Molecule.ladderWeight L γ δ (scales S.1) ^ (π0.m S) =
      ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S := by
    rw [← Finset.prod_coe_sort G.molecule.maximalLadders]
    refine Finset.prod_congr rfl (fun S _ => ?_)
    rw [π0.m_eq_ladderLength S]
  rw [hrho, hprod] at harith
  have hLam1 : 1 ≤ Lam := le_trans (by nlinarith) hΛLam
  have hLL : 1 ≤ Lam * Real.log L ^ 2 := by nlinarith
  have hE0 : (Lam * Real.log L ^ 2) ^ (∑ S : LQ G, hS fix face π0 S) ≤
      (Lam * Real.log L ^ 2) ^ (E0 fix face).card := pow_le_pow_right₀ hLL sum_hS_le
  have hw : 0 ≤ ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S := by
    apply Finset.prod_nonneg
    intro S hS
    apply pow_nonneg
    unfold Molecule.ladderWeight
    apply le_min (sq_nonneg _)
    have := mul_nonneg hc (hP0 ⟨S, hS⟩)
    linarith
  have hDl1 := one_le_Dl hδ hδ1 hν
  have hC0 : 0 ≤ C1 := by linarith
  refine harith.trans (mul_le_mul_of_nonneg_left hE0 ?_)
  have : 0 ≤ Lam := by linarith
  positivity

/-- The real class inequality (main's `class_real_ineq` with `16^{|Iv|}`). -/
theorem class_real_ineqI {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d) {hp : G.IsPlain}
    (scales : Finset (GBranch G.tree) → ℝ) (γ δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ν : ℝ) (hν : 0 ≤ ν)
    {base : Mom d} {roots : Fin w → (Fin d → ℤ)} (Dt Lam C1 : ℝ) (hDt0 : 0 ≤ Dt)
    (hΛ : 1 ≤ Real.log L) (hbig : Real.log L ^ 2 < 1 + δ * L ^ (2 * γ))
    (hY : 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) ≤ 180 * d * Real.log L)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4) ≤ Lam)
    (hΛLam : (Real.log L) ^ 2 ≤ Lam) (hfree : 256 * (180 * d * Real.log L) ≤ Lam)
    (hC : 256 * (180 * d) * (64 * (1 + d * (2 : ℝ) ^ (d - 1))) ≤ C1) (hC1 : 1 ≤ C1) (hd1 : 1 ≤ d)
    (π0 : PF G) (hP0 : ∀ S : LQ G, 0 ≤ scales S.1) (hP1 : ∀ S : LQ G, scales S.1 ≤ 1)
    (cd : CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1)) :
    ((Sigs G).card : ℝ) * 16 ^ Fintype.card (Iv fix face) *
      ((∏ q : SegQ π0, (8 * rhoS d L γ δ (scales q.1.1) * Dt) ^ (Kq fix face π0 (cd.JS (smallP scales L γ δ)) q) /
          (Nat.factorial (Kq fix face π0 (cd.JS (smallP scales L γ δ)) q) : ℝ)) *
        Real.pi ^ Fintype.card (Iv fix face) *
        (3 * (2 * (2 * Real.arsinh (Mv d L) + 1))) ^
          (Fintype.card (Iv fix face) - Fintype.card (Jr (Kq fix face π0 (cd.JS (smallP scales L γ δ)))))) ≤
      TrMK G scales L γ δ ν Lam C1 (E0 fix face).card := by
  have harith := arith_classI (fix := fix) (face := face) hL D scales γ δ hδ hδ1 ν hν Dt Lam C1 hDt0 hΛ hbig hY
    hexp hΛLam hfree hC hC1 hd1 π0 hP0 hP1 cd
  have hc : 0 ≤ δ * L ^ (2 * γ) := mul_nonneg hδ.le (Real.rpow_nonneg hL.le _)
  have harsinh : 0 ≤ Real.arsinh (Mv d L) :=
    Real.arsinh_nonneg_iff.mpr (by linarith [one_le_Mv d hL.le])
  have hY1 : 1 ≤ 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) := by linarith
  have hcardJ : Fintype.card (Jr (Kq fix face π0 (cd.JS (smallP scales L γ δ)))) =
      ∑ S : LQ G, ∑ k : Fin (π0.m S + 1), Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩ := by
    rw [Fintype.card_sigma, Fintype.sum_sigma]; simp only [Fintype.card_fin]
  have hιn : Fintype.card (Iv fix face) ≤ G.order := by
    rw [← card_branch_eq G]; exact Fintype.card_subtype_le _
  have hLam1 : 1 ≤ Lam := le_trans (by nlinarith) hΛLam
  have hDl1 := one_le_Dl hδ hδ1 hν
  have hC0 : 0 ≤ C1 := by linarith
  have hw : 0 ≤ ∏ S ∈ G.molecule.maximalLadders, Molecule.ladderWeight L γ δ (scales S) ^ Molecule.ladderLength S := by
    apply Finset.prod_nonneg
    intro S hS
    apply pow_nonneg
    unfold Molecule.ladderWeight
    apply le_min (sq_nonneg _)
    have := mul_nonneg hc (hP0 ⟨S, hS⟩)
    linarith
  unfold TrMK
  refine combine_realMK (n := G.order)
    (m' := G.order - ∑ S : LQ G, ∑ k : Fin (π0.m S + 1), Kq fix face π0 (cd.JS (smallP scales L γ δ)) ⟨S, k⟩)
    (by exact_mod_cast Sigs_card_le G) (by positivity)
    (Finset.prod_nonneg (fun q _ => by
      have : 0 ≤ rhoS d L γ δ (scales q.1.1) := by unfold rhoS; positivity
      positivity)) hY1 hιn (by rw [hcardJ]; omega) ?_ hC1 (by positivity)
  rw [Fintype.prod_sigma]
  exact harith

theorem class_condI (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d)
    (hamp : SplicedAmplitudeBounds G D) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ν : ℝ) (hν : 0 ≤ ν) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (hF : FaceOK fix face) (β : GBranch G.tree → ℝ)
    (Dt Lam C1 : ℝ) (hDt0 : 0 ≤ Dt) (hDt : ∀ v, (D.layer v : ℝ) + 2 ≤ Dt)
    (hΛ : 1 ≤ Real.log L) (hbig : Real.log L ^ 2 < 1 + δ * L ^ (2 * γ))
    (hY : 3 * (2 * (2 * Real.arsinh (Mv d L) + 1)) ≤ 180 * d * Real.log L)
    (hexp : Real.exp (Dt * δ ^ (1 + 10 * ν) * Real.log L) * (Real.log L) ^ (2 * d + 4) ≤ Lam)
    (hΛLam : (Real.log L) ^ 2 ≤ Lam) (hfree : 256 * (180 * d * Real.log L) ≤ Lam)
    (hC : 256 * (180 * d) * (64 * (1 + d * (2 : ℝ) ^ (d - 1))) ≤ C1) (hC1 : 1 ≤ C1) (hd1 : 1 ≤ d)
    (π0 : PF G) (A : Finset (Iv fix face)) :
    ((Sigs G).card : ℝ≥0∞) * 2 ^ (4 * Fintype.card (Iv fix face)) *
        ∫⁻ α in Wnb (clsI D scales L γ η δ base roots π0 fix face β),
          ‖Phi (Om0 (chF fix face) (lsF D.layer fix face) (capF D.layer D.rootTime fix face))
            (lsF D.layer fix face) A α‖ₑ ≤
      ENNReal.ofReal (TrMK G scales L γ δ ν Lam C1 (E0 fix face).card) := by
  by_cases hne : (clsI D scales L γ η δ base roots π0 fix face β).Nonempty
  swap
  · have : Wnb (clsI D scales L γ η δ base roots π0 fix face β) = ∅ := by
      rw [Set.not_nonempty_iff_eq_empty] at hne
      ext α; simp [Wnb, hne]
    rw [this]; simp
  obtain ⟨α', α0, hα0, -, -⟩ := hne
  have hP0 : ∀ S : LQ G, 0 ≤ scales S.1 := fun S => scale_nonneg hL.le hα0 S
  have hP1 : ∀ S : LQ G, scales S.1 ≤ 1 := fun S => scale_le_one hα0 S
  obtain ⟨cd⟩ := exists_CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1)
  have hcl := class_fourierI hp hL D hamp scales γ η δ hδ.le base roots π0 cd (smallP scales L γ δ)
    (fun S hS => hS.1) hF β D.layer D.rootTime Dt hDt0 hDt A
  have hKc0 : 0 ≤ 2 * Real.arsinh (Mv d L) + 1 := by
    have : 0 ≤ Real.arsinh (Mv d L) := Real.arsinh_nonneg_iff.mpr (by linarith [one_le_Mv d hL.le])
    linarith
  have hE := class_E_eq (Kq fix face π0 (cd.JS (smallP scales L γ δ)))
    (fun q : SegQ π0 => rhoS d L γ δ (scales q.1.1)) (fun q => by unfold rhoS; positivity)
    Dt (2 * Real.arsinh (Mv d L) + 1) hDt0 hKc0 (Fintype.card (Iv fix face))
  have hbound := hcl.trans (le_of_eq hE)
  have hreal := class_real_ineqI (fix := fix) (face := face) hL D scales γ δ hδ hδ1 ν hν Dt Lam C1 hDt0 hΛ hbig
    hY hexp hΛLam hfree hC hC1 hd1 π0 hP0 hP1 cd
  have hcardE : ((Sigs G).card : ℝ≥0∞) = ENNReal.ofReal ((Sigs G).card : ℝ) :=
    (ENNReal.ofReal_natCast _).symm
  have h16 : (2 : ℝ≥0∞) ^ (4 * Fintype.card (Iv fix face)) = ENNReal.ofReal (16 ^ Fintype.card (Iv fix face)) := by
    rw [pow_mul, ENNReal.ofReal_pow (by norm_num)]; norm_num
  refine (mul_le_mul' le_rfl hbound).trans ?_
  rw [hcardE, h16, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end WaveTurbulence.Flower.FinalMKPin
