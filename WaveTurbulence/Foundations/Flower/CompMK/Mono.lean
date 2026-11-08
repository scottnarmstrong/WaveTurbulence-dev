/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Defs
public import WaveTurbulence.Foundations.Spine.SpliceGateMonotone
public import WaveTurbulence.Foundations.Spine.Stage1GateMonotone

/-! # C5b COMP-MK: large-constant monotonicity (to combine the inputs through main's `prefix_and`)

Enlarging `C₁, C₂` only weakens the right sides of the marked gates and the mass bound and class counts of the
B4 gate; carriers, `SoundMKFull` and the selections read only `N, R, L, γ, η, d`. (Main's `Stage1GateMonotone` and
`SpliceGateMonotone`, for the marked statements.) -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

namespace WaveTurbulence.Flower.CompMK

theorem coarseSplicedAtMK_largeConstantMonotone : LargeConstantMonotone CoarseSplicedAtMK := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirr hbal hn hnmax D split cθ hcθ hD hlayer hatom
    hfix A base roots hgeom
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirr hbal hn hnmax D split cθ hcθ hD hlayer hatom hfix A base roots hgeom
  refine h0.trans ?_
  have hc1 : 0 ≤ P.C₁ := by linarith
  have hδ0 : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hL0 : 0 ≤ P.L := by linarith
  have hb : 0 ≤ cθ * P.C₁ * Real.sqrt P.δ := by positivity
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL0 _)
  exact mul_le_mul h₂ (pow_le_pow_left₀ hb (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h₁ (by linarith)) hδ0) _) (pow_nonneg hb _) (by linarith)

theorem fineSplicedHalfMK_largeConstantMonotone :
    LargeConstantMonotone (fun P => 1 / 2 < P.γ → FineSplicedAtMK P) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h hγ p hp R hR hRmax G hplain hirr hbal hn hnmax D Cs S E hD hlayer hfilt hind
    hfixE hfixT hlbE base roots hgeom hconc
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h hγ p hp R hR hRmax G hplain hirr hbal hn hnmax D Cs S E hD hlayer hfilt hind hfixE hfixT hlbE base
    roots hgeom hconc
  refine h0.trans ?_
  have hc1 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have hδ0 : 0 ≤ P.δ ^ (-10 * P.ν) := Real.rpow_nonneg hδ.le _
  have hrest : 0 ≤ P.L ^ (2 * (S.m : ℝ)) * (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
      P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) := by
    positivity
  have hmono : P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order ≤ c₁ * (c₁ * P.δ ^ (-10 * P.ν)) ^ G.order :=
    mul_le_mul h₁ (pow_le_pow_left₀ (mul_nonneg hc1 hδ0) (mul_le_mul_of_nonneg_right h₁ hδ0) _)
      (pow_nonneg (mul_nonneg hc1 hδ0) _) (by linarith)
  calc P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order * P.L ^ (2 * (S.m : ℝ)) *
        (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))
      = (P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ G.order) * (P.L ^ (2 * (S.m : ℝ)) *
        (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))) := by
        ring
    _ ≤ (c₁ * (c₁ * P.δ ^ (-10 * P.ν)) ^ G.order) * (P.L ^ (2 * (S.m : ℝ)) *
        (((G.order : ℝ) + 1) * P.L) ^ ((5 * P.d + 4) * E.card) *
        P.L ^ (-P.η ^ 6 * (G.molecule.rho + D.hinges.card)) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50))) :=
        mul_le_mul_of_nonneg_right hmono hrest
    _ = _ := by ring

theorem ladderFourierAtMKFace_largeConstantMonotone : LargeConstantMonotone LadderFourierAtMKFace := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h p hp R hR hRmax G hplain hirr hbal hn hnmax D fix face E scales hlayer hD
    hfixE hfixT hface hface1 base roots β
  rw [N_largeConstants] at hnmax
  rw [R_largeConstants] at hRmax
  have h0 := h p hp R hR hRmax G hplain hirr hbal hn hnmax D fix face E scales hlayer hD hfixE hfixT hface hface1
    base roots β
  refine h0.trans ?_
  have hc1 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have hδ0 : 0 ≤ P.δ ^ (-1 / 2 - 5 * P.ν) := Real.rpow_nonneg hδ.le _
  have hpow := Real.rpow_nonneg hL0 (P.δ ^ (5 * P.ν) * (G.molecule.rho : ℝ))
  have hQ : 0 ≤ (((G.order : ℝ) + 1) * P.L) ^ (4 * E.card) := by positivity
  simp only [← mul_assoc]
  apply ofReal_mul_mono_any (by positivity)
  apply mul_le_mul_of_nonneg_right _ hpow
  rw [mul_assoc _ P.C₁, mul_assoc _ c₁]
  apply mul_le_mul_of_nonneg_left _ hQ
  exact mul_le_mul h₁ (pow_le_pow_left₀ (mul_nonneg hc1 hδ0) (mul_le_mul_of_nonneg_right h₁ hδ0) _)
    (pow_nonneg (mul_nonneg hc1 hδ0) _) (by linarith)

theorem representsIntMKSel_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (hc : P.C₁ ≤ c₁) (h0 : 0 ≤ P.C₁)
    (hL : 0 ≤ P.L) (π : Stage1PieceMK P.d R) (sel : Finset (GBranch π.Gsb.tree)) (n : ℕ) (cP : ℝ)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : 0 ≤ s) (val : ℂ)
    (h : RepresentsIntMKSel π sel n cP tt base roots s val) :
    RepresentsIntMKSel (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π sel n cP tt base roots s val := by
  obtain ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb, hD⟩ := h
  refine ⟨Ξ, hm, μ, w, ctr, edge, hinge, freq, hint, hv, hwint, hwb.trans ?_, hD⟩
  have hsq : 0 ≤ Real.sqrt P.δ := Real.sqrt_nonneg _
  have hpow : (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) :=
    pow_le_pow_left₀ (mul_nonneg h0 hsq) (mul_le_mul_of_nonneg_right hc hsq) _
  have hpow2 : P.C₁ ^ (π.Gsb.order + 2 * R) ≤ c₁ ^ (π.Gsb.order + 2 * R) := pow_le_pow_left₀ h0 hc _
  have hB : 0 ≤ (c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) := pow_nonneg (mul_nonneg (h0.trans hc) hsq) _
  have hC : 0 ≤ P.C₁ ^ (π.Gsb.order + 2 * R) := pow_nonneg h0 _
  have hAC := mul_le_mul hpow hpow2 hC hB
  have hrest : 0 ≤ P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) +
        P.η ^ 7 * (π.Cs.hinges.card : ℝ)) * P.L ^ (cP * P.d * (π.nProt : ℝ)) *
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s := by positivity
  calc (P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R) *
        P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s
      = ((P.C₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * P.C₁ ^ (π.Gsb.order + 2 * R)) *
        (P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s) := by ring
    _ ≤ ((c₁ * Real.sqrt P.δ) ^ (n - π.Gsb.order) * c₁ ^ (π.Gsb.order + 2 * R)) *
        (P.L ^ (-P.η ^ 8 * (π.gsk : ℝ) - P.η ^ 2 / 2 * (π.bsk : ℝ) + P.η ^ 7 * (π.Cs.hinges.card : ℝ)) *
        P.L ^ (cP * P.d * (π.nProt : ℝ)) * P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s) :=
        mul_le_mul_of_nonneg_right hAC hrest
    _ = _ := by ring

theorem soundMKFull_largeConstants {P : WTParams} {R : ℕ} (c₁ c₂ : ℝ) (π : Stage1PieceMK P.d R) (p : ℕ)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (cθ : ℝ) (h : SoundMKFull π p base roots cθ) :
    SoundMKFull (P := ({P with C₁ := c₁, C₂ := c₂} : WTParams)) π p base roots cθ :=
  { plain := h.plain, irreducible := h.irreducible, balanced := h.balanced, order_pos := h.order_pos,
    order_le := by rw [N_largeConstants]; exact h.order_le, layer_le := h.layer_le, survivors := h.survivors,
    survivors_card := h.survivors_card, prot_card := h.prot_card,
    molecule := h.molecule, connected := h.connected, atom_count := h.atom_count, bond_count := h.bond_count,
    structural := h.structural, support := h.support, hingeOutsideFirst := h.hingeOutsideFirst,
    tripleDesignated := h.tripleDesignated, hingeNoLoop := h.hingeNoLoop, chainOrder := h.chainOrder,
    fix_prot := h.fix_prot, fix_layer := h.fix_layer, filt_ok := h.filt_ok, ind_ok := h.ind_ok,
    ind_local := h.ind_local, lb_free := h.lb_free, lb_prot := h.lb_prot, lb_layer := h.lb_layer }

theorem mkCarries_largeConstants {P : WTParams} (c₁ c₂ : ℝ) {p n w : ℕ} {LG : LayeredGarden w}
    (h : MkCarries ({P with C₁ := c₁, C₂ := c₂} : WTParams) p n LG) : MkCarries P p n LG := by
  simpa only [MkCarries, N_largeConstants] using h

theorem selMass_nonneg {R : ℕ} (N : ℕ) {b : ℝ} (hb : 0 ≤ b) {Rs : Fin (2 * R) → ℝ} (hRs : ∀ j, 0 ≤ Rs j)
    (kSel : Fin (2 * R) → Option ℕ) (U : Finset (Fin (2 * R))) : 0 ≤ selMass N b Rs kSel U := by
  unfold selMass
  refine mul_nonneg (pow_nonneg hb _) (Finset.prod_nonneg fun j _ => ?_)
  split_ifs
  · exact mul_nonneg (inv_nonneg.2 (hRs j)) zero_le_one
  · exact mul_nonneg (inv_nonneg.2 (hRs j)) (Real.rpow_nonneg (hRs j) _)
  · exact zero_le_one

theorem stage1ReductionAtMKSel_largeConstantMonotone (C₀ : ℕ) (cP cθ : ℝ) :
    LargeConstantMonotone (Stage1ReductionAtMKSel C₀ cP cθ) := by
  intro P c₁ c₂ hC hC₂ hδ hL h₁ h₂ h
  intro p hp R hR hRmax N hN1 hN J hJ pat kSel t ht s hs A hA hplain hTC roots hh b Rf σ Rs dag hb hhb hRf hRs
    hhigh
  rw [R_largeConstants] at hRmax
  rw [N_largeConstants] at hN
  obtain ⟨S, Cl, hCl, cls, members, sel, selR, hpart, hpc, hsound, hord, hcounts⟩ :=
    h p hp R hR hRmax N hN1 hN J hJ pat kSel t ht s hs A
      (fun LG hLG => ⟨mkCarries_largeConstants c₁ c₂ (hA LG hLG).1, (hA LG hLG).2⟩) hplain hTC roots hh b Rf σ Rs
      dag hb hhb hRf hRs hhigh
  refine ⟨⟨S.Pc, S.fin, S.piece, S.val⟩, Cl, hCl, cls, members, sel, selR, hpart, fun π => ?_,
    fun π => soundMKFull_largeConstants c₁ c₂ (S.piece π) p 0 roots cθ (hsound π), hord, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hpc π
    have hL0 : (0 : ℝ) ≤ P.L := by linarith
    refine ⟨h1, representsIntMKSel_largeConstants c₁ c₂ h₁ (by linarith) hL0 (S.piece π) (selR π) N cP _ 0 roots
      _ (selMass_nonneg N (by linarith) (fun j => by linarith [hRs j]) kSel _) (S.val π) h2, h3, h4, h5, h6⟩
  · obtain ⟨hr, hg, hcnt⟩ := hcounts
    refine ⟨hr, hg, fun g r => (hcnt g r).trans ?_⟩
    have hC₂0 : 0 ≤ P.C₂ := by linarith
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC₂0 h₂ _) (by positivity)

end WaveTurbulence.Flower.CompMK
