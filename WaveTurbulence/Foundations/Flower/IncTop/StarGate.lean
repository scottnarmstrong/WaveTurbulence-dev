/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.IncTop.StarTree
public import WaveTurbulence.Foundations.Flower.IncTop.StarCouple
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.Gate

/-! # INC-TOP: the star-weighted leafwise incoherent decay gate

`starIncoherentDecay : StarIncoherentDecayGate` (C2-B-TOP's star statement layer, ported): main's leafwise B2.2 gate
`LeafwiseIncoherentDecayGate` for kernels carrying arbitrary Fourier-presented star weights on an arbitrary node set
`S`, at the cost `∏_{a ∈ S} c a`.  The proof is main's `IncohLeafwise.leafwiseIncoherentDecay` (Spine/IncohLeafwise/
Gate.lean) with the weighted decays `exists_KQstarStar_decay` / `exists_KTstarStar_decay`; the weight-independent
presentation constant `rootJetConstant (30d)` is absorbed into `C₁` (chosen after `d, γ, η`).

The leafwise normalization (`leafwise_bound_of_normalized`) needs the weighted kernel to be homogeneous in each leaf
profile and to vanish with one leaf profile (`kernelLeavesW_scale`, `kernelLeavesW_zero_of_leaf`): the multiplier
`m` reads only the decoration, so main's proof applies verbatim. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal Classical
namespace WaveTurbulence.Flower.IncTop
open WaveTurbulence.Induct WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise

/-- The weighted kernel with an individual positive bound per leaf: homogeneity of degree one in each leaf
(weighted copy of main's `IncohLeafwise.kernelLeaves_scale`). -/
theorem kernelLeavesW_scale {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (B : (Fin w × TTree.Path) → NNReal) (hB : ∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ))
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m =
      ((leafSizeProduct LG B : ℝ) : ℂ) *
        Stage1W.kernelLeavesW L γ δ LG (fun a x => H a x / (B a : ℝ)) up s k₀ nroot nfl m := by
  unfold Stage1W.kernelLeavesW leafSizeProduct
  have hprod : ∀ x : GNode LG.garden.tree → Mom d,
      ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (x ℓ.toNode) : ℂ) =
        ((∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ) : ℝ) : ℂ) *
          ∏ ℓ ∈ inputLeaves LG.garden, ((H ℓ.1 (x ℓ.toNode) / (B ℓ.1 : ℝ) : ℝ) : ℂ) := by
    intro x
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro ℓ hℓ
    have hne : (B ℓ.1 : ℝ) ≠ 0 := (hB ℓ hℓ).ne'
    push_cast
    have hne' : ((B ℓ.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
    field_simp
  have hsum : ∀ κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) =
      ((∏ ℓ ∈ inputLeaves LG.garden, (B ℓ.1 : ℝ) : ℝ) : ℂ) *
        (m (cosetDecoration LG.garden L k₀ κ.1) *
          ((epsDec LG.garden κ.1 : ℂ) *
            phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
            ∏ ℓ ∈ inputLeaves LG.garden,
              ((H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) / (B ℓ.1 : ℝ) : ℝ) : ℂ))) := by
    intro κ
    rw [hprod]
    ring
  rw [tsum_congr hsum, tsum_mul_left]
  ring

/-- A vanishing leaf profile kills the weighted kernel (weighted `IncohLeafwise.kernelLeaves_zero_of_leaf`). -/
theorem kernelLeavesW_zero_of_leaf {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H : LeafProfiles w d) {ℓ : GLeaf LG.garden.tree} (hℓ : ℓ ∈ inputLeaves LG.garden)
    (h0 : H ℓ.1 = fun _ => 0) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (m : (GNode LG.garden.tree → Mom d) → ℂ) :
    Stage1W.kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = 0 := by
  unfold Stage1W.kernelLeavesW
  have : ∀ κ : GenDecoration LG.garden d nroot nfl,
      m (cosetDecoration LG.garden L k₀ κ.1) *
        ((epsDec LG.garden κ.1 : ℂ) *
          phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
          ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) = 0 := by
    intro κ
    rw [Finset.prod_eq_zero hℓ (by simp [h0]), mul_zero, mul_zero]
  simp [this]

/-- The constant of the gate: dominates the presentation constant and both analytic constants. -/
def starGateConstant (d : ℕ) (Cc Ct : ℝ) : ℝ := max (rootJetConstant (30 * d)) (max 1 (max Cc Ct))

theorem one_le_starGateConstant (d : ℕ) (Cc Ct : ℝ) : 1 ≤ starGateConstant d Cc Ct := by
  unfold starGateConstant
  exact (le_max_left _ _).trans (le_max_right _ _)

/-- `rootJetConstant (30d) · ∏ c · (C δ)^n L^{-…g} ≤ ∏ c · regBound`, once `C, rootJetConstant ≤ C₁`. -/
theorem star_cost_le_regBound (P : WTParams) {C : ℝ} (hC : 0 ≤ C) (hCC : C ≤ P.C₁)
    (hJ : rootJetConstant (30 * P.d) ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) (M : ℝ≥0∞) :
    ENNReal.ofReal (rootJetConstant (30 * P.d)) * M *
        ENNReal.ofReal ((C * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g)) ≤
      M * regBound P n g := by
  rw [mul_comm (ENNReal.ofReal (rootJetConstant (30 * P.d))) M, mul_assoc]
  refine mul_le_mul_right ?_ M
  rw [← ENNReal.ofReal_mul (rootJetConstant_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  change rootJetConstant (30 * P.d) * ((C * P.δ) ^ n *
      P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g)) ≤
    P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g)
  have hbase : 0 ≤ C * P.δ := mul_nonneg hC hδ
  have hp := pow_le_pow_left₀ hbase (mul_le_mul_of_nonneg_right hCC hδ) n
  have hr : 0 ≤ P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g) := Real.rpow_nonneg hL _
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hr
  exact mul_le_mul hJ hp (pow_nonneg hbase n) ((rootJetConstant_pos _).le.trans hJ)

/-- **The star-weighted leafwise incoherent decay gate** (C2-B-TOP's `StarIncoherentDecayGate`). -/
theorem starIncoherentDecay : StarIncoherentDecayGate := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, heta⟩ := exists_source_eta0L d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin _ τstar _ φ _
  obtain ⟨Cc, hCc, hc⟩ := exists_KQstarStar_decay d hd 1 zero_le_one
  obtain ⟨Ct, hCt, ht⟩ := exists_KTstarStar_decay d hd 1 zero_le_one
  let C₁ := starGateConstant d Cc Ct
  have hC₁ : 1 ≤ C₁ := one_le_starGateConstant d Cc Ct
  have hJC : rootJetConstant (30 * d) ≤ C₁ := le_max_left _ _
  have hcC : Cc ≤ C₁ := ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have htC : Ct ≤ C₁ := ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨C₁, hC₁, 1, zero_lt_one, ?_⟩
  intro ν _
  refine ⟨1, zero_lt_one, ?_⟩
  intro δ hδ D _ _
  obtain ⟨hηsmall, hscale, hηγ⟩ := heta η hη
  obtain ⟨Lc, hLc, hc⟩ := hc η hη.1 (hηsmall.trans (by norm_num)) hscale γ hγ hηγ
    δ hδ.1 hδ.2 D
  obtain ⟨Lt, hLt, ht⟩ := ht η hη.1 hηsmall hscale γ hγ hηγ δ hδ.1 hδ.2 D
  refine ⟨1, le_rfl, max 2 (max Lc Lt), le_max_left _ _, ?_⟩
  intro L hL
  let P : WTParams := ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, 1, L⟩
  have hLtwo : 2 ≤ L := (le_max_left _ _).trans hL
  have hLone : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hLtwo
  have hLcL : Lc ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLtL : Lt ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  intro p hp n _
  change p < D at hp
  have hpD : p ≤ D := Nat.le_of_lt hp
  constructor
  · intro Q _ hsize LG hQ hlayers q q' hq hq' hr hr' hg S ω c hω H B hctrl
    have hlen : Q.links.length = n := by
      have he : Q.links.length * 2 = Q.size := couple_linksAt_length Q ((0 : Fin 2), []) (1, [])
      omega
    have hb := leafwise_bound_of_normalized LG
      (fun H ts k => coupleLeavesStar L γ δ LG S ω H (ts 0) (ts 1) k)
      (fun B H hB ts k => kernelLeavesW_scale L γ δ LG H B hB _ _ _ _ _ _)
      (fun H _ hℓ h0 ts k => kernelLeavesW_zero_of_leaf L γ δ LG H hℓ h0 _ _ _ _ _ _)
      η (30 * d) (30 * d) (by omega) (timeBox q q')
      (ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (c a)) *
        ENNReal.ofReal ((Cc * δ) ^ Q.links.length *
          L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links)))
      (fun H' hH' => hc L hLcL p hpD Q LG hQ hlayers q q' hq hq' hr hr' hg H' hH' S ω c hω) H B hctrl
    rw [hlen] at hb
    refine hb.trans ?_
    rw [mul_comm (ENNReal.ofReal (leafSizeProduct LG B))]
    have := star_cost_le_regBound P hCc.le hcC hJC hδ.1.le (zero_le_one.trans hLone) n
      (LG.incoherency Q.links) (∏ a ∈ S, ENNReal.ofReal (c a))
    exact mul_le_mul_left this _
  · intro X _ hsize LG hX hlayers q q' hq'q hq _ _ hg S ω c hω H B hctrl
    have hlen : (X.treeLinks (LG.garden.sig 0)).length = n := by
      have he : (X.treeLinks (LG.garden.sig 0)).length * 2 = X.size :=
        chain_linksAt_length X (LG.garden.sig 0) ((0 : Fin 1), [])
      omega
    have hb := leafwise_bound_of_normalized LG
      (fun H ts k => treeLeavesStar L γ δ LG S ω H (ts 0) (ts 1) k)
      (fun B H hB ts k => kernelLeavesW_scale L γ δ LG H B hB _ _ _ _ _ _)
      (fun H _ hℓ h0 ts k => kernelLeavesW_zero_of_leaf L γ δ LG H hℓ h0 _ _ _ _ _ _)
      η (30 * d) 0 (by omega) (timeBoxGt q q')
      (ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (c a)) *
        ENNReal.ofReal ((Ct * δ) ^ (X.treeLinks (LG.garden.sig 0)).length *
          L ^ (-(incoherenceExponent d γ - Real.sqrt η) *
            LG.incoherency (X.treeLinks (LG.garden.sig 0)))))
      (fun H' hH' => ht L hLtL p hpD X LG hX hlayers q q' hq (hq'q.trans hq) hg H' hH' S ω c hω) H B hctrl
    rw [hlen] at hb
    refine hb.trans ?_
    rw [mul_comm (ENNReal.ofReal (leafSizeProduct LG B))]
    have := star_cost_le_regBound P hCt.le htC hJC hδ.1.le (zero_le_one.trans hLone) n
      (LG.incoherency (X.treeLinks (LG.garden.sig 0))) (∏ a ∈ S, ENNReal.ofReal (c a))
    exact mul_le_mul_left this _

end WaveTurbulence.Flower.IncTop
