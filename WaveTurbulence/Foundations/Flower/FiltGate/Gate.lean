/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltGate.Statements
public import WaveTurbulence.Foundations.Flower.IncTop.StarGate
public import WaveTurbulence.Foundations.Flower.FiltGate.StarDecay

/-! # D5b-3 FILT-GATE: the gate from the filtered star decays

`filtIncoherentDecayGate_of_star`: `ProtDefs.FiltIncoherentDecayGate` from `StarFiltCoupleDecay d 1` and
`StarFiltTreeDecay d 1` (every `d ≥ 3`). The proof is INC-TOP's `starIncoherentDecay` (StarGate) with the D5 multiplier:
leafwise normalization (`leafwise_bound_of_normalized`; the weighted kernel is homogeneous and vanishes with a leaf
profile for every multiplier, `IncTop.kernelLeavesW_scale`, `kernelLeavesW_zero_of_leaf`), at the time weight `θ` of
the gate, and the constant `C₁ := starGateConstant d Cc Ct`, chosen after `d, γ, η`. The loss `L^c` is carried.

`filtIncoherentDecayGate : ProtDefs.FiltIncoherentDecayGate` closes it with `StarDecay`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Finset
open scoped ENNReal Classical
namespace WaveTurbulence.Flower.FiltGate
open WaveTurbulence.Induct WaveTurbulence.IncohInst WaveTurbulence.Incoh WaveTurbulence.Links
open WaveTurbulence.LGSpine WaveTurbulence.IncohLeafwise WaveTurbulence.Flower.IncTop

/-- `rootJetConstant (30d) · M · (C δ)^n L^{-…g} L^c ≤ M · L^c · regBound`, once `C, rootJetConstant ≤ C₁`. -/
theorem starFilt_cost_le_regBound (P : WTParams) {C : ℝ} (hC : 0 ≤ C) (hCC : C ≤ P.C₁)
    (hJ : rootJetConstant (30 * P.d) ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) (c : ℝ) (M : ℝ≥0∞) :
    ENNReal.ofReal (rootJetConstant (30 * P.d)) * M *
        ENNReal.ofReal ((C * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g) * P.L ^ c) ≤
      M * ENNReal.ofReal (P.L ^ c) * regBound P n g := by
  rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (mul_nonneg hC hδ) n) (Real.rpow_nonneg hL _))]
  have h := star_cost_le_regBound P hC hCC hJ hδ hL n g M
  calc
    _ = (ENNReal.ofReal (rootJetConstant (30 * P.d)) * M *
          ENNReal.ofReal ((C * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g))) *
        ENNReal.ofReal (P.L ^ c) := by ring
    _ ≤ (M * regBound P n g) * ENNReal.ofReal (P.L ^ c) := mul_le_mul' h le_rfl
    _ = _ := by ring

/-- **The D5b gate from the two filtered star decays.** -/
theorem filtIncoherentDecayGate_of_star (hcpl : ∀ d : ℕ, 3 ≤ d → StarFiltCoupleDecay d 1)
    (htree : ∀ d : ℕ, 3 ≤ d → StarFiltTreeDecay d 1) : ProtDefs.FiltIncoherentDecayGate := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, heta⟩ := exists_source_eta0L d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin _ τstar _ φ _
  obtain ⟨Cc, hCc, hc⟩ := hcpl d hd
  obtain ⟨Ct, hCt, ht⟩ := htree d hd
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
  obtain ⟨Lc, hLc, hc⟩ := hc η hη.1 hηsmall hscale γ hγ hηγ δ hδ.1 hδ.2 D
  obtain ⟨Lt, hLt, ht⟩ := ht η hη.1 hηsmall hscale γ hγ hηγ δ hδ.1 hδ.2 D
  refine ⟨1, le_rfl, max 2 (max Lc Lt), le_max_left _ _, ?_⟩
  intro L hL
  let P : WTParams := ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, 1, L⟩
  have hLtwo : 2 ≤ L := (le_max_left _ _).trans hL
  have hLone : 1 ≤ L := (by norm_num : (1 : ℝ) ≤ 2).trans hLtwo
  have hLcL : Lc ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLtL : Lt ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  intro p hp n _ θ c hθc
  change p < D at hp
  have hpD : p ≤ D := Nat.le_of_lt hp
  constructor
  · intro Q _ hsize LG hQ hlayers q q' hq hq' hr hr' hg S ω cω hω F ann M hM Fu Mu hMu H B hctrl
    have hlen : Q.links.length = n := by
      have he : Q.links.length * 2 = Q.size := couple_linksAt_length Q ((0 : Fin 2), []) (1, [])
      omega
    have hb := leafwise_bound_of_normalized LG
      (fun H ts k => coupleLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts 0) (ts 1) k)
      (fun B H hB ts k => kernelLeavesW_scale L γ δ LG H B hB _ _ _ _ _ _)
      (fun H _ hℓ h0 ts k => kernelLeavesW_zero_of_leaf L γ δ LG H hℓ h0 _ _ _ _ _ _)
      θ (30 * d) (30 * d) (by omega) (timeBox q q')
      (ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (cω a)) *
        ENNReal.ofReal ((Cc * δ) ^ Q.links.length *
          L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links) * L ^ c))
      (fun H' hH' => hc L hLcL θ c hθc p hpD Q LG hQ hlayers q q' hq hq' hr hr' hg H' hH' S ω cω hω
        F ann M hM Fu Mu hMu) H B hctrl
    rw [hlen] at hb
    refine hb.trans ?_
    rw [mul_comm (ENNReal.ofReal (leafSizeProduct LG B))]
    exact mul_le_mul' (starFilt_cost_le_regBound P hCc.le hcC hJC hδ.1.le (zero_le_one.trans hLone) n
      (LG.incoherency Q.links) c (∏ a ∈ S, ENNReal.ofReal (cω a))) le_rfl
  · intro X _ hsize LG hX hlayers q q' hq'q hq _ _ hg S ω cω hω F ann M hM Fu Mu hMu H B hctrl
    have hlen : (X.treeLinks (LG.garden.sig 0)).length = n := by
      have he : (X.treeLinks (LG.garden.sig 0)).length * 2 = X.size :=
        chain_linksAt_length X (LG.garden.sig 0) ((0 : Fin 1), [])
      omega
    have hb := leafwise_bound_of_normalized LG
      (fun H ts k => treeLeavesStarFilt L γ δ LG S ω F ann M Fu Mu H (ts 0) (ts 1) k)
      (fun B H hB ts k => kernelLeavesW_scale L γ δ LG H B hB _ _ _ _ _ _)
      (fun H _ hℓ h0 ts k => kernelLeavesW_zero_of_leaf L γ δ LG H hℓ h0 _ _ _ _ _ _)
      θ (30 * d) 0 (by omega) (timeBoxGt q q')
      (ENNReal.ofReal (rootJetConstant (30 * d)) * (∏ a ∈ S, ENNReal.ofReal (cω a)) *
        ENNReal.ofReal ((Ct * δ) ^ (X.treeLinks (LG.garden.sig 0)).length *
          L ^ (-(incoherenceExponent d γ - Real.sqrt η) *
            LG.incoherency (X.treeLinks (LG.garden.sig 0))) * L ^ c))
      (fun H' hH' => ht L hLtL θ c hθc p hpD X LG hX hlayers q q' hq (hq'q.trans hq) hg H' hH' S ω cω hω
        F ann M hM Fu Mu hMu) H B hctrl
    rw [hlen] at hb
    refine hb.trans ?_
    rw [mul_comm (ENNReal.ofReal (leafSizeProduct LG B))]
    exact mul_le_mul' (starFilt_cost_le_regBound P hCt.le htC hJC hδ.1.le (zero_le_one.trans hLone) n
      (LG.incoherency (X.treeLinks (LG.garden.sig 0))) c (∏ a ∈ S, ENNReal.ofReal (cω a))) le_rfl

/-- **D5b FILT-INC: the filtered incoherent decay gate** (`ProtDefs.FiltIncoherentDecayGate`, SCOPE D0 §4.4;
o82 Prop 15.1 `g ≥ 1` at `X^η`, Lemma 16.1 at `X^{1/4}` with loss `L^{4d}`, Lemma 18.1 for annular factors). -/
theorem filtIncoherentDecayGate : ProtDefs.FiltIncoherentDecayGate :=
  filtIncoherentDecayGate_of_star (fun d hd => starFiltCoupleDecay d hd 1 zero_le_one)
    (fun d hd => starFiltTreeDecay d hd 1 zero_le_one)

end WaveTurbulence.Flower.FiltGate
