/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.IncohLeafwise.KernelScaling
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.AllCoupleDecay
public import WaveTurbulence.Foundations.Spine.IncohLeafwise.TreeDecay
public import WaveTurbulence.Foundations.Spine.LeafwiseAt
public import WaveTurbulence.Foundations.IncohInst.Links.Partition

/-! # TARGET Proposition 5.1 with individually modified leaf inputs (L953-L956 at L2062-L2067)

`leafwiseIncoherentDecay`: the leafwise B2.2 gate `LeafwiseIncoherentDecayGate`. The common-profile
proof of `incoherentDecay` is generalized: the raw kernel identities and the analytic decay are
proved for per-leaf profiles (`IncohLeafwise.*Decay`), and each leaf bound `B_ℓ` is extracted by
homogeneity (`leafwise_bound_of_normalized`). -/

public section
open WaveTurbulence.Induct
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace WaveTurbulence.IncohLeafwise
open WaveTurbulence.IncohInst Incoh Links WaveTurbulence.LGSpine

theorem exists_source_eta0L (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc (0 : ℝ) η₀,
      η ≤ 1 / 100 ∧ (100 * (d : ℝ)) ^ 2 * η ≤ 1 ∧ η < incoherenceExponent d γ := by
  have hg := incoherenceExponent_pos (by omega : 2 ≤ d) hγ
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hc : (0 : ℝ) < (100 * (d : ℝ)) ^ 2 := by positivity
  refine ⟨min (1 / 100) (min (1 / (100 * (d : ℝ)) ^ 2) (incoherenceExponent d γ / 2)),
    lt_min (by norm_num) (lt_min (div_pos zero_lt_one hc) (half_pos hg)), ?_⟩
  intro η hη
  have h₁ := hη.2.trans (min_le_left _ _)
  have h₂ := hη.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ := hη.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨h₁, ?_, lt_of_le_of_lt h₃ (half_lt_self hg)⟩
  have hh := (le_div_iff₀ hc).mp h₂
  simpa only [mul_comm] using hh

/-- Enlarge the already proved coefficient to the source's common `C₁`, retaining its outside factor. -/
theorem componentBound_le_regBoundL (P : WTParams) {C : ℝ} (hC : 0 ≤ C)
    (hCC : C ≤ P.C₁) (hC₁ : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ) (hL : 0 ≤ P.L) (n g : ℕ) :
    ENNReal.ofReal ((C * P.δ) ^ n *
      P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g)) ≤ regBound P n g := by
  apply ENNReal.ofReal_le_ofReal
  change (C * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g) ≤
    P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(incoherenceExponent P.d P.γ - Real.sqrt P.η) * g)
  have hbase : 0 ≤ C * P.δ := mul_nonneg hC hδ
  have hp := pow_le_pow_left₀ hbase (mul_le_mul_of_nonneg_right hCC hδ) n
  have he := mul_le_mul_of_nonneg_right hC₁ (pow_nonneg (mul_nonneg (zero_le_one.trans hC₁) hδ) n)
  simp only [one_mul] at he
  exact mul_le_mul_of_nonneg_right (hp.trans he) (Real.rpow_nonneg hL _)

theorem coupleLeaves_scale {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2) :
    ∀ (B : (Fin 2 × TTree.Path) → NNReal) (H : LeafProfiles 2 d),
      (∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ)) →
        ∀ (ts : Fin 2 → ℝ) (k : Mom d), coupleLeaves L γ δ LG H (ts 0) (ts 1) k = ((leafSizeProduct LG B : ℝ) : ℂ) *
          coupleLeaves L γ δ LG (fun a x => H a x / (B a : ℝ)) (ts 0) (ts 1) k :=
  fun B H hB _ k => kernelLeaves_scale L γ δ LG H B hB _ _ _ _ _

theorem treeLeaves_scale {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1) :
    ∀ (B : (Fin 1 × TTree.Path) → NNReal) (H : LeafProfiles 1 d),
      (∀ ℓ ∈ inputLeaves LG.garden, 0 < (B ℓ.1 : ℝ)) →
        ∀ (ts : Fin 2 → ℝ) (k : Mom d), treeLeaves L γ δ LG H (ts 0) (ts 1) k = ((leafSizeProduct LG B : ℝ) : ℂ) *
          treeLeaves L γ δ LG (fun a x => H a x / (B a : ℝ)) (ts 0) (ts 1) k :=
  fun B H hB _ k => kernelLeaves_scale L γ δ LG H B hB _ _ _ _ _

theorem coupleLeaves_zero {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2) :
    ∀ (H : LeafProfiles 2 d) (ℓ : GLeaf LG.garden.tree), ℓ ∈ inputLeaves LG.garden →
      H ℓ.1 = (fun _ => 0) → ∀ (ts : Fin 2 → ℝ) (k : Mom d), coupleLeaves L γ δ LG H (ts 0) (ts 1) k = 0 :=
  fun H _ hℓ h0 _ _ => kernelLeaves_zero_of_leaf L γ δ LG H hℓ h0 _ _ _ _ _

theorem treeLeaves_zero {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1) :
    ∀ (H : LeafProfiles 1 d) (ℓ : GLeaf LG.garden.tree), ℓ ∈ inputLeaves LG.garden →
      H ℓ.1 = (fun _ => 0) → ∀ (ts : Fin 2 → ℝ) (k : Mom d), treeLeaves L γ δ LG H (ts 0) (ts 1) k = 0 :=
  fun H _ hℓ h0 _ _ => kernelLeaves_zero_of_leaf L γ δ LG H hℓ h0 _ _ _ _ _

/-- TARGET Prop 5.1 applied with individually modified leaf inputs (L2062-L2067). -/
theorem leafwiseIncoherentDecay : LeafwiseIncoherentDecayGate := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, heta⟩ := exists_source_eta0L d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin _ τstar _ φ _
  obtain ⟨Cc, hCc, hc⟩ := exists_KQstar_decayL d hd 1 zero_le_one
  obtain ⟨Ct, hCt, ht⟩ := exists_KTstar_decayL d hd 1 zero_le_one
  let C₁ := max 1 (max Cc Ct)
  have hC₁ : 1 ≤ C₁ := le_max_left _ _
  have hcC : Cc ≤ C₁ := (le_max_left _ _).trans (le_max_right _ _)
  have htC : Ct ≤ C₁ := (le_max_right _ _).trans (le_max_right _ _)
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
  · intro Q _ hsize LG hQ hlayers q q' hq hq' hr hr' hg H B hctrl
    have hlen : Q.links.length = n := by
      have he : Q.links.length * 2 = Q.size := couple_linksAt_length Q ((0 : Fin 2), []) (1, [])
      omega
    have hb := leafwise_bound_of_normalized LG
      (fun H ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k)
      (coupleLeaves_scale L γ δ LG) (coupleLeaves_zero L γ δ LG) η (30 * d) (30 * d)
      (by omega) (timeBox q q')
      (ENNReal.ofReal ((Cc * δ) ^ Q.links.length *
        L ^ (-(incoherenceExponent d γ - Real.sqrt η) * LG.incoherency Q.links)))
      (fun H' hH' => hc L hLcL p hpD Q LG hQ hlayers q q' hq hq' hr hr' hg H' hH') H B hctrl
    rw [hlen] at hb
    refine hb.trans ?_
    rw [mul_comm]
    gcongr
    exact componentBound_le_regBoundL P hCc.le hcC hC₁ hδ.1.le (zero_le_one.trans hLone) n _
  · intro X _ hsize LG hX hlayers q q' hq'q hq _ _ hg H B hctrl
    have hlen : (X.treeLinks (LG.garden.sig 0)).length = n := by
      have he : (X.treeLinks (LG.garden.sig 0)).length * 2 = X.size :=
        chain_linksAt_length X (LG.garden.sig 0) ((0 : Fin 1), [])
      omega
    have hb := leafwise_bound_of_normalized LG
      (fun H ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k)
      (treeLeaves_scale L γ δ LG) (treeLeaves_zero L γ δ LG) η (30 * d) 0
      (by omega) (timeBoxGt q q')
      (ENNReal.ofReal ((Ct * δ) ^ (X.treeLinks (LG.garden.sig 0)).length *
        L ^ (-(incoherenceExponent d γ - Real.sqrt η) *
          LG.incoherency (X.treeLinks (LG.garden.sig 0)))))
      (fun H' hH' => ht L hLtL p hpD X LG hX hlayers q q' hq (hq'q.trans hq) hg H' hH') H B hctrl
    rw [hlen] at hb
    refine hb.trans ?_
    rw [mul_comm]
    gcongr
    exact componentBound_le_regBoundL P hCt.le htC hC₁ hδ.1.le (zero_le_one.trans hLone) n _

end WaveTurbulence.IncohLeafwise
