/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FlowerTop.ThreeInputs
public import WaveTurbulence.Foundations.Flower.Stage1W.Defs
public import WaveTurbulence.Foundations.Flower.Stage1W.Bound

/-! # STAGE1W-GLUE G4: `Stage1TypeBoundFW` (R5), the weighted copy of main's `stage1_type_bound`.

`GPresented` weights are bounded by `cψ`, so the garden weight is bounded by `cψ^(#nodes)`; the weighted
decoration sums split over the piece partition, and `stage1_core_bound_int` is applied at size `cψ^(16N) s`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1W
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

/-- A `GPresented` weight is bounded by its constant. -/
theorem GPresented.norm_le {d J : ℕ} {g : Mom d → ℂ} {c : ℝ} (h : GPresented J g c) (hc : 0 ≤ c) (x : Mom d) :
    ‖g x‖ ≤ c := by
  obtain ⟨α, _, M, hM, hv⟩ := h
  rw [← hv x]
  have h1 : ‖M.value x‖ ≤ ∫ a, ‖M.amplitude a‖ ∂M.μ := by
    unfold Cut2A.SpatialMeasure.value
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      M.amplitude_integrable.norm (Filter.Eventually.of_forall fun a => ?_)
    simp
  refine h1.trans ?_
  rw [integral_norm_eq_lintegral_enorm M.amplitude_integrable.aestronglyMeasurable]
  have h2 : ∫⁻ a, ‖M.amplitude a‖ₑ ∂M.μ ≤ ENNReal.ofReal c := by
    refine le_trans (lintegral_mono fun a => ?_) hM
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + ‖M.frequency a‖) ^ J) := by
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      exact one_le_pow₀ (by linarith [norm_nonneg (M.frequency a)])
    calc ‖M.amplitude a‖ₑ = 1 * ‖M.amplitude a‖ₑ := (one_mul _).symm
      _ ≤ _ := by gcongr
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h2).trans (ENNReal.toReal_ofReal hc).le


/-- The garden weight is bounded by `cψ ^ (#nodes)`. -/
theorem fwWeight_norm_le {P : WTParams} {R : ℕ} (p : ℕ) (g : Fin (2 * R) → Mom P.d → ℂ) (base : Mom P.d)
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (cψ : ℝ) (hc : 1 ≤ cψ)
    (hg : ∀ j x, ‖g j x‖ ≤ cψ) (LG : LayeredGarden (2 * R)) (κ : GenDecoration LG.garden P.d roots 0) :
    ‖fwWeight p g base LG κ‖ ≤ cψ ^ Fintype.card (GNode LG.garden.tree) := by
  unfold fwWeight nodeLabelProduct
  rw [norm_prod]
  refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => ?_ : ∀ a ∈ Finset.univ, _ ≤ cψ)).trans
    (by simp)
  simp only [topPsi]
  split_ifs <;> first | exact hg _ _ | simpa using hc

/-- Weighted sigma-indicator partition lemma. -/
theorem valueSelW_sum {P : WTParams} {w : ℕ} (F : LeafFamily P w) (tt : Fin w → ℝ)
    (base : Mom P.d) (roots : Fin w → (Fin P.d → ℤ)) (LG : LayeredGarden w) {ι : Type*}
    (t : Finset ι) (sel : ι → GenDecoration LG.garden P.d roots 0 → Prop)
    (wt : GenDecoration LG.garden P.d roots 0 → ℂ) (B : ℝ) (hB : ∀ κ, ‖wt κ‖ ≤ B)
    (hpart : ∀ κ, ∃! i, i ∈ t ∧ sel i κ)
    (hsum : ∀ j, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      kernelLeavesTerm P.L P.γ P.δ LG (F.H LG j) (fun b => tt b.1.1) 0 base κ) :
    ∑ i ∈ t, valueSelW F tt base roots LG (sel i) wt = valueW F tt base roots LG wt := by
  unfold valueSelW valueW
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold kernelLeavesSelW
  rw [← Finset.mul_sum]
  congr 1
  have hs1 : Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      wt κ * kernelLeavesTerm P.L P.γ P.δ LG (F.H LG j) (fun b => tt b.1.1) 0 base κ := by
    have := (summable_norm_iff.mpr (hsum j))
    refine Summable.of_norm_bounded (this.mul_left B) fun κ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB κ) (norm_nonneg _)
  have hsel : ∀ i, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      if sel i κ then wt κ * kernelLeavesTerm P.L P.γ P.δ LG (F.H LG j) (fun b => tt b.1.1) 0 base κ else 0 := by
    intro i
    have := hs1.indicator {κ | sel i κ}
    refine this.congr fun κ => ?_
    by_cases h : sel i κ <;> simp [Set.indicator, h]
  rw [← Summable.tsum_finsetSum (fun i _ => hsel i)]
  refine tsum_congr fun κ => ?_
  obtain ⟨i0, ⟨hi0, hs0⟩, huniq⟩ := hpart κ
  rw [Finset.sum_eq_single i0]
  · simp [hs0]
  · intro j' hj hne
    have : ¬ sel j' κ := fun h => hne (huniq j' ⟨hj, h⟩)
    simp [this]
  · intro h; exact absurd hi0 h

/-- Weighted `sum_eq_sum_pieces`. -/
theorem sum_eq_sum_piecesW {R : ℕ} {P : WTParams} {Pc Cl : Type} [Fintype Pc]
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (A : Finset (LayeredGarden (2 * R))) (members : Cl → Finset (LayeredGarden (2 * R)))
    (cls : Pc → Cl)
    (sel : Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    [Fintype Cl] (h : Stage1Partition roots A members cls sel)
    (tt : Fin (2 * R) → ℝ) (base : Mom P.d) (F : LeafFamily P (2 * R))
    (wt : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ)
    (hB : ∀ LG ∈ A, ∃ B : ℝ, ∀ κ, ‖wt LG κ‖ ≤ B)
    (hsum : ∀ LG ∈ A, ∀ j, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      kernelLeavesTerm P.L P.γ P.δ LG (F.H LG j) (fun b => tt b.1.1) 0 base κ) :
    ∑ LG ∈ A, valueW F tt base roots LG (wt LG) =
      ∑ π, ∑ LG ∈ members (cls π), valueSelW F tt base roots LG (sel π LG) (wt LG) := by
  have hA : A = Finset.univ.biUnion members := by
    ext LG; simp [h.1 LG]
  have e1 : ∑ LG ∈ A, valueW F tt base roots LG (wt LG) =
      ∑ c, ∑ LG ∈ members c, valueW F tt base roots LG (wt LG) := by
    rw [hA, Finset.sum_biUnion]
    intro c _ c' _ hne
    exact h.2.1 c c' hne
  rw [e1, ← Finset.sum_fiberwise (s := Finset.univ) (g := cls)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hmem : ∀ LG ∈ members c, LG ∈ A := fun LG hLG => (h.1 LG).2 ⟨c, hLG⟩
  calc ∑ LG ∈ members c, valueW F tt base roots LG (wt LG)
      = ∑ LG ∈ members c, ∑ π ∈ Finset.univ.filter (fun π => cls π = c),
          valueSelW F tt base roots LG (sel π LG) (wt LG) := by
        refine Finset.sum_congr rfl fun LG hLG => ?_
        symm
        obtain ⟨B, hBd⟩ := hB LG (hmem LG hLG)
        refine valueSelW_sum F tt base roots LG (Finset.univ.filter (fun π => cls π = c))
          (fun π => sel π LG) (wt LG) B hBd (fun κ => ?_) (hsum LG (hmem LG hLG))
        obtain ⟨π, ⟨hπ1, hπ2⟩, hu⟩ := h.2.2 c LG hLG κ
        exact ⟨π, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ1⟩, hπ2⟩,
          fun π' ⟨hπ', hs'⟩ => hu π' ⟨(Finset.mem_filter.mp hπ').2, hs'⟩⟩
    _ = ∑ π ∈ Finset.univ.filter (fun π => cls π = c), ∑ LG ∈ members (cls π),
          valueSelW F tt base roots LG (sel π LG) (wt LG) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun π hπ => ?_
        rw [(Finset.mem_filter.mp hπ).2]

theorem stage1TypeBoundFW : Stage1TypeBoundFW := by
  intro C₀ P hs hcoarse hfourier hcount habs hlog hd hgate p R N hp hR hRmax hN1 hN A hA hcl tt htt base roots
    g cψ hc1 hgp hreal U s hs0 hU hsize
  have hctrl : ∀ LG ∈ A, U.toLF.Controlled LG := fun LG hLG =>
    TypeFamilyD.controlled_of_bounded U hU LG (Canon.layer_le_of_isCanonGC (hA LG hLG).1)
  have hc0 : 0 ≤ cψ := by linarith
  have hgb : ∀ j x, ‖g j x‖ ≤ cψ := fun j x => (hgp j).norm_le hc0 x
  have hs0' : 0 < cψ ^ (16 * N) * s := by positivity
  obtain ⟨S, Cl, hCl, cls, members, sel, hpart, hrep, hsound, hord, hcounts⟩ :=
    hgate p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots g cψ hc1 hgp hreal U s hs0 hU hsize
  letI := S.fin
  letI := hCl
  have hL1 : 1 ≤ P.L := by linarith [hs.L_ge]
  have hsumm : ∀ LG ∈ A, ∀ j, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      kernelLeavesTerm P.L P.γ P.δ LG (U.toLF.H LG j) (fun b => tt b.1.1) 0 base κ := by
    intro LG hLG j
    have hplain : LG.garden.IsPlain := (hA LG hLG).1.1
    exact summable_leafKernel_summand P.L P.γ P.δ LG (U.toLF.H LG j) _ 0 base roots 0
      (card_lone_le_one_of_plain LG.garden hplain)
      ((hctrl LG hLG j).summable_coset hd hL1 base)
  have hsum : ∑ LG ∈ A, valueW U.toLF tt base roots LG (fwWeight p g base LG) = ∑ π, S.val π := by
    rw [sum_eq_sum_piecesW roots A members cls sel hpart tt base U.toLF (fwWeight p g base)
      (fun LG _ => ⟨_, fwWeight_norm_le p g base cψ hc1 hgb LG⟩) hsumm]
    exact Finset.sum_congr rfl fun π _ => ((hrep π).1).symm
  rw [hsum]
  have hnn : 0 ≤ cψ ^ (16 * N) * s *
      (P.δ ^ (8 * P.ν * N) * (P.L ^ (-P.η ^ 7) * P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 70)))) := by
    have hL0 : 0 < P.L := by linarith [hs.L_ge]
    have := hs.delta_pos
    positivity
  by_cases hne : Nonempty S.Pc
  · obtain ⟨π⟩ := hne
    have hRN : R ≤ 2 * N := by
      have h1 := (hsound π).bond_count
      have h2 := hord π
      omega
    have hNlog : (N : ℝ) ≤ Real.log P.L ^ (4 * (40 * P.d) ^ (2 * P.D + 2)) := by
      have h1 : (N : ℝ) ≤ (P.N (p + 1) : ℝ) ^ 4 := by exact_mod_cast hN
      exact h1.trans (N_quartic_le_log_pow P hd hlog (p + 1))
    obtain ⟨hT2, hS2, hL⟩ := habs.2 N R hR hRN hNlog
    exact stage1_core_bound_int P hs hcoarse hfourier hcount hp hR hRmax S tt base roots C₀ Cl cls
      (cψ ^ (16 * N) * s) hs0' hsound hord (fun π => (hrep π).2) hcounts.1 hcounts.2.1 hcounts.2.2 habs.1
      hT2 hS2 hL
  · have hemp : IsEmpty S.Pc := not_nonempty_iff.mp hne
    simpa [Finset.univ_eq_empty] using hnn

end WaveTurbulence.Flower.Stage1W
