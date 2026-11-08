/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTDefs
public import WaveTurbulence.Foundations.Flower.MkSlotsB.CapPKer
public import WaveTurbulence.Foundations.Flower.ProtWhole.ContJ

/-! # B3s-HELPER3 (B5(ii)): generic analytic lemmas for the root-trace slots

* `kDomainR_eq_protDom`, **`kernelNodeWR_kDomainR_eq_kernelProt`**: the relaxed node kernel with no pinned clock
  constraint is D2a's protected kernel at the lower time `s`, when the free lower clock (`sFree`) leaves no pinned lone
  parent;
* `prod_fwNode_eq_starWeight`, `norm_starWeight_front_le`, `starPresented_front`: the frontier cutoffs of a native
  object are star weights (the node's own momentum) of constant `frontierConst`;
* `mem_protDom_up_iff`, **`continuous_kernelProt_cpl`**: continuity of a couple kernel in its two tree clocks (the
  twin of D6b's `continuous_kernelProt_joint`, one clock per tree);
* the gate boxes: `cell2`, `timeBoxGt_cut_subset_cell`, `timeBoxGt_cut_subset_closure_interior`,
  `timeBox_subset_closure_interior`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal Topology
open Set Filter MeasureTheory
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.LGSpine WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtWhole
  WaveTurbulence.Flower.Stage1WNoVine WaveTurbulence.Flower.Stage1W WaveTurbulence.VineEstS3.FS

namespace WaveTurbulence.Flower.MkSlotsB

/-! ### The relaxed node kernel is the protected kernel -/

section Ker

variable {w d : ℕ}

theorem kDomainR_eq_protDom (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) (sFree : Prop)
    (hs : sFree → ∀ b, LG.garden.IsLoneParent b → fix b = none) :
    kDomainR LG up s fix (fun _ => False) sFree = protDom LG up s fix := by
  ext τ
  simp only [kDomainR, protDom, kDomainFix, Set.mem_inter_iff, Set.mem_ofPred_eq, or_false]
  constructor
  · intro h
    refine ⟨fun b => ⟨fun hb => ⟨((h b).1 hb).1, ((h b).1 hb).2.1, ((h b).1 hb).2.2, (h b).2.1 hb⟩, (h b).2.2.1⟩,
      fun b hl hf => (h b).2.2.2 hl (Or.inl hf)⟩
  · rintro ⟨h1, h2⟩ b
    refine ⟨fun hb => ⟨((h1 b).1 hb).1, ((h1 b).1 hb).2.1, ((h1 b).1 hb).2.2.1⟩, fun hb => ((h1 b).1 hb).2.2.2,
      (h1 b).2, fun hl hf => ?_⟩
    rcases hf with hf | hf
    · exact h2 b hl hf
    · exact h2 b hl (hs hf b hl)

/-- **The relaxed node kernel with no pinned clock constraint is the protected kernel.** -/
theorem kernelNodeWR_kDomainR_eq_kernelProt (L γ δ : ℝ) (LG : LayeredGarden w)
    (A : GNode LG.garden.tree → Mom d → ℝ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (sFree : Prop) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) (fix : GBranch LG.garden.tree → Option ℝ)
    (hs : sFree → ∀ b, LG.garden.IsLoneParent b → fix b = none) :
    kernelNodeWR L γ δ LG A m (kDomainR LG up s fix (fun _ => False) sFree) k₀ nroot nfl (fun _ => 1) fix =
      kernelProt L γ δ LG (MkSlots.capProfiles LG A) m up s fix k₀ nroot nfl := by
  rw [kernelProt_eq_tsum, kDomainR_eq_protDom LG up s fix sFree hs]
  unfold kernelNodeWR
  congr 1
  refine tsum_congr fun κ => ?_
  unfold ProtCut.protSummand ProtCut.protTime
  rw [mul_one]
  congr 2
  · congr 1
    rw [MkSlots.integral_fixMeasure]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    dsimp only
    rw [← MkSlots.capExtendFix_eq]
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [MkSlots.capProfiles_leaf]

end Ker

/-! ### The frontier cutoffs as star weights -/

section Front

variable {w w' d : ℕ}

/-- **The frontier cutoffs of a native object are star weights** (the node's own momentum). -/
theorem prod_fwNode_eq_starWeight (LG : LayeredGarden w) (p : ℕ) (g : Fin w → Mom d → ℂ) {T : Fin w' → TTree}
    (e : GNode T → GNode LG.garden.tree) (K' : GNode T → Mom d) :
    ∏ z, fwNode LG p g (e z) (K' z) =
      IncTop.starWeight (Finset.univ.filter fun z => (e z).1.2 ≠ [] ∧ LG.layer (e z) < p ∧
        LG.parentLayer p (e z) = p) (fun z y => g (e z).1.1 (y 0)) K' := by
  unfold IncTop.starWeight
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun z _ => ?_
  dsimp only
  rw [IncTop.starMomenta_zero]
  unfold fwNode topPsi
  split_ifs <;> first | rfl | (exfalso; tauto)

theorem norm_frontierG_le (o : Option ℝ) (x : Mom d) : ‖frontierG (d := d) o x‖ ≤ 1 := by
  unfold frontierG
  rw [Complex.norm_real, Real.norm_eq_abs]
  cases o with
  | none => simp
  | some r =>
    simp only [Option.elim]
    rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact XChain.ProductCut.chi0_le_one _

theorem norm_starWeight_front_le {T : Fin w' → TTree} (S : Finset (GNode T)) (Rf : Fin w → Option ℝ)
    (j : GNode T → Fin w) (K' : GNode T → Mom d) :
    ‖IncTop.starWeight S (fun z y => frontierG (Rf (j z)) (y 0)) K'‖ ≤ 1 := by
  unfold IncTop.starWeight
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun z _ => norm_frontierG_le _ _

theorem starPresented_front {T : Fin w' → TTree} (Rf : Fin w → Option ℝ) (hRf : ∀ j r, Rf j = some r → 1 ≤ r)
    (j : GNode T → Fin w) (z : GNode T) :
    IncTop.StarPresented (30 * d) (fun y : IncTop.Star d => frontierG (Rf (j z)) (y 0)) (frontierConst d) :=
  IncTop.starPresented_of_gPresented (by omega) (gPresented_frontierG d (Rf (j z)) (hRf (j z)))

end Front

/-! ### Continuity of a couple kernel in its two tree clocks -/

section Cont

variable {d : ℕ}

theorem mem_protDom_up_iff {w : ℕ} (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ)
    (x : GBranch LG.garden.tree → ℝ) (up up' : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (h : ∀ b, fix b = none → (x b < up b ↔ x b < up' b)) :
    x ∈ protDom LG up s fix ↔ x ∈ protDom LG up' s fix := by
  unfold protDom kDomainFix
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ⟨fun hf => ?_, (h1 b).2⟩, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := (h1 b).1 hf
    exact ⟨a1, a2, a3, (h b hf).1 a4⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun b => ⟨fun hf => ?_, (h1 b).2⟩, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := (h1 b).1 hf
    exact ⟨a1, a2, a3, (h b hf).2 a4⟩

/-- The per-tree clock of a couple. -/
def cplUp {T : Fin 2 → TTree} (ts : Fin 2 → ℝ) : GBranch T → ℝ := fun b => if b.1.1 = 0 then ts 0 else ts 1

theorem cplUp_mem {T : Fin 2 → TTree} (ts : Fin 2 → ℝ) (b : GBranch T) : cplUp ts b = ts 0 ∨ cplUp ts b = ts 1 := by
  unfold cplUp
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem continuousAt_protIntegrand_cpl (L γ δ s : ℝ) (LG : LayeredGarden 2)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) (ts₀ : Fin 2 → ℝ)
    (τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ) (hτ : ∀ b, τ b ≠ ts₀ 0 ∧ τ b ≠ ts₀ 1) :
    ContinuousAt (fun ts : Fin 2 → ℝ => protIntegrand L γ δ LG (cplUp ts) s fix K τ) ts₀ := by
  have hev : ∀ᶠ ts in 𝓝 ts₀, ∀ b : {b : GBranch LG.garden.tree // fix b = none},
      (τ b < ts 0 ↔ τ b < ts₀ 0) ∧ (τ b < ts 1 ↔ τ b < ts₀ 1) := by
    rw [Filter.eventually_all]
    intro b
    have e : ∀ i : Fin 2, τ b ≠ ts₀ i → ∀ᶠ ts in 𝓝 ts₀, (τ b < ts i ↔ τ b < ts₀ i) := by
      intro i hi
      rcases lt_or_gt_of_ne hi with hb | hb
      · filter_upwards [(continuous_apply i).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hb)] with ts hts
        exact iff_of_true hts hb
      · filter_upwards [(continuous_apply i).continuousAt.preimage_mem_nhds (Iio_mem_nhds hb)] with ts hts
        exact iff_of_false (not_lt.2 (le_of_lt hts)) (not_lt.2 hb.le)
    exact (e 0 (hτ b).1).and (e 1 (hτ b).2)
  refine (continuousAt_const (y := protIntegrand L γ δ LG (cplUp ts₀) s fix K τ)).congr ?_
  filter_upwards [hev] with ts hts
  unfold protIntegrand
  have hmem := mem_protDom_up_iff LG fix (LG.garden.extendFix fix τ) (cplUp ts) (cplUp ts₀) s
    (fun b hf => by
      rw [extendFix_free LG.garden fix τ ⟨b, hf⟩]
      unfold cplUp
      split_ifs
      · exact (hts ⟨b, hf⟩).1
      · exact (hts ⟨b, hf⟩).2)
  by_cases hm : LG.garden.extendFix fix τ ∈ protDom LG (cplUp ts₀) s fix
  · rw [indicator_of_mem hm, indicator_of_mem (hmem.2 hm)]
  · rw [indicator_of_notMem hm, indicator_of_notMem (fun h => hm (hmem.1 h))]

theorem continuous_protTime_cpl (L γ δ s : ℝ) (LG : LayeredGarden 2)
    (fix : GBranch LG.garden.tree → Option ℝ) (K : GNode LG.garden.tree → Mom d) :
    Continuous (fun ts : Fin 2 → ℝ => protTime L γ δ LG (cplUp ts) s fix K) := by
  have hBm : MeasurableSet (freeBox LG fix) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hint : Integrable ((freeBox LG fix).indicator (1 : ({b : GBranch LG.garden.tree //
      fix b = none} → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff hBm]
    exact integrableOn_const (by rw [volume_freeBox]; exact ENNReal.one_ne_top)
  rw [continuous_iff_continuousAt]
  intro ts₀
  show ContinuousAt (fun ts : Fin 2 → ℝ => ∫ τ, protIntegrand L γ δ LG (cplUp ts) s fix K τ) ts₀
  have hae : ∀ᵐ τ ∂(volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)),
      ∀ b, τ b ≠ ts₀ 0 ∧ τ b ≠ ts₀ 1 :=
    ((ae_ne_eval _ (ts₀ 0)).and (ae_ne_eval _ (ts₀ 1))).mono fun τ h b => ⟨h.1 b, h.2 b⟩
  exact continuousAt_of_dominated
    (Eventually.of_forall fun ts =>
      (measurable_protIntegrand L γ δ LG (cplUp ts) s fix K).aestronglyMeasurable)
    (Eventually.of_forall fun ts => Eventually.of_forall
      (norm_protIntegrand_le L γ δ LG (cplUp ts) s fix K))
    hint (hae.mono fun τ hτ => continuousAt_protIntegrand_cpl L γ δ s LG fix K ts₀ τ hτ)

/-- **Continuity of a couple kernel in its two tree clocks.** -/
theorem continuous_kernelProt_cpl (L γ δ s : ℝ) (LG : LayeredGarden 2) (H : LeafProfiles 2 d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (C : ℝ) (hm : ∀ K, ‖m K‖ ≤ C)
    (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => kernelProt L γ δ LG H m (cplUp ts) s fix k₀ (fun _ => 0) 0) := by
  have he : (fun ts : Fin 2 → ℝ => kernelProt L γ δ LG H m (cplUp ts) s fix k₀ (fun _ => 0) 0) =
      fun ts => (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ∑' κ : GenDecoration LG.garden d (fun _ => 0) 0, protSummand L γ δ LG H m (cplUp ts) s fix k₀ κ := by
    funext ts
    exact kernelProt_eq_tsum L γ δ LG H m _ _ fix k₀ _ _
  rw [he]
  refine continuous_const.mul (continuous_tsum (fun κ => ?_)
    ((PL234.summable_leafMajorant L LG H k₀ (fun _ => 0) 0 hlone hH).mul_left C)
    (fun κ ts => norm_protSummand_le L γ δ LG H m C hm (cplUp ts) s fix k₀ κ))
  unfold protSummand
  exact continuous_const.mul ((continuous_const.mul
    (continuous_protTime_cpl L γ δ s LG fix _)).mul continuous_const)

end Cont

/-! ### The gate boxes -/

/-- The cell at `(q, q')`. -/
def cell2 (q q' : ℝ) : Fin 2 → ℝ := ![q, q']

theorem timeBox_eq_cell (q q' : ℝ) : timeBox q q' = cell (cell2 q q') := by
  ext ts
  constructor
  · rintro ⟨h0, h1⟩
    show ∀ i, ts i ∈ Icc (cell2 q q' i) (cell2 q q' i + 1)
    intro i
    fin_cases i
    · simpa [cell2] using h0
    · simpa [cell2] using h1
  · intro h
    have h' : ∀ i, ts i ∈ Icc (cell2 q q' i) (cell2 q q' i + 1) := h
    exact ⟨by simpa [cell2] using h' 0, by simpa [cell2] using h' 1⟩

theorem timeBoxGt_cut_subset_cell (q q' s : ℝ) : timeBoxGt q q' ∩ {ts | ts 1 < s} ⊆ cell (cell2 q q') := by
  intro ts hts
  rw [← timeBox_eq_cell]
  exact hts.1.1

theorem convex_timeBox (q q' : ℝ) : Convex ℝ (timeBox q q') := by
  intro x hx y hy a b ha hb hab
  obtain ⟨⟨hx1, hx2⟩, hx3, hx4⟩ := hx
  obtain ⟨⟨hy1, hy2⟩, hy3, hy4⟩ := hy
  have e : ∀ i, (a • x + b • y) i = a * x i + b * y i := fun i => by simp [smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> rw [e] <;> nlinarith

theorem timeBox_subset_closure_interior (q q' : ℝ) : timeBox q q' ⊆ closure (interior (timeBox q q')) := by
  have hne : (interior (timeBox q q')).Nonempty := by
    let U : Set (Fin 2 → ℝ) := {ts | q < ts 0 ∧ ts 0 < q + 1 ∧ q' < ts 1 ∧ ts 1 < q' + 1}
    have hUo : IsOpen U := by
      simp only [U, Set.ofPred_and]
      exact (isOpen_lt continuous_const (continuous_apply 0)).inter ((isOpen_lt (continuous_apply 0)
        continuous_const).inter ((isOpen_lt continuous_const (continuous_apply 1)).inter
          (isOpen_lt (continuous_apply 1) continuous_const)))
    have hUsub : U ⊆ timeBox q q' := fun ts h => ⟨⟨h.1.le, h.2.1.le⟩, ⟨h.2.2.1.le, h.2.2.2.le⟩⟩
    refine ⟨![q + 1 / 2, q' + 1 / 2], interior_maximal hUsub hUo ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> norm_num
  rw [(convex_timeBox q q').closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

theorem timeBoxGt_cut_subset_closure_interior (q q' s : ℝ) (hqq : q' ≤ q) (hs : q < s) :
    timeBoxGt q q' ∩ {ts | ts 1 < s} ⊆ closure (interior (timeBoxGt q q' ∩ {ts | ts 1 < s})) := by
  have hcv : Convex ℝ (timeBoxGt q q' ∩ {ts : Fin 2 → ℝ | ts 1 < s}) := by
    refine (MkSlots.convex_timeBoxGt q q').inter ?_
    intro x hx y hy a b ha hb hab
    show a * x 1 + b * y 1 < s
    have hx' : x 1 < s := hx
    have hy' : y 1 < s := hy
    rcases ha.lt_or_eq with ha' | ha'
    · have h1 := mul_lt_mul_of_pos_left hx' ha'
      have h2 := mul_le_mul_of_nonneg_left hy'.le hb
      have h3 : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
      linarith
    · subst ha'; simp at hab; subst hab; simpa using hy'
  have hne : (interior (timeBoxGt q q' ∩ {ts : Fin 2 → ℝ | ts 1 < s})).Nonempty := by
    let U : Set (Fin 2 → ℝ) := {ts | q < ts 0 ∧ ts 0 < q + 1 ∧ q' < ts 1 ∧ ts 1 < q' + 1 ∧ ts 1 < ts 0 ∧ ts 1 < s}
    have hUo : IsOpen U := by
      simp only [U, Set.ofPred_and]
      exact (isOpen_lt continuous_const (continuous_apply 0)).inter ((isOpen_lt (continuous_apply 0)
        continuous_const).inter ((isOpen_lt continuous_const (continuous_apply 1)).inter
          ((isOpen_lt (continuous_apply 1) continuous_const).inter ((isOpen_lt (continuous_apply 1)
            (continuous_apply 0)).inter (isOpen_lt (continuous_apply 1) continuous_const)))))
    have hUsub : U ⊆ timeBoxGt q q' ∩ {ts | ts 1 < s} := fun ts h =>
      ⟨⟨⟨⟨h.1.le, h.2.1.le⟩, ⟨h.2.2.1.le, h.2.2.2.1.le⟩⟩, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩
    set m := min (1 / 2 : ℝ) (s - q') with hm
    have hm0 : 0 < m := lt_min (by norm_num) (by linarith)
    have hm1 : m ≤ 1 / 2 := min_le_left _ _
    have hm2 : m ≤ s - q' := min_le_right _ _
    refine ⟨![q + 1 / 2, q' + m / 2], interior_maximal hUsub hUo ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

theorem timeBoxGt_cut2_subset_cell (q q' s : ℝ) :
    timeBoxGt q q' ∩ {ts | ts 1 < s ∧ s ≤ ts 0} ⊆ cell (cell2 q q') := by
  intro ts hts
  rw [← timeBox_eq_cell]
  exact hts.1.1

/-- The tree gate's box (R189): `timeBoxGt q q'` with the lower clock below `s` and the upper clock above `s`. -/
theorem timeBoxGt_cut2_subset_closure_interior (q q' s : ℝ) (hqq : q' ≤ q) (hs : q < s) (hs1 : s < q + 1) :
    timeBoxGt q q' ∩ {ts | ts 1 < s ∧ s ≤ ts 0} ⊆
      closure (interior (timeBoxGt q q' ∩ {ts | ts 1 < s ∧ s ≤ ts 0})) := by
  have hcv : Convex ℝ (timeBoxGt q q' ∩ {ts : Fin 2 → ℝ | ts 1 < s ∧ s ≤ ts 0}) := by
    refine (MkSlots.convex_timeBoxGt q q').inter ?_
    intro x hx y hy a b ha hb hab
    obtain ⟨hx1, hx0⟩ := hx
    obtain ⟨hy1, hy0⟩ := hy
    have h3 : a * s + b * s = s := by rw [← add_mul, hab, one_mul]
    have e : ∀ i, (a • x + b • y) i = a * x i + b * y i := fun i => by simp [smul_eq_mul]
    refine ⟨?_, ?_⟩
    · show (a • x + b • y) 1 < s
      rw [e]
      rcases ha.lt_or_eq with ha' | ha'
      · have h1 := mul_lt_mul_of_pos_left hx1 ha'
        have h2 := mul_le_mul_of_nonneg_left hy1.le hb
        linarith
      · subst ha'; simp at hab; subst hab; simpa using hy1
    · show s ≤ (a • x + b • y) 0
      rw [e]
      have h1 := mul_le_mul_of_nonneg_left hx0 ha
      have h2 := mul_le_mul_of_nonneg_left hy0 hb
      linarith
  have hne : (interior (timeBoxGt q q' ∩ {ts : Fin 2 → ℝ | ts 1 < s ∧ s ≤ ts 0})).Nonempty := by
    let U : Set (Fin 2 → ℝ) :=
      {ts | s < ts 0 ∧ ts 0 < q + 1 ∧ q' < ts 1 ∧ ts 1 < q' + 1 ∧ ts 1 < s}
    have hUo : IsOpen U := by
      simp only [U, Set.ofPred_and]
      exact (isOpen_lt continuous_const (continuous_apply 0)).inter ((isOpen_lt (continuous_apply 0)
        continuous_const).inter ((isOpen_lt continuous_const (continuous_apply 1)).inter
          ((isOpen_lt (continuous_apply 1) continuous_const).inter (isOpen_lt (continuous_apply 1)
            continuous_const))))
    have hUsub : U ⊆ timeBoxGt q q' ∩ {ts | ts 1 < s ∧ s ≤ ts 0} := fun ts h =>
      ⟨⟨⟨⟨by linarith [h.1], h.2.1.le⟩, ⟨h.2.2.1.le, h.2.2.2.1.le⟩⟩, by linarith [h.1, h.2.2.2.2]⟩,
        h.2.2.2.2, h.1.le⟩
    set m := min (1 / 2 : ℝ) (s - q') with hm
    have hm0 : 0 < m := lt_min (by norm_num) (by linarith)
    have hm1 : m ≤ 1 / 2 := min_le_left _ _
    have hm2 : m ≤ s - q' := min_le_right _ _
    refine ⟨![(s + (q + 1)) / 2, q' + m / 2], interior_maximal hUsub hUo ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  rw [hcv.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

end WaveTurbulence.Flower.MkSlotsB
