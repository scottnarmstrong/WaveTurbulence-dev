/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootPack
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeBasic

/-! # D3 PROT-PIN: pinning the root (kernel level)

For a paired tree whose root (layer `p`) is not a lone parent, with all branches free and upper clock `T ≤ p + 1`:
`kernel(T, s; free) = ∫_{Ioo p T} kernel(u, s; root at u) du` (`kernelProt_root_pin`): D2c's time-level
`protTime_pin` at the root, the upper clock lowered to the root time (`protTime_rootFix_up`: every free branch lies
below the pinned root), measurability in the root time by a reindexing of the free coordinates
(`stronglyMeasurable_protTime_root`), and the exchange of the decoration sum and the integral. The integrand is the
`trace` configuration (root at its own upper clock). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

variable {LG : LayeredGarden 1}

theorem eq_rb_iff {rb : GBranch LG.garden.tree} (hrb : rb.1.2 = []) (b : GBranch LG.garden.tree) :
    b = rb ↔ b.1.2 = [] := by
  constructor
  · rintro rfl; exact hrb
  · intro h; exact Subtype.ext (Prod.ext (Subsingleton.elim _ _) (h.trans hrb.symm))

theorem rootFix_eq_update {rb : GBranch LG.garden.tree} (hrb : rb.1.2 = []) (u : ℝ) :
    (rootFix u : GBranch LG.garden.tree → Option ℝ) = Function.update (fun _ => none) rb (some u) := by
  funext b
  unfold rootFix
  by_cases hb : b = rb
  · subst hb; rw [if_pos hrb, Function.update_self]
  · rw [if_neg (fun h => hb ((eq_rb_iff hrb b).2 h)), Function.update_of_ne hb]

theorem rootFix_none_iff {rb : GBranch LG.garden.tree} (hrb : rb.1.2 = []) (u : ℝ) (b : GBranch LG.garden.tree) :
    (rootFix u : GBranch LG.garden.tree → Option ℝ) b = none ↔ b ≠ rb := by
  rw [ne_eq, eq_rb_iff hrb b]
  unfold rootFix
  split_ifs with h <;> simp [h]

/-- **Below a pinned root**: every free branch is earlier than the root time. -/
theorem lt_root_of_mem (up : GBranch LG.garden.tree → ℝ) (u : ℝ) (x : GBranch LG.garden.tree → ℝ)
    (hx : x ∈ kDomainFix LG up (rootFix u)) (hroot : ∀ b : GBranch LG.garden.tree, b.1.2 = [] → x b = u) :
    ∀ (n : ℕ) (b : GBranch LG.garden.tree), b.1.2.length = n + 1 → x b < u := by
  intro n
  induction n with
  | zero =>
    intro b hb
    have hne : b.1.2 ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hpar : b.1.2.dropLast ∈ (LG.garden.tree b.1.1).branching := by
      have h := b.2
      rw [← List.dropLast_append_getLast hne] at h
      exact MainCoef.mem_branching_of_append _ _ _ h
    let b0 : GBranch LG.garden.tree := ⟨(b.1.1, b.1.2.dropLast), hpar⟩
    have hchild : b.IsChildOf b0 := ⟨rfl, b.1.2.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hfree : (rootFix u : GBranch LG.garden.tree → Option ℝ) b = none := by
      unfold rootFix; rw [if_neg hne]
    have h1 := (hx b0).2 b hchild (Or.inl hfree)
    have h0 : b0.1.2 = [] := by
      show b.1.2.dropLast = []
      rw [← List.length_eq_zero_iff, List.length_dropLast, hb]
    rw [hroot b0 h0] at h1
    exact h1
  | succ n ih =>
    intro b hb
    have hne : b.1.2 ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hpar : b.1.2.dropLast ∈ (LG.garden.tree b.1.1).branching := by
      have h := b.2
      rw [← List.dropLast_append_getLast hne] at h
      exact MainCoef.mem_branching_of_append _ _ _ h
    let b0 : GBranch LG.garden.tree := ⟨(b.1.1, b.1.2.dropLast), hpar⟩
    have hchild : b.IsChildOf b0 := ⟨rfl, b.1.2.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    have hfree : (rootFix u : GBranch LG.garden.tree → Option ℝ) b = none := by
      unfold rootFix; rw [if_neg hne]
    have h1 := (hx b0).2 b hchild (Or.inl hfree)
    have hl : b0.1.2.length = n + 1 := by
      show b.1.2.dropLast.length = n + 1
      rw [List.length_dropLast, hb]; rfl
    exact h1.trans (ih b0 hl)

/-- **The upper clock of a root-pinned kernel can be lowered to the root time.** -/
theorem protTime_rootFix_up (L γ δ : ℝ) (s : ℝ) {d : ℕ} (K : GNode LG.garden.tree → Mom d) {u T : ℝ} (huT : u ≤ T) :
    protTime L γ δ LG (fun _ => T) s (rootFix u) K = protTime L γ δ LG (fun _ => u) s (rootFix u) K := by
  unfold protTime
  congr 1
  funext τ
  set x := LG.garden.extendFix (rootFix u) τ with hx
  have hroot : ∀ b : GBranch LG.garden.tree, b.1.2 = [] → x b = u := fun b hb =>
    extendFix_some LG.garden (rootFix u) τ (by unfold rootFix; rw [if_pos hb])
  have hiff : x ∈ protDom LG (fun _ => T) s (rootFix u) ↔ x ∈ protDom LG (fun _ => u) s (rootFix u) := by
    constructor
    · rintro ⟨hk, hl⟩
      refine ⟨fun b => ⟨fun hb => ?_, (hk b).2⟩, hl⟩
      obtain ⟨h1, h2, h3, -⟩ := (hk b).1 hb
      refine ⟨h1, h2, h3, ?_⟩
      have hne : b.1.2 ≠ [] := by
        intro h
        unfold rootFix at hb
        rw [if_pos h] at hb
        exact absurd hb (by simp)
      obtain ⟨n, hn⟩ : ∃ n, b.1.2.length = n + 1 :=
        ⟨b.1.2.length - 1, by have := List.length_pos_of_ne_nil hne; omega⟩
      exact lt_root_of_mem _ u x hk hroot n b hn
    · rintro ⟨hk, hl⟩
      refine ⟨fun b => ⟨fun hb => ?_, (hk b).2⟩, hl⟩
      obtain ⟨h1, h2, h3, h4⟩ := (hk b).1 hb
      exact ⟨h1, h2, h3, h4.trans_le huT⟩
  by_cases hm : x ∈ protDom LG (fun _ => T) s (rootFix u)
  · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.1 hm)]
  · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm (hiff.2 h))]

/-- The pin set of the root. -/
theorem pinSet_root {rb : GBranch LG.garden.tree} {p : ℕ} (hlay : LG.layer rb.toNode = p)
    (hnl : ¬ LG.garden.IsLoneParent rb) {T s : ℝ} (hT : T ≤ p + 1) :
    pinSet LG (fun _ => T) s (fun _ => none) rb = Ioo (p : ℝ) T := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  constructor
  · rintro ⟨h1, -, -, h4, -⟩
    rw [hlay] at h1
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [hlay]; exact h1, by rw [hlay]; linarith, by linarith, h2,
      fun _ _ _ h => absurd h (by simp), fun _ _ _ h => absurd h (by simp), fun h => absurd h hnl⟩

/-- **The time-level root pin.** -/
theorem protTime_root_pin (L γ δ : ℝ) (s : ℝ) {d : ℕ} (K : GNode LG.garden.tree → Mom d)
    {rb : GBranch LG.garden.tree} (hrb : rb.1.2 = []) {p : ℕ} (hlay : LG.layer rb.toNode = p)
    (hnl : ¬ LG.garden.IsLoneParent rb) {T : ℝ} (hT : T ≤ p + 1) :
    protTime L γ δ LG (fun _ => T) s (fun _ => none) K =
      ∫ u in Ioo (p : ℝ) T, protTime L γ δ LG (fun _ => u) s (rootFix u) K := by
  rw [protTime_pin L γ δ LG (fun _ => T) s (fun _ => none) K rb rfl, pinSet_root hlay hnl hT,
    integral_indicator measurableSet_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  rw [← rootFix_eq_update hrb u]
  exact protTime_rootFix_up L γ δ s K hu.2.le

/-! ### Measurability in the root time -/

/-- The free times with the root time `u` inserted. -/
def rootExt (rb : GBranch LG.garden.tree) (u : ℝ) (σ : {b : GBranch LG.garden.tree // b ≠ rb} → ℝ) :
    GBranch LG.garden.tree → ℝ :=
  fun b => if h : b = rb then u else σ ⟨b, h⟩

theorem measurable_rootExt (rb : GBranch LG.garden.tree) :
    Measurable (fun q : ℝ × ({b : GBranch LG.garden.tree // b ≠ rb} → ℝ) => rootExt rb q.1 q.2) := by
  refine measurable_pi_iff.mpr fun b => ?_
  unfold rootExt
  by_cases h : b = rb
  · simp only [h, dite_true]; exact measurable_fst
  · simp only [h, dite_false]; exact (measurable_pi_apply _).comp measurable_snd

theorem protDom_rootFix_eq (up : GBranch LG.garden.tree → ℝ) (s : ℝ) {rb : GBranch LG.garden.tree}
    (hrb : rb.1.2 = []) (u v : ℝ) :
    protDom LG up s (rootFix u) = protDom LG up s (rootFix v) := by
  have hn : ∀ b : GBranch LG.garden.tree,
      ((rootFix u : GBranch LG.garden.tree → Option ℝ) b = none ↔ (rootFix v : GBranch LG.garden.tree → Option ℝ) b = none) :=
    fun b => (rootFix_none_iff hrb u b).trans (rootFix_none_iff hrb v b).symm
  ext τ
  simp only [protDom, kDomainFix, Set.mem_inter_iff, Set.mem_setOf_eq, hn]

/-- The root-pinned time integral in the reindexed free coordinates. -/
theorem protTime_rootFix_eq (L γ δ : ℝ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) {d : ℕ}
    (K : GNode LG.garden.tree → Mom d) {rb : GBranch LG.garden.tree} (hrb : rb.1.2 = []) (u : ℝ) :
    protTime L γ δ LG up s (rootFix u) K =
      ∫ σ : {b : GBranch LG.garden.tree // b ≠ rb} → ℝ,
        (protDom LG up s (rootFix 0)).indicator (phaseProd L γ δ LG.garden K) (rootExt rb u σ) := by
  let e : {b : GBranch LG.garden.tree // b ≠ rb} ≃ {b : GBranch LG.garden.tree // rootFix u b = none} :=
    Equiv.subtypeEquivRight fun b => (rootFix_none_iff hrb u b).symm
  have hmp : MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) volume volume :=
    measurePreserving_piCongrLeft (fun _ : {b : GBranch LG.garden.tree // rootFix u b = none} =>
      (volume : Measure ℝ)) e
  unfold protTime
  refine (hmp.integral_comp' _).symm.trans ?_
  · congr 1
    funext σ
    rw [protDom_rootFix_eq up s hrb u 0]
    congr 1
    funext b
    unfold rootExt
    by_cases h : b = rb
    · rw [dif_pos h]
      exact extendFix_some LG.garden (rootFix u) _ (by unfold rootFix; rw [if_pos ((eq_rb_iff hrb b).1 h)])
    · rw [dif_neg h]
      have hfree : (rootFix u : GBranch LG.garden.tree → Option ℝ) b = none := (rootFix_none_iff hrb u b).2 h
      rw [extendFix_free LG.garden (rootFix u) _ ⟨b, hfree⟩]
      simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, e]
      exact congrArg σ (Subtype.ext rfl)

/-- **Measurability in the root time.** -/
theorem stronglyMeasurable_protTime_root (L γ δ : ℝ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) {d : ℕ}
    (K : GNode LG.garden.tree → Mom d) {rb : GBranch LG.garden.tree} (hrb : rb.1.2 = []) :
    StronglyMeasurable (fun u => protTime L γ δ LG up s (rootFix u) K) := by
  have e := fun u => protTime_rootFix_eq L γ δ up s K hrb u
  simp only [e]
  have hm : StronglyMeasurable (fun q : ℝ × ({b : GBranch LG.garden.tree // b ≠ rb} → ℝ) =>
      (protDom LG up s (rootFix 0)).indicator (phaseProd L γ δ LG.garden K) (rootExt rb q.1 q.2)) := by
    refine Measurable.stronglyMeasurable ?_
    exact ((ProtCut.continuous_phaseProd L γ δ LG.garden K).measurable.indicator
      (measurableSet_protDom LG up s _)).comp (measurable_rootExt rb)
  exact hm.integral_prod_right'

/-! ### The kernel -/

/-- **The root pin at kernel level.** -/
theorem kernelProt_root_pin (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (CM : ℝ) (hm : ∀ K, ‖m K‖ ≤ CM) (s : ℝ) (k₀ : Mom d)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree => ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|)
    {rb : GBranch LG.garden.tree} (hrb : rb.1.2 = []) {p : ℕ} (hlay : LG.layer rb.toNode = p)
    (hnl : ¬ LG.garden.IsLoneParent rb) {T : ℝ} (hT : T ≤ p + 1) :
    kernelProt L γ δ LG H m (fun _ => T) s (fun _ => none) k₀ (fun _ => 0) 0 =
      ∫ u in Ioo (p : ℝ) T, kernelProt L γ δ LG H m (fun _ => u) s (rootFix u) k₀ (fun _ => 0) 0 := by
  have hCM : 0 ≤ CM := (norm_nonneg _).trans (hm 0)
  set c0 : ℂ := (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta with hc0
  set f : GenDecoration LG.garden d (fun _ => 0) 0 → ℝ → ℂ :=
    fun κ u => protSummand L γ δ LG H m (fun _ => u) s (rootFix u) k₀ κ with hf
  have hsum := (PL234.summable_leafMajorant L LG H k₀ (fun _ => 0) 0 hlone hH).mul_left CM
  have hbd : ∀ κ u, ‖f κ u‖ ≤ CM * PL234.leafMajorant L LG H k₀ κ := fun κ u =>
    norm_protSummand_le L γ δ LG H m CM hm (fun _ => u) s (rootFix u) k₀ κ
  have hmeas : ∀ κ, AEStronglyMeasurable (f κ) (volume.restrict (Ioo (p : ℝ) T)) := fun κ => by
    have hg : StronglyMeasurable (fun u => protSummand L γ δ LG H m (fun _ => T) s (rootFix u) k₀ κ) := by
      simp only [protSummand]
      exact stronglyMeasurable_const.mul ((stronglyMeasurable_const.mul
        (stronglyMeasurable_protTime_root L γ δ (fun _ => T) s _ hrb)).mul stronglyMeasurable_const)
    refine hg.aestronglyMeasurable.congr ?_
    refine (ae_restrict_mem measurableSet_Ioo).mono fun u hu => ?_
    simp only [hf, protSummand]
    rw [protTime_rootFix_up L γ δ s _ hu.2.le]
  have hvol : volume (Ioo (p : ℝ) T) ≠ ⊤ := measure_Ioo_lt_top.ne
  have hint : ∀ κ, Integrable (f κ) (volume.restrict (Ioo (p : ℝ) T)) := fun κ =>
    Integrable.of_bound (hmeas κ) (CM * PL234.leafMajorant L LG H k₀ κ)
      (Filter.Eventually.of_forall (hbd κ))
  have hnorm : ∀ κ, ∫ u in Ioo (p : ℝ) T, ‖f κ u‖ ≤ CM * PL234.leafMajorant L LG H k₀ κ * (volume (Ioo (p : ℝ) T)).toReal :=
    fun κ => by
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (p : ℝ) T) (f := fun u => ‖f κ u‖)
        (C := CM * PL234.leafMajorant L LG H k₀ κ) (lt_top_iff_ne_top.mpr hvol)
        (fun u _ => by rw [norm_norm]; exact hbd κ u)
      have h0 : 0 ≤ ∫ u in Ioo (p : ℝ) T, ‖f κ u‖ := integral_nonneg fun _ => norm_nonneg _
      rw [Real.norm_of_nonneg h0, measureReal_def] at h1
      exact h1
  have hsI : Summable fun κ => ∫ u in Ioo (p : ℝ) T, ‖f κ u‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hnorm (hsum.mul_right _)
  rw [kernelProt_eq_tsum]
  have hR : ∀ u, kernelProt L γ δ LG H m (fun _ => u) s (rootFix u) k₀ (fun _ => 0) 0 = c0 * ∑' κ, f κ u :=
    fun u => kernelProt_eq_tsum L γ δ LG H m _ s _ k₀ _ _
  simp only [hR]
  rw [integral_const_mul, ← integral_tsum_of_summable_integral_norm hint hsI]
  congr 1
  refine tsum_congr fun κ => ?_
  simp only [hf, protSummand]
  rw [protTime_root_pin L γ δ s _ hrb hlay hnl hT, ← integral_const_mul, ← integral_mul_const,
    ← integral_const_mul]

end WaveTurbulence.Flower.ProtPin
