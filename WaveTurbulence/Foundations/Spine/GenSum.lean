/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.BoxSup
public import WaveTurbulence.Foundations.Spine.PhiFamily
import Mathlib.Tactic
/-! Step 1 of TARGET ladderl1old (L2003–L2008), generic form: the sum over integer boxes of
suprema is bounded by `2^n 2^n ∑_A ∫_W ‖Φ_A‖`, `W` the `2`-neighbourhood of the spectrum. -/
@[expose] public section
open MeasureTheory Set Finset Function
open scoped ENNReal
namespace WaveTurbulence.Ladder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unit box with lower corner `a`. -/
def ubox (a : ι → ℝ) : Set (ι → ℝ) := Set.pi univ (fun v => Icc (a v) (a v + 1))

/-- The shifted corner `σ - 1_E`. -/
def corner (σ : ι → ℤ) (E : Finset ι) : ι → ℝ := fun v => (σ v : ℝ) - if v ∈ E then 1 else 0

theorem box_cover (α : ι → ℝ) (σ : ι → ℤ) (h : ∀ v, |α v - σ v| ≤ 1) :
    ∃ E : Finset ι, α ∈ ubox (corner σ E) := by
  refine ⟨univ.filter (fun v => α v < σ v), fun v _ => ?_⟩
  have := abs_le.mp (h v)
  by_cases hv : α v < σ v
  · simp only [corner, Finset.mem_filter, Finset.mem_univ, true_and, hv, if_true]
    constructor <;> linarith [this.1]
  · simp only [corner, Finset.mem_filter, Finset.mem_univ, true_and, hv, if_false]
    constructor <;> linarith [this.2, not_lt.mp hv]

theorem multiplicity_le (E : Finset ι) (α : ι → ℝ) (Sg : Set (ι → ℤ)) :
    ∑' σ : Sg, (ubox (corner σ.1 E)).indicator (fun _ => (1 : ℝ≥0∞)) α ≤ 2 ^ Fintype.card ι := by
  classical
  set F : Finset (ι → ℤ) := Fintype.piFinset (fun v => ({⌊α v⌋ + (if v ∈ E then 1 else 0),
      ⌊α v⌋ - 1 + (if v ∈ E then 1 else 0)} : Finset ℤ)) with hF
  rw [tsum_subtype Sg (fun σ => (ubox (corner σ E)).indicator (fun _ => (1 : ℝ≥0∞)) α)]
  have hsupp : ∀ σ ∉ F, Sg.indicator (fun σ => (ubox (corner σ E)).indicator (fun _ => (1 : ℝ≥0∞)) α) σ = 0 := by
    intro σ hσ
    by_cases hs : σ ∈ Sg
    · by_cases hα : α ∈ ubox (corner σ E)
      · exfalso; apply hσ
        rw [hF, Fintype.mem_piFinset]
        intro v
        have h1 := (hα v (mem_univ v))
        simp only [corner] at h1
        set c : ℤ := if v ∈ E then 1 else 0 with hc
        have hcr : ((c : ℤ) : ℝ) = if v ∈ E then 1 else 0 := by
          rw [hc]; split_ifs <;> simp
        rw [← hcr] at h1
        have h2 : ⌊α v⌋ ≥ σ v - c := by
          rw [ge_iff_le, Int.le_floor]; push_cast; linarith [h1.1]
        have h3 : ⌊α v⌋ ≤ σ v - c + 1 := by
          have h4 : (⌊α v⌋ : ℝ) ≤ ((σ v - c + 1 : ℤ) : ℝ) := by
            have := Int.floor_le (α v)
            push_cast; linarith [h1.2]
          exact_mod_cast h4
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · simp [Set.indicator_of_mem hs, Set.indicator_of_notMem hα]
    · simp [Set.indicator_of_notMem hs]
  rw [tsum_eq_sum hsupp]
  calc ∑ σ ∈ F, Sg.indicator (fun σ => (ubox (corner σ E)).indicator (fun _ => (1 : ℝ≥0∞)) α) σ
      ≤ ∑ σ ∈ F, (1 : ℝ≥0∞) := by
        refine Finset.sum_le_sum (fun σ _ => ?_)
        by_cases hs : σ ∈ Sg
        · rw [Set.indicator_of_mem hs]
          by_cases hα : α ∈ ubox (corner σ E) <;> simp [hα]
        · simp [Set.indicator_of_notMem hs]
    _ = F.card := by simp
    _ ≤ 2 ^ Fintype.card ι := by
        have : F.card ≤ 2 ^ Fintype.card ι := by
          rw [hF, Fintype.card_piFinset]
          calc ∏ v : ι, ({⌊α v⌋ + (if v ∈ E then 1 else 0), ⌊α v⌋ - 1 + (if v ∈ E then 1 else 0)} : Finset ℤ).card
              ≤ ∏ _v : ι, 2 := Finset.prod_le_prod' (fun v _ => Finset.card_le_two)
            _ = 2 ^ Fintype.card ι := by simp
        exact_mod_cast this

/-- The `1`-neighbourhood of a set of frequencies. -/
def Wnb (𝒜 : Set (ι → ℝ)) : Set (ι → ℝ) := {α | ∃ α' ∈ 𝒜, ∀ v, |α v - α' v| ≤ 1}

theorem tsum_box_le (g : (ι → ℝ) → ℝ≥0∞) (hg : Measurable g) (E : Finset ι)
    (W : Set (ι → ℝ)) (Sg : Set (ι → ℤ)) (hSg : ∀ σ ∈ Sg, ubox (corner σ E) ⊆ W) :
    ∑' σ : Sg, ∫⁻ x in ubox (corner σ.1 E), g x ≤ 2 ^ Fintype.card ι * ∫⁻ x in W, g x := by
  have hbm : ∀ σ : Sg, MeasurableSet (ubox (corner σ.1 E)) := fun σ =>
    MeasurableSet.univ_pi (fun v => measurableSet_Icc)
  have h1 : ∀ σ : Sg, ∫⁻ x in ubox (corner σ.1 E), g x =
      ∫⁻ x, (ubox (corner σ.1 E)).indicator g x := fun σ => (lintegral_indicator (hbm σ) g).symm
  simp_rw [h1]
  rw [← lintegral_tsum (fun σ => (hg.indicator (hbm σ)).aemeasurable)]
  have h2 : ∀ x, ∑' σ : Sg, (ubox (corner σ.1 E)).indicator g x ≤ 2 ^ Fintype.card ι * W.indicator g x := by
    intro x
    by_cases hx : x ∈ W
    · rw [Set.indicator_of_mem hx]
      have : ∀ σ : Sg, (ubox (corner σ.1 E)).indicator g x =
          (ubox (corner σ.1 E)).indicator (fun _ => (1 : ℝ≥0∞)) x * g x := by
        intro σ
        by_cases hσ : x ∈ ubox (corner σ.1 E) <;> simp [hσ]
      simp_rw [this]
      rw [ENNReal.tsum_mul_right]
      exact mul_le_mul_left (multiplicity_le E x Sg) _
    · have : ∀ σ : Sg, (ubox (corner σ.1 E)).indicator g x = 0 := by
        intro σ
        by_cases hσ : x ∈ ubox (corner σ.1 E)
        · exact absurd (hSg σ.1 σ.2 hσ) hx
        · simp [hσ]
      simp [this]
  calc _ ≤ ∫⁻ x, 2 ^ Fintype.card ι * W.indicator g x := lintegral_mono h2
    _ = 2 ^ Fintype.card ι * ∫⁻ x, W.indicator g x := by
        rw [lintegral_const_mul' _ _ (by simp)]
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_indicator_le g _)

theorem sum_sup_le (Ω : Set (ι → ℝ)) (hΩm : MeasurableSet Ω) (T : ℝ)
    (hΩb : ∀ t ∈ Ω, ∀ v, |t v| ≤ T) (L : ι → ℝ) (𝒜 : Set (ι → ℝ)) (Sg : Set (ι → ℤ)) :
    ∑' σ : Sg, ⨆ (α : ι → ℝ) (_ : α ∈ 𝒜) (_ : ∀ v, |α v - (σ.1 v : ℝ)| ≤ 1), ‖Phi Ω L ∅ α‖ₑ ≤
      2 ^ Fintype.card ι * (2 ^ Fintype.card ι *
        ∑ A : Finset ι, ∫⁻ α in Wnb 𝒜, ‖Phi Ω L A α‖ₑ) := by
  classical
  have hga : ∀ A : Finset ι, Measurable (fun y => ‖Phi Ω L A y‖ₑ) := fun A =>
    (continuous_Phi Ω hΩm T hΩb L A).measurable.enorm
  set F : Finset ι → Finset ι → (ι → ℤ) → ℝ≥0∞ := fun E A σ =>
    if (ubox (corner σ E) ∩ 𝒜).Nonempty then ∫⁻ y in ubox (corner σ E), ‖Phi Ω L A y‖ₑ else 0 with hF
  have ha : ∀ σ : Sg, ⨆ (α : ι → ℝ) (_ : α ∈ 𝒜) (_ : ∀ v, |α v - (σ.1 v : ℝ)| ≤ 1), ‖Phi Ω L ∅ α‖ₑ ≤
      ∑ E : Finset ι, ∑ A : Finset ι, F E A σ.1 := by
    intro σ
    refine iSup_le (fun α => iSup_le (fun hα' => iSup_le (fun hα => ?_)))
    obtain ⟨E, hE⟩ := box_cover α σ.1 hα
    have h1 := elem_sup_Phi Ω hΩm T hΩb L (corner σ.1 E) α (fun v => hE v (mem_univ v))
    have hne : (ubox (corner σ.1 E) ∩ 𝒜).Nonempty := ⟨α, hE, hα'⟩
    refine h1.trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun E : Finset ι => ∑ A : Finset ι, F E A σ.1)
      (fun _ _ => bot_le) (mem_univ E))
    refine le_of_eq (Finset.sum_congr rfl (fun A _ => ?_))
    simp only [hF, if_pos hne]
    rfl
  have hsub : ∀ E : Finset ι, ∀ σ ∈ {σ : ι → ℤ | (ubox (corner σ E) ∩ 𝒜).Nonempty},
      ubox (corner σ E) ⊆ Wnb 𝒜 := by
    intro E σ hσ y hy
    obtain ⟨α', hα'1, hα'2⟩ := hσ
    refine ⟨α', hα'2, fun v => ?_⟩
    have h1 := hy v (mem_univ v)
    have h2 := hα'1 v (mem_univ v)
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  calc _ ≤ ∑' σ : Sg, ∑ E : Finset ι, ∑ A : Finset ι, F E A σ.1 := ENNReal.tsum_le_tsum ha
    _ = ∑ E : Finset ι, ∑ A : Finset ι, ∑' σ : Sg, F E A σ.1 := by
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        refine Finset.sum_congr rfl (fun E _ => ?_)
        rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    _ ≤ ∑ E : Finset ι, ∑ A : Finset ι, 2 ^ Fintype.card ι * ∫⁻ y in Wnb 𝒜, ‖Phi Ω L A y‖ₑ := by
        refine Finset.sum_le_sum (fun E _ => Finset.sum_le_sum (fun A _ => ?_))
        set SgE : Set (ι → ℤ) := {σ | (ubox (corner σ E) ∩ 𝒜).Nonempty} with hSgE
        have h1 : ∑' σ : Sg, F E A σ.1 ≤ ∑' σ : (ι → ℤ), F E A σ :=
          ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun σ => F E A σ)
        have h2 : ∑' σ : (ι → ℤ), F E A σ = ∑' σ : SgE, ∫⁻ y in ubox (corner σ.1 E), ‖Phi Ω L A y‖ₑ := by
          rw [tsum_subtype SgE (fun σ => ∫⁻ y in ubox (corner σ E), ‖Phi Ω L A y‖ₑ)]
          refine tsum_congr (fun σ => ?_)
          by_cases hσ : σ ∈ SgE
          · have hn : (ubox (corner σ E) ∩ 𝒜).Nonempty := hσ
            rw [Set.indicator_of_mem hσ]; simp only [hF, if_pos hn]
          · have hn : ¬ (ubox (corner σ E) ∩ 𝒜).Nonempty := hσ
            rw [Set.indicator_of_notMem hσ]; simp only [hF, if_neg hn]
        refine h1.trans (h2.le.trans ?_)
        exact tsum_box_le _ (hga A) E (Wnb 𝒜) SgE (hsub E)
    _ = _ := by
        simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_finset,
          nsmul_eq_mul]
        push_cast; ring

end WaveTurbulence.Ladder
