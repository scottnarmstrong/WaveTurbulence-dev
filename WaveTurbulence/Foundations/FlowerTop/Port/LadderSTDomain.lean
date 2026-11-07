/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final3f
public import WaveTurbulence.Foundations.FlowerTop.Port.FixLemmas
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderFourierSTFree
/-! # FLOWER-P5: the free-clock time domain with stubs as a generic ladder-engine domain

With stubs held at `D.stubTime`, the time domain of the free clocks is (up to null sets) the generic domain
`Om0 chF lsF capF`: children of a stub get the cap `stubTime`, parents of a stub get the floor `stubTime`
(encoded by shifting the box start `lsF` and capping at `layer + 1`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ} {G : Garden w}

/-- The free branches. -/
abbrev FrB (G : Garden w) (fix : GBranch G.tree → Option ℝ) := {b : GBranch G.tree // fix b = none}

/-- `b` is the parent of a stub: floor. -/
def floorB (D : SplicedKernelDataST G d) (b : GBranch G.tree) : Prop := ∃ c ∈ D.stubs, c.IsChildOf b
/-- `b` is a child of a stub: cap. -/
def capB (D : SplicedKernelDataST G d) (b : GBranch G.tree) : Prop := ∃ c ∈ D.stubs, b.IsChildOf c

/-- Box start of a free branch (floor encoded). -/
noncomputable def lsF (D : SplicedKernelDataST G d) (v : FrB G D.fix) : ℝ :=
  if floorB D v.1 then max (D.layer v.1 : ℝ) D.stubTime else (D.layer v.1 : ℝ)

/-- Strict cap of a free branch. -/
noncomputable def capF (D : SplicedKernelDataST G d) (v : FrB G D.fix) : ℝ :=
  min (min (D.rootTime v.1.1.1) (if floorB D v.1 then (D.layer v.1 : ℝ) + 1 else D.rootTime v.1.1.1))
    (if capB D v.1 then D.stubTime else D.rootTime v.1.1.1)

def chF (D : SplicedKernelDataST G d) (a b : FrB G D.fix) : Prop := a.1.IsChildOf b.1

/-- The null set of boundary coincidences. -/
def nullF (D : SplicedKernelDataST G d) : Set (FrB G D.fix → ℝ) :=
  (⋃ v : FrB G D.fix, {τ | τ v = D.stubTime}) ∪ ⋃ v : FrB G D.fix, {τ | τ v = (D.layer v.1 : ℝ) + 1}

theorem volume_nullF (D : SplicedKernelDataST G d) : volume (nullF D) = 0 := by
  unfold nullF
  exact measure_union_null (measure_iUnion_null fun v => volume_eval_eq v _)
    (measure_iUnion_null fun v => volume_eval_eq v _)

theorem fix_stub (D : SplicedKernelDataST G d) (b : GBranch G.tree) (hb : b ∈ D.stubs) :
    D.fix b = some D.stubTime := by
  unfold SplicedKernelDataST.fix FlowerP1.stubFix; simp [hb]

theorem fix_none_iff (D : SplicedKernelDataST G d) (b : GBranch G.tree) : D.fix b = none ↔ b ∉ D.stubs := by
  unfold SplicedKernelDataST.fix FlowerP1.stubFix; by_cases h : b ∈ D.stubs <;> simp [h]

theorem extendFix_stub (D : SplicedKernelDataST G d) (τ : FrB G D.fix → ℝ) (b : GBranch G.tree)
    (hb : b ∈ D.stubs) : G.extendFix D.fix τ b = D.stubTime := by
  unfold Garden.extendFix
  split
  · rename_i v hv; rw [fix_stub D b hb] at hv; cases hv; rfl
  · rename_i hv; rw [fix_stub D b hb] at hv; cases hv

theorem domFix_iff (D : SplicedKernelDataST G d) (τ : FrB G D.fix → ℝ) (hτ : τ ∉ nullF D) :
    G.extendFix D.fix τ ∈ splicedTimeDomainFix G D.layer D.rootTime D.fix ↔
      τ ∈ Om0 (chF D) (lsF D) (capF D) := by
  have hn1 : ∀ v : FrB G D.fix, τ v ≠ D.stubTime := fun v h => hτ (Or.inl (Set.mem_iUnion.mpr ⟨v, h⟩))
  have hn2 : ∀ v : FrB G D.fix, τ v ≠ (D.layer v.1 : ℝ) + 1 := fun v h =>
    hτ (Or.inr (Set.mem_iUnion.mpr ⟨v, h⟩))
  have hext : ∀ v : FrB G D.fix, G.extendFix D.fix τ v.1 = τ v := fun v => extendFix_free D.fix τ v.1 v.2
  unfold splicedTimeDomainFix Om0
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun v => ?_, fun v => ?_, fun a b hab => ?_⟩
    · have := h1 v.1 v.2; rw [hext] at this
      have hfl : floorB D v.1 → D.stubTime < τ v := by
        rintro ⟨c, hc, hch⟩
        have := h2 c v.1 hch (Or.inr v.2)
        rwa [extendFix_stub D τ c hc, hext] at this
      unfold lsF
      split_ifs with hf
      · exact ⟨max_le this.1.1 (hfl hf).le, this.1.2.trans (by
          have := le_max_left (D.layer v.1 : ℝ) D.stubTime; linarith)⟩
      · exact this.1
    · have := h1 v.1 v.2; rw [hext] at this
      unfold capF
      refine lt_min (lt_min this.2 ?_) ?_
      · split_ifs with hf
        · exact lt_of_le_of_ne this.1.2 (hn2 v)
        · exact this.2
      · split_ifs with hc
        · obtain ⟨c, hc', hch⟩ := hc
          have := h2 v.1 c hch (Or.inl v.2)
          rwa [extendFix_stub D τ c hc', hext] at this
        · exact this.2
    · have := h2 a.1 b.1 hab (Or.inl a.2)
      rwa [hext, hext] at this
  · rintro ⟨h1, h2, h3⟩
    have hl : ∀ v : FrB G D.fix, (D.layer v.1 : ℝ) ≤ lsF D v := by
      intro v; unfold lsF; split_ifs
      · exact le_max_left _ _
      · exact le_rfl
    have hcap1 : ∀ v : FrB G D.fix, capF D v ≤ D.rootTime v.1.1.1 := fun v =>
      (min_le_left _ _).trans (min_le_left _ _)
    have hcap2 : ∀ v : FrB G D.fix, floorB D v.1 → capF D v ≤ (D.layer v.1 : ℝ) + 1 := fun v hf => by
      unfold capF
      refine (min_le_left _ _).trans ((min_le_right _ _).trans ?_)
      rw [if_pos hf]
    have hcap3 : ∀ v : FrB G D.fix, capB D v.1 → capF D v ≤ D.stubTime := fun v hc => by
      unfold capF
      refine (min_le_right _ _).trans ?_
      rw [if_pos hc]
    refine ⟨fun v hv => ?_, fun v u hvu hfree => ?_⟩
    · have hV := h1 ⟨v, hv⟩
      have hV2 := h2 ⟨v, hv⟩
      rw [hext ⟨v, hv⟩]
      refine ⟨⟨(hl ⟨v, hv⟩).trans hV.1, ?_⟩, hV2.trans_le (hcap1 _)⟩
      by_cases hf : floorB D v
      · exact (hV2.trans_le (hcap2 ⟨v, hv⟩ hf)).le
      · have : lsF D ⟨v, hv⟩ = D.layer v := by unfold lsF; rw [if_neg hf]
        have := hV.2; rwa [‹lsF D ⟨v, hv⟩ = D.layer v›] at this
    · by_cases hvs : v ∈ D.stubs
      · have hu : u ∉ D.stubs := by
          rcases hfree with h | h
          · exact absurd h (by rw [fix_stub D v hvs]; simp)
          · exact (fix_none_iff D u).mp h
        have huf : D.fix u = none := (fix_none_iff D u).mpr hu
        have hfl : floorB D u := ⟨v, hvs, hvu⟩
        rw [extendFix_stub D τ v hvs, hext ⟨u, huf⟩]
        have h1u := (h1 ⟨u, huf⟩).1
        have : lsF D ⟨u, huf⟩ = max (D.layer u : ℝ) D.stubTime := by unfold lsF; rw [if_pos hfl]
        rw [this] at h1u
        exact lt_of_le_of_ne (le_trans (le_max_right _ _) h1u) (fun h => hn1 ⟨u, huf⟩ h.symm)
      · have hvf : D.fix v = none := (fix_none_iff D v).mpr hvs
        by_cases hus : u ∈ D.stubs
        · rw [extendFix_stub D τ u hus, hext ⟨v, hvf⟩]
          exact (h2 ⟨v, hvf⟩).trans_le (hcap3 ⟨v, hvf⟩ ⟨u, hus, hvu⟩)
        · have huf : D.fix u = none := (fix_none_iff D u).mpr hus
          rw [hext ⟨v, hvf⟩, hext ⟨u, huf⟩]
          exact h3 ⟨v, hvf⟩ ⟨u, huf⟩ hvu


/-- The designated factor: the stubs' fixed-clock phases. -/
noncomputable def stubPhase (D : SplicedKernelDataST G d) (α : GBranch G.tree → ℝ) : ℂ :=
  ∏ b : {b : GBranch G.tree // ¬ D.fix b = none},
    Complex.exp ((Real.pi * α b.1 * D.stubTime : ℝ) * Complex.I)

theorem norm_stubPhase (D : SplicedKernelDataST G d) (α : GBranch G.tree → ℝ) : ‖stubPhase D α‖ = 1 := by
  unfold stubPhase
  rw [norm_prod]
  exact Finset.prod_eq_one fun _ _ => Complex.norm_exp_ofReal_mul_I _

/-- **B_ST is the generic Fourier transform of the free-clock domain** (norm). -/
theorem enorm_splicedFourierBST_eq (D : SplicedKernelDataST G d) (α : GBranch G.tree → ℝ) :
    ‖splicedFourierBST G D.layer D.rootTime D.fix α‖ₑ =
      ‖Phi (Om0 (chF D) (lsF D) (capF D)) (lsF D) ∅ (fun v : FrB G D.fix => α v.1)‖ₑ := by
  unfold splicedFourierBST Phi
  have hpt : ∀ τ : FrB G D.fix → ℝ, τ ∉ nullF D →
      (splicedTimeDomainFix G D.layer D.rootTime D.fix).indicator
        (fun t => ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * t v : ℝ) * Complex.I))
        (G.extendFix D.fix τ) =
      stubPhase D α * (Om0 (chF D) (lsF D) (capF D)).indicator
        (famInt (lsF D) ∅ (fun v : FrB G D.fix => α v.1)) τ := by
    intro τ hτ
    have hprod : ∏ v : GBranch G.tree, Complex.exp ((Real.pi * α v * G.extendFix D.fix τ v : ℝ) * Complex.I) =
        (∏ v : FrB G D.fix, Complex.exp ((Real.pi * α v.1 * τ v : ℝ) * Complex.I)) * stubPhase D α := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (fun b : GBranch G.tree => D.fix b = none)]
      congr 1
      · refine Finset.prod_congr rfl fun v _ => ?_
        rw [extendFix_free D.fix τ v.1 v.2]
      · unfold stubPhase
        refine Finset.prod_congr rfl fun b _ => ?_
        rw [extendFix_stub D τ b.1 (by
          by_contra h; exact b.2 ((fix_none_iff D b.1).mpr h))]
    by_cases hm : G.extendFix D.fix τ ∈ splicedTimeDomainFix G D.layer D.rootTime D.fix
    · have hm' := (domFix_iff D τ hτ).mp hm
      rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm', hprod, mul_comm]
      simp [famInt]
    · have hm' : τ ∉ Om0 (chF D) (lsF D) (capF D) := fun h => hm ((domFix_iff D τ hτ).mpr h)
      rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem hm', mul_zero]
  have hae : ∀ᵐ τ : FrB G D.fix → ℝ, τ ∉ nullF D := measure_eq_zero_iff_ae_notMem.mp (volume_nullF D)
  rw [integral_congr_ae (hae.mono hpt), integral_const_mul, enorm_mul]
  have : ‖stubPhase D α‖ₑ = 1 := by rw [← ofReal_norm_eq_enorm, norm_stubPhase]; simp
  rw [this, one_mul]

end WaveTurbulence.FlowerP5
