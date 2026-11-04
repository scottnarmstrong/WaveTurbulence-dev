/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.GroupedTimeMeasure

/-!
# Grouped input-box measures

An arbitrary coordinate box becomes the exact product of its linear,
pair and normal boxes. The corresponding set-integral Tonelli identity
retains every interval endpoint, ready for the enlarged source boxes.
-/

public section

open MeasureTheory Set ENNReal

namespace WaveTurbulence.Sumint

/-- The box for all distinguished linear times. -/
@[expose] def linearFamilyBox (S : SumintShape) (lo hi : S.TVar → ℝ) : Set (Fin S.I → ℝ) :=
  Icc (fun i => lo (.inl ⟨i,0⟩)) (fun i => hi (.inl ⟨i,0⟩))

/-- The box for all outer/inner pair-time tuples. -/
@[expose] def pairFamilyBox (S : SumintShape) (lo hi : S.TVar → ℝ) :
    Set ((Σ i : Fin S.I, Fin (S.m i)) → ℝ × ℝ) :=
  Icc (fun a => (lo (.inl ⟨a.1,a.2.succ⟩),lo (.inr (.inl a))))
    (fun a => (hi (.inl ⟨a.1,a.2.succ⟩),hi (.inr (.inl a))))

/-- The box for all normal-time triples. -/
@[expose] def normalFamilyBox (S : SumintShape) (lo hi : S.TVar → ℝ) :
    Set ({i : Fin S.I // S.nor i = true} → Fin 3 → ℝ) :=
  Icc (fun i j => lo (.inr (.inr ⟨i,j⟩))) (fun i j => hi (.inr (.inr ⟨i,j⟩)))

/-- The inverse image of the grouped boxes is precisely the original input box. -/
theorem preimage_grouped_time_boxes (S : SumintShape) (lo hi : S.TVar → ℝ) :
    measurableTimeGrouping S ⁻¹'
      (linearFamilyBox S lo hi ×ˢ (pairFamilyBox S lo hi ×ˢ normalFamilyBox S lo hi)) = Icc lo hi := by
  ext τ
  constructor
  · rintro ⟨h0,hp,hn⟩
    constructor
    · rintro (⟨i,j⟩ | (a | ⟨i,j⟩))
      · refine Fin.cases (h0.1 i) (fun k => (hp.1 ⟨i,k⟩).1) j
      · exact (hp.1 a).2
      · exact hn.1 i j
    · rintro (⟨i,j⟩ | (a | ⟨i,j⟩))
      · refine Fin.cases (h0.2 i) (fun k => (hp.2 ⟨i,k⟩).1) j
      · exact (hp.2 a).2
      · exact hn.2 i j
  · intro h
    exact ⟨⟨fun i => h.1 _,fun i => h.2 _⟩,
      ⟨fun a => ⟨h.1 _,h.1 _⟩,fun a => ⟨h.2 _,h.2 _⟩⟩,
      ⟨fun i j => h.1 _,fun i j => h.2 _⟩⟩

/-- Exact set-integral Tonelli identity in grouped time families. -/
theorem lintegral_input_box_grouped (S : SumintShape) (lo hi : S.TVar → ℝ)
    (f : GroupedTimes S → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ τ in Icc lo hi, f (measurableTimeGrouping S τ)) =
      ∫⁻ u in linearFamilyBox S lo hi,
        ∫⁻ p in pairFamilyBox S lo hi,
          ∫⁻ n in normalFamilyBox S lo hi, f (u,p,n) := by
  let B := linearFamilyBox S lo hi ×ˢ (pairFamilyBox S lo hi ×ˢ normalFamilyBox S lo hi)
  have hB : MeasurableSet B := measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)
  have hp := (volume_preserving_measurableTimeGrouping S).restrict_preimage hB
  rw [preimage_grouped_time_boxes S lo hi] at hp
  rw [hp.lintegral_comp_emb (measurableTimeGrouping S).measurableEmbedding f]
  change (∫⁻ z in B, f z) = _
  rw [Measure.volume_eq_prod,← Measure.prod_restrict,
    lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro u
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  exact lintegral_prod _ ((hf.comp (measurable_const.prodMk measurable_id)).aemeasurable)

end WaveTurbulence.Sumint
