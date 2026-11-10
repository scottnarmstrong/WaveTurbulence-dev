/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.InputGrouping
public import WaveTurbulence.Foundations.SumintPar.ProductMeasureTools

/-!
# Exact product measure for the grouped time families

The linear times, pair-time tuples and normal-time triples have the
literal product Lebesgue measure. Integrating the pairs before the
linear times keeps the case-(a) middle time fixed, and its already
proved pair estimate is uniform in that middle time.
-/

@[expose] public section
set_option autoImplicit false

open MeasureTheory Set ENNReal

namespace WaveTurbulence.SumintPar

/-- The three literal source time families. -/
abbrev GroupedTimes (S : SumintShape) := (Fin S.I → ℝ) ×
  ((Σ i : Fin S.I, Fin (S.m i)) → ℝ × ℝ) ×
  ({i : Fin S.I // S.nor i = true} → Fin 3 → ℝ)

/-- The explicit source grouping as a measurable equivalence. -/
@[expose] noncomputable def measurableTimeGrouping (S : SumintShape) :
    (S.TVar → ℝ) ≃ᵐ (Fin S.I → ℝ) ×
      ((Σ i : Fin S.I, Fin (S.m i)) → ℝ × ℝ) ×
      ({i : Fin S.I // S.nor i = true} → Fin 3 → ℝ) where
  toEquiv := timeGroupingEquiv S ℝ
  measurable_toFun := by
    change Measurable (fun x : S.TVar → ℝ =>
      (fun i => x (.inl ⟨i,0⟩),
        (fun p : Σ i : Fin S.I, Fin (S.m i) => (x (.inl ⟨p.1,p.2.succ⟩),x (.inr (.inl p)))),
        fun (i : {i : Fin S.I // S.nor i = true}) (j : Fin 3) => x (.inr (.inr ⟨i,j⟩))))
    fun_prop
  measurable_invFun := by
    apply measurable_pi_iff.mpr
    intro a
    rcases a with ⟨i,j⟩ | (p | ⟨i,j⟩)
    · refine Fin.cases ?_ (fun k => ?_) j
      · change Measurable (fun z : GroupedTimes S => z.1 i)
        fun_prop
      · change Measurable (fun z : GroupedTimes S => (z.2.1 ⟨i,k⟩).1)
        fun_prop
    · change Measurable (fun z : (Fin S.I → ℝ) ×
        ((Σ i : Fin S.I, Fin (S.m i)) → ℝ × ℝ) ×
        ({i : Fin S.I // S.nor i = true} → Fin 3 → ℝ) => (z.2.1 p).2)
      fun_prop
    · change Measurable (fun z : (Fin S.I → ℝ) ×
        ((Σ i : Fin S.I, Fin (S.m i)) → ℝ × ℝ) ×
        ({i : Fin S.I // S.nor i = true} → Fin 3 → ℝ) => z.2.2 i j)
      fun_prop

/-- The explicit grouping preserves the exact product Lebesgue measure, with no dimension constant. -/
theorem volume_preserving_measurableTimeGrouping (S : SumintShape) :
    MeasurePreserving (measurableTimeGrouping S) volume volume := by
  let e := measurableTimeGrouping S
  have hi : MeasurePreserving e.symm volume volume := by
    refine ⟨e.symm.measurable,(Measure.pi_eq fun s hs => ?_).symm⟩
    have hpre : e.symm ⁻¹' Set.pi Set.univ s =
        (Set.pi Set.univ (fun i : Fin S.I => s (.inl ⟨i,0⟩))) ×ˢ
        ((Set.pi Set.univ (fun p : Σ i : Fin S.I, Fin (S.m i) =>
          s (.inl ⟨p.1,p.2.succ⟩) ×ˢ s (.inr (.inl p)))) ×ˢ
        Set.pi Set.univ (fun i : {i : Fin S.I // S.nor i = true} =>
          Set.pi Set.univ (fun j : Fin 3 => s (.inr (.inr ⟨i,j⟩))))) := by
      ext z
      simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_prod]
      constructor
      · intro h
        exact ⟨fun i => h (.inl ⟨i,0⟩),fun p => ⟨h (.inl ⟨p.1,p.2.succ⟩),h (.inr (.inl p))⟩,
          fun i j => h (.inr (.inr ⟨i,j⟩))⟩
      · rintro ⟨h0,hp,hn⟩ a
        rcases a with ⟨i,j⟩ | (p | ⟨i,j⟩)
        · refine Fin.cases (h0 i) (fun k => (hp ⟨i,k⟩).1) j
        · exact (hp p).2
        · exact hn i j
    rw [e.symm.map_apply,hpre]
    simp only [Measure.volume_eq_prod,volume_pi,Measure.prod_prod,Measure.pi_pi]
    simp only [Fintype.prod_sum_type,Fintype.prod_sigma,Fin.prod_univ_succ,Finset.prod_mul_distrib]
    ring
  exact MeasurePreserving.symm e.symm hi

end WaveTurbulence.SumintPar
