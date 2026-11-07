/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.SumintPar.OldFactorMassIdentities

/-!
# Exact two-time change of variables for old source pairs

For pairs without the case-(a) strip, the old-factor window mass is the
literal orderedPairMass, uniformly in the distinguished linear times.
-/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.SumintPar

/-- The old pair mass agrees with the source pair mass whenever no case-(a) ordering is imposed. -/
theorem oldFactorWindowMass_pair {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (u : Fin D.S.I → ℝ) (a : Σ i : Fin D.S.I, Fin (D.S.m i)) (ha : ¬ caseAPair D a) :
    oldFactorWindowMass D L γ δ η p ν r t c h (.inr (.inl a)) =
      orderedPairMass D L γ δ η p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) u a := by
  let ei : FactorCoordinate D.S (.inr (.inl a)) ≃ Fin 2 := Equiv.refl _
  let e := (MeasurableEquiv.piCongrLeft (fun _ => ℝ) ei).trans (MeasurableEquiv.finTwoArrow (α := ℝ))
  have hp : MeasurePreserving e volume volume :=
    (volume_preserving_finTwoArrow ℝ).comp (volume_measurePreserving_piCongrLeft (fun _ => ℝ) ei)
  have hbox : oldFactorTimeBox D c h (.inr (.inl a)) = e ⁻¹'
      Icc (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeLower D c h (.inr (.inl a)))
        (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeUpper D c h (.inr (.inl a))) := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨(hz 0 (Set.mem_univ _)).1,(hz 1 (Set.mem_univ _)).1⟩,
        ⟨(hz 0 (Set.mem_univ _)).2,(hz 1 (Set.mem_univ _)).2⟩⟩
    · intro hz j _
      fin_cases j
      · exact ⟨hz.1.1,hz.2.1⟩
      · exact ⟨hz.1.2,hz.2.2⟩
  unfold oldFactorWindowMass
  rw [hbox]
  have he := hp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun z => ENNReal.ofReal (orderedPairNorm D L γ δ η p ν r t u a z))
    (Icc (enlargedTimeLower D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeLower D c h (.inr (.inl a)))
      (enlargedTimeUpper D c h (.inl ⟨a.1,a.2.succ⟩),enlargedTimeUpper D c h (.inr (.inl a))))
  have hev (z : FactorCoordinate D.S (.inr (.inl a)) → ℝ) : e z = (z 0,z 1) := rfl
  simpa only [orderedPairNorm,ite_eq_right ha,hev,sourceTimeNormFactor,timeGapFactor,plainTimeNormFactor,
    orderedPairMass] using he

end WaveTurbulence.SumintPar
