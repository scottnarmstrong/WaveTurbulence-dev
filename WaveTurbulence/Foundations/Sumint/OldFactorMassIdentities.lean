/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Sumint.CoreUnorderedMass
public import WaveTurbulence.Foundations.Sumint.SourceLinearMass

/-!
# Literal old-factor window masses in the original one-, two-, and three-time coordinates

These changes of variables identify the coarse factor integrals with
the previously estimated source window masses.
-/

public section
open MeasureTheory Set ENNReal
open scoped Classical
namespace WaveTurbulence.Sumint

/-- The distinguished old-factor interval is the inverse image of its actual scalar source interval. -/
theorem oldFactorTimeBox_linear {d : ℕ} (D : SumintDatum d) (c h : ℝ) (i : Fin D.S.I) :
    oldFactorTimeBox D c h (.inl i) =
      (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹'
        Icc (enlargedTimeLower D c h (.inl ⟨i,0⟩)) (enlargedTimeUpper D c h (.inl ⟨i,0⟩)) := by
  ext z
  constructor
  · intro hz
    exact hz 0 (Set.mem_univ _)
  · intro hz j _
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hz

/-- The distinguished old-factor mass is exactly the already estimated scalar source mass. -/
theorem oldFactorWindowMass_linear {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (i : Fin D.S.I) :
    oldFactorWindowMass D L γ δ η p ν r t c h (.inl i) =
      linearFactorMass D L γ δ p ν r t c h i := by
  unfold oldFactorWindowMass
  rw [oldFactorTimeBox_linear]
  let ei : FactorCoordinate D.S (.inl i) ≃ Fin 1 := Equiv.refl _
  let e := (MeasurableEquiv.piCongrLeft (fun _ => ℝ) ei).trans (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have hp : MeasurePreserving e volume volume :=
    (volume_preserving_funUnique (Fin 1) ℝ).comp (volume_measurePreserving_piCongrLeft (fun _ => ℝ) ei)
  have he := hp.setLIntegral_comp_preimage_emb e.measurableEmbedding
    (fun s => ENNReal.ofReal ‖linearTimeSum D L γ δ p ν r t i s‖)
    (Icc (enlargedTimeLower D c h (.inl ⟨i,0⟩)) (enlargedTimeUpper D c h (.inl ⟨i,0⟩)))
  have hev (z : FactorCoordinate D.S (.inl i) → ℝ) : e z = z 0 := rfl
  have hef : (e : (FactorCoordinate D.S (.inl i) → ℝ) → ℝ) = MeasurableEquiv.funUnique (Fin 1) ℝ := rfl
  simpa only [sourceTimeNormFactor,timeGapFactor,plainTimeNormFactor,one_mul,linearFactorMass,hev,hef] using he

/-- The normal old-factor interval is already in its native three-time coordinate space. -/
theorem oldFactorWindowMass_normal {d : ℕ} (D : SumintDatum d) (L γ δ η : ℝ)
    (p : D.S.VIdx → Fin d → ℝ) (ν : D.S.VIdx → Mom d) (r : Mom d) (t c h : ℝ)
    (i : {i : Fin D.S.I // D.S.nor i = true}) :
    oldFactorWindowMass D L γ δ η p ν r t c h (.inr (.inr i)) =
      normalFactorMass D L γ δ p ν r t (enlargedTimeLower D c h) (enlargedTimeUpper D c h) i := by
  have hbox : oldFactorTimeBox D c h (.inr (.inr i)) =
      Icc (fun j => enlargedTimeLower D c h (.inr (.inr ⟨i,j⟩)))
        (fun j => enlargedTimeUpper D c h (.inr (.inr ⟨i,j⟩))) := by
    ext z
    simp only [oldFactorTimeBox,Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Icc,Pi.le_def]
    exact forall_and
  unfold oldFactorWindowMass
  rw [hbox]
  simp only [sourceTimeNormFactor,timeGapFactor,plainTimeNormFactor,one_mul,normalFactorMass]

end WaveTurbulence.Sumint
