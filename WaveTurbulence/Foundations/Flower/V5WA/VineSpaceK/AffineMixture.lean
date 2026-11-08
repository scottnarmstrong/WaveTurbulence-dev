/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.SpatialMeasure
public import WaveTurbulence.Foundations.Flower.V5WA.VineSpaceK.Certificate
/-! Exact Fourier realization of affine common data in normalized engine coordinates.
No norm estimate or covariance of the cut2 weight is assumed or proved here. -/
@[expose] public section
noncomputable section
namespace WaveTurbulence.VineSpaceK
open MeasureTheory Cut2A DegenVine VineEstS2 VineEstS3 RegRed Reg.Skeleton VineParamContract
variable {V α : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [CompleteSpace V]
  [MeasurableSpace α] {d : ℕ}

/-- C2-A's common data evaluated at an affine function of the normalized lattice.
Exterior dependence enters only a bounded scalar, not the input frequencies. -/
def affineCharMix (S : SumintShape) (F : SpatialMeasure V α)
    (A : S.VIdx → Mom d →L[ℝ] V) (c : (Fin 4 → Mom d) → V) : CharMix S d :=
  spatialCharMix S F (fun ξ v => (A v).adjoint ξ)
    ((continuous_pi fun v => (A v).adjoint.continuous).measurable)
    (fun a E => (Real.fourierChar (inner ℝ (F.frequency a) (c E)) : ℂ))
    (fun E => (continuous_subtype_val.comp Real.continuous_fourierChar).measurable.comp
      (F.frequency_measurable.inner measurable_const))
    (fun _ _ => by simp only [Circle.norm_coe, le_refl])

theorem affineCharMix_mass (S : SumintShape) (F : SpatialMeasure V α)
    (A : S.VIdx → Mom d →L[ℝ] V) (c : (Fin 4 → Mom d) → V) :
    (affineCharMix S F A c).mass = F.mass :=
  spatialCharMix_mass _ _ _ _ _ _ _

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem affine_character (S : SumintShape) (A : S.VIdx → Mom d →L[ℝ] V)
    (c ξ : V) (L : ℝ) (x : S.VIdx → Fin d → ℤ) :
    (Real.fourierChar (inner ℝ ξ c) : ℂ) *
      charOf S L (fun v => (A v).adjoint ξ) x =
    (Real.fourierChar (inner ℝ ξ (c + ∑ v, A v (latticePoint L (x v)))) : ℂ) := by
  simp only [inner_add_right, inner_sum, AddChar.map_add_eq_mul, Circle.coe_mul,
    charOf, ContinuousLinearMap.adjoint_inner_left]
  congr 1
  have hf (s : Finset S.VIdx) :
      (∏ v ∈ s, (Real.fourierChar (inner ℝ ξ (A v (latticePoint L (x v))))) : Circle) =
        Real.fourierChar (∑ v ∈ s, inner ℝ ξ (A v (latticePoint L (x v)))) := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, AddChar.map_zero_eq_one]
    | @insert v s hv ih =>
      rw [Finset.prod_insert hv, Finset.sum_insert hv, AddChar.map_add_eq_mul, ih]
  exact (map_prod Circle.coeHom _ _).symm.trans (congrArg (fun z : Circle => (z : ℂ)) (hf Finset.univ))

theorem affineCharMix_val (S : SumintShape) (F : SpatialMeasure V α)
    (A : S.VIdx → Mom d →L[ℝ] V) (c : (Fin 4 → Mom d) → V)
    (L : ℝ) (E : Fin 4 → Mom d) (x : S.VIdx → Fin d → ℤ) :
    (affineCharMix S F A c).val L E x =
      F.value (c E + ∑ v, A v (latticePoint L (x v))) := by
  rw [affineCharMix, spatialCharMix_val]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun a => by
    beta_reduce
    rw [mul_assoc, affine_character]

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)}
  {a b : GBranch G.tree}

/-- Algebraic bridge at the exact `EnginePullback` boundary: an affine coordinate
identity for every possible certificate assembly produces its actual mixture,
with exactly C2-A's mass. This does not supply the common-data coordinate map. -/
theorem enginePullback_of_affine (R : CLRegionData G U a b) (L : ℝ) (base : Mom d)
    (F : SpatialMeasure V α) (q : (GNode G.tree → Fin d → ℤ) → V)
    (hcoord : ∀ (n : ℕ) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hL : L ≠ 0),
      ∃ (A : (assemblyShape hM9 B).VIdx → Mom d →L[ℝ] V)
        (c : (Fin 4 → Mom d) → V),
      ∀ (β : Fin 4 → Fin d → ℤ)
        (hβ : ((G.sign a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3) x,
        q (clExtendIndices R ((clNormalizedChainEquiv hL B base β hβ hM9).symm x).1) =
          c (sumintBoundary (G.sign a.toNode) (fun j => base + latticePoint L (β j))) +
            ∑ v, A v (latticePoint L (x v))) :
    EnginePullback R L base (fun z => F.value (q z)) F.mass := by
  intro n hM9 B hL
  obtain ⟨A, c, hc⟩ := hcoord n hM9 B hL
  refine ⟨affineCharMix _ F A c, (affineCharMix_mass _ F A c).le, ?_⟩
  intro β hβ x
  beta_reduce
  rw [hc β hβ x, affineCharMix_val]
end WaveTurbulence.VineSpaceK
