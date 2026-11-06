/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalErrorIntegrability

/-! # The complete original finite physical error family shares one inverse profile -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT

/-- Original coefficient and input norms justify collecting every physical error into
one actual original-frequency density before taking the mixed norm. -/
theorem tree_finite_physical_errors_eq_profile {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hd : 3 ≤ d) (hX : X.DecodesTree G) {ι : Type*} [Fintype ι]
    {L : ℝ} (hL : 1 ≤ L) (δ γ : ℝ)
    (J : ι → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : ι) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i)) (hiC : ∀ i, Integrable (Function.uncurry (C i))) (c : ι → ℂ)
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B Ccover : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ q, ((S q).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length)
    (t : Fin 2 → ℝ) (k : Mom d) :
    (∑ i, c i*(∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u * pairedInverseProfile
      (fun lam => treeNormalizedScalar hX (treePhysicalErrorScalar L δ γ (J i) (C i)) S lam u) t
        ∂treeLeafCellMeasure S)) =
      ∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u * pairedInverseProfile
        (fun lam => ∑ i, c i*treeNormalizedScalar hX (treePhysicalErrorScalar L δ γ (J i) (C i)) S lam u) t
          ∂treeLeafCellMeasure S := by
  classical
  have hi (i : ι) := tree_physical_error_mixture_integrable hd hX hL δ γ (J i) (hC i) (hiC i)
    f hK hM hB hf S hS t k
  have hiLam (i : ι) (u) := tree_physical_normalized_error_integrable hX hL δ γ (J i) (hC i) (hiC i) S u
  calc
    _ = ∫ u, ∑ i, c i*(rootAmplitudeSum (treeRootLeafAmplitude f S) k u * pairedInverseProfile
        (fun lam => treeNormalizedScalar hX (treePhysicalErrorScalar L δ γ (J i) (C i)) S lam u) t)
          ∂treeLeafCellMeasure S := by
      rw [integral_finsetSum _ (fun i _ => (hi i).const_mul (c i))]
      exact Finset.sum_congr rfl (fun _ _ => (integral_const_mul _ _).symm)
    _ = _ := by
      apply integral_congr_ae
      apply ae_of_all
      intro u
      dsimp only
      rw [tree_pairedInverseProfile_finsetSum Finset.univ _ (fun i _ => (hiLam i u).const_mul (c i))]
      simp_rw [tree_pairedInverseProfile_const_mul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)

end WaveTurbulence.RA1Leafwise
