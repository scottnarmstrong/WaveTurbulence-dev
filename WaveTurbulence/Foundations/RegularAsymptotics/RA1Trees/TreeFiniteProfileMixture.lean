/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeNormalizedFiniteProfiles
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeProfileScalarMass
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeQualitativeInverseProfile

/-! # Exact finite original time-profile decomposition of the full tree Fourier mixture -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT WithLp Incoh Links IncohInst

/-- Original qualitative profile regularity and finite spatial input norms justify the
finite special-set exchange through the actual moving-root integral. This identity has
no assumed time/spatial estimate or substituted source kernel. -/
theorem tree_leaf_mixture_finite_profiles {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {ι : Type*} [Fintype ι] {L : ℝ} (hL : 1 ≤ L) (μ : ℝ)
    (W : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    {D : ℝ} (hD : 0 ≤ D) (hW : ∀ g, ‖W g‖ ≤ D)
    (a : ι → ℂ) (J : ι → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : ι) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i))
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B Ccover : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ b, Fourier.spatialNorm K M (f b) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length)
    (t : Fin 2 → ℝ) (k : Mom d) :
    (∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u *
      treeBoundedScalar hX L (fun g => W g *
        ∑ i, a i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
          (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam (t 0) (t 1)) S u
            ∂treeLeafCellMeasure S) =
      ∑ i, a i * ∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX
          (fun lam β γ z => treeProfileArrayScalar L μ W z β γ (J i) (C i) lam) S lam u) t
            ∂treeLeafCellMeasure S := by
  classical
  let R := fun i (lam : ℝ × ℝ) β γ z => treeProfileArrayScalar (d := d) L μ W z β γ (J i) (C i) lam
  have hQual (i : ι) :
      (∃ E : (ℝ × ℝ) → ℝ, Integrable E ∧
        (∀ z, StronglyMeasurable (fun p : (ℝ × ℝ) ×
          ((Fin (X.treeLinks (G.sig 0)).length → Mom d) ×
            (Fin (X.treeLinks (G.sig 0)).length → Mom d)) => R i p.1 p.2.1 p.2.2 z)) ∧
        ∀ᵐ lam, ∀ z β γ, ‖R i lam β γ z‖ ≤ E lam) := by
    obtain ⟨E,-,-,hiE,hbE⟩ := treeProfileArrayScalar_uniform_integrable_envelope hL μ W hD hW (J i) (hC i)
    exact ⟨E,hiE,fun z => stronglyMeasurable_treeProfileArrayScalar_joint L μ W z (J i) (hC i).meas,hbE⟩
  have hi (i : ι) : Integrable (fun u => a i *
      (rootAmplitudeSum (treeRootLeafAmplitude f S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (R i) S lam u) t))
        (treeLeafCellMeasure S) := by
    obtain ⟨E,hiE,hmR,hbR⟩ := hQual i
    have hq := tree_normalized_inverseProfile_qualitative hX (R i) hmR E hiE hbR S
    exact (integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar f hK hM hB hf S hS
      (fun u => pairedInverseProfile (fun lam => treeNormalizedScalar hX (R i) S lam u) t)
      (hq.2.1 t) (hq.2.2 t) k).const_mul (a i)
  calc
    _ = ∫ u, ∑ i, a i * (rootAmplitudeSum (treeRootLeafAmplitude f S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (R i) S lam u) t)
          ∂treeLeafCellMeasure S := by
      apply integral_congr_ae
      apply ae_of_all
      intro u
      dsimp only
      rw [treeBoundedScalar_finite_profiles hX (zero_lt_one.trans_le hL) μ W a J C hC S t u,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, ∫ u, a i * (rootAmplitudeSum (treeRootLeafAmplitude f S) k u *
        pairedInverseProfile (fun lam => treeNormalizedScalar hX (R i) S lam u) t)
          ∂treeLeafCellMeasure S := integral_finsetSum _ (fun i _ => hi i)
    _ = _ := Finset.sum_congr rfl (fun _ _ => integral_const_mul _ _)

end WaveTurbulence.RegAsymp
