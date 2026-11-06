/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalMixtureSplit

/-! # Actual temporal and moving-root L1 for the physical tree error density -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT WithLp

/-- Original profile regularity and joint coefficient L1 give actual error-density L1. -/
theorem tree_physical_normalized_error_integrable {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {L : ℝ} (hL : 1 ≤ L) (δ γ : ℝ)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    {C : ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : SymReg C) (hiC : Integrable (Function.uncurry C))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    Integrable (fun lam => treeNormalizedScalar hX (treePhysicalErrorScalar L δ γ J C) S lam u) := by
  let R := fun (lam : ℝ × ℝ) β γ' z =>
    treeProfileArrayScalar (d := d) L (2*δ*L^(2*γ)) treeWickArrayWeight z β γ' J C lam
  obtain ⟨E,-,-,hiE,hbE⟩ := treeProfileArrayScalar_uniform_integrable_envelope hL (2*δ*L^(2*γ))
    treeWickArrayWeight zero_le_one treeWickArrayWeight_norm_le J hC
  have hmR (z) : StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) × (Fin (X.treeLinks (G.sig 0)).length → Mom d)) =>
      R p.1 p.2.1 p.2.2 z) := stronglyMeasurable_treeProfileArrayScalar_joint L (2*δ*L^(2*γ))
        treeWickArrayWeight z J hC.meas
  have hiS := (tree_normalized_inverseProfile_qualitative hX R hmR E hiE hbE S).1 u
  have hiA : Integrable (fun lam => treeNormalizedScalar hX
      (fun lam β γ' z => approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) :=
    (tree_integrable_approxApp_profile L (2*δ) γ J hiC
      (halfCellAmplitude u.1.2.val (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2)).div_const _
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*(X.treeLinks (G.sig 0)).length):ℝ):ℂ)
  apply ((hiS.sub hiA).const_mul q).congr
  apply ae_of_all
  intro lam
  change q*(treeNormalizedScalar hX R S lam u - treeNormalizedScalar hX
    (fun lam β γ' z => approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) = _
  unfold treeNormalizedScalar
  dsimp only [R]
  rw [← sub_div,← mul_div_assoc]
  exact congrArg (fun v : ℂ => v/(treeLeafModulationWeight u.2:ℂ))
    (tree_physical_profile_sub_leading (zero_lt_one.trans_le hL) δ γ J C u.1.2.val
      (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2 lam)

/-- Actual source leaf moments justify the complete physical error moving-root integral. -/
theorem tree_physical_error_mixture_integrable {d K M : ℕ} {G : Garden 1} {X : RegChain}
    (hd : 3 ≤ d) (hX : X.DecodesTree G) {L : ℝ} (hL : 1 ≤ L) (δ γ : ℝ)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    {C : ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : SymReg C) (hiC : Integrable (Function.uncurry C))
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ) {B Ccover : ℝ}
    (hK : d+2 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (f a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^(X.treeLinks (G.sig 0)).length)
    (t : Fin 2 → ℝ) (k : Mom d) :
    Integrable (fun u => rootAmplitudeSum (treeRootLeafAmplitude f S) k u * pairedInverseProfile
      (fun lam => treeNormalizedScalar hX (treePhysicalErrorScalar L δ γ J C) S lam u) t)
        (treeLeafCellMeasure S) := by
  let R := fun (lam : ℝ × ℝ) β γ' z =>
    treeProfileArrayScalar (d := d) L (2*δ*L^(2*γ)) treeWickArrayWeight z β γ' J C lam
  obtain ⟨E,-,-,hiE,hbE⟩ := treeProfileArrayScalar_uniform_integrable_envelope hL (2*δ*L^(2*γ))
    treeWickArrayWeight zero_le_one treeWickArrayWeight_norm_le J hC
  have hmR (z) : StronglyMeasurable (fun p : (ℝ × ℝ) ×
      ((Fin (X.treeLinks (G.sig 0)).length → Mom d) × (Fin (X.treeLinks (G.sig 0)).length → Mom d)) =>
      R p.1 p.2.1 p.2.2 z) := stronglyMeasurable_treeProfileArrayScalar_joint L (2*δ*L^(2*γ))
        treeWickArrayWeight z J hC.meas
  have hQual := tree_normalized_inverseProfile_qualitative hX R hmR E hiE hbE S
  have hiS := integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar f hK hM hB hf S hS
    (fun u => pairedInverseProfile (fun lam => treeNormalizedScalar hX R S lam u) t)
    (hQual.2.1 t) (hQual.2.2 t) k
  obtain ⟨D,-,hmD,hbD⟩ := exists_treeLeadingScalar_control hd hX J S
  have hiLead := integrable_rootAmplitudeSum_treeRootLeaf_mul_scalar f hK hM hB hf S hS
    (treeNormalizedScalar hX (fun _ β γ z => singInt J (halfCellAmplitude z β γ)) S (0,0)) hmD hbD k
  have hiA : Integrable (fun u => rootAmplitudeSum (treeRootLeafAmplitude f S) k u *
      pairedInverseProfile (fun lam => treeNormalizedScalar hX (fun lam β γ' z =>
        approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) t)
        (treeLeafCellMeasure S) := by
    simp_rw [tree_paired_normalized_approxApp_eq hX L (2*δ) γ J hiC]
    convert hiLead.const_mul ((((L^(2*(d:ℝ)-2*γ)*(2*δ)⁻¹:ℝ):ℂ)^(X.treeLinks (G.sig 0)).length) *
      (∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1))) using 1
    funext u
    ring
  let q : ℂ := (((δ/(2*L^((d:ℝ)-γ)))^(2*(X.treeLinks (G.sig 0)).length):ℝ):ℂ)
  apply ((hiS.const_mul q).sub (hiA.const_mul q)).congr
  apply ae_of_all
  intro u
  simp only [Pi.sub_apply]
  have he := tree_physical_normalized_inverse_sub_leading hX hL δ γ J hC hiC S t u
  change q*_ - q*_ = _ at he
  calc
    _ = rootAmplitudeSum (treeRootLeafAmplitude f S) k u * (q*pairedInverseProfile
        (fun lam => treeNormalizedScalar hX R S lam u) t - q*pairedInverseProfile
        (fun lam => treeNormalizedScalar hX (fun lam β γ' z => approxApp L (2*δ) γ J
          (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) t) := by ring
    _ = _ := by rw [he]

end WaveTurbulence.RA1Leafwise
