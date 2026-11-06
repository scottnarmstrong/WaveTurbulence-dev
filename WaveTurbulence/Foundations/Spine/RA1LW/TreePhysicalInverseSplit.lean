/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreePhysicalScalarSplit
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeQualitativeInverseProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeProfileScalarMass
public import WaveTurbulence.Foundations.RegAsymp.TreeLeadingIntegrability
public import WaveTurbulence.Foundations.RegAsymp.TreeProfileLinearity

/-! # Lawful original-frequency subtraction at the physical tree scale -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory ApproxNT Incoh Links IncohInst WithLp ClassJR

/-- Original SymReg and joint coefficient L1 justify the exact temporal subtraction.
No integrability or linearity of an arbitrary singular operation is assumed. -/
theorem tree_physical_normalized_inverse_sub_leading {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {L : ℝ} (hL : 1 ≤ L) (δ γ : ℝ)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    {C : ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hC : SymReg C) (hiC : Integrable (Function.uncurry C))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ)
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    (((δ/(2*L^((d:ℝ)-γ)))^(2*(X.treeLinks (G.sig 0)).length):ℝ):ℂ)*
      pairedInverseProfile (fun lam => treeNormalizedScalar hX
        (fun lam β γ' z => treeProfileArrayScalar L (2*δ*L^(2*γ)) treeWickArrayWeight z β γ' J C lam) S lam u) t -
    (((δ/(2*L^((d:ℝ)-γ)))^(2*(X.treeLinks (G.sig 0)).length):ℝ):ℂ)*
      pairedInverseProfile (fun lam => treeNormalizedScalar hX
        (fun lam β γ' z => approxApp L (2*δ) γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) t =
      pairedInverseProfile (fun lam => treeNormalizedScalar hX
        (treePhysicalErrorScalar L δ γ J C) S lam u) t := by
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
  change q*pairedInverseProfile (fun lam => treeNormalizedScalar hX R S lam u) t - q*pairedInverseProfile _ t = _
  rw [← mul_sub,← tree_pairedInverseProfile_sub hiS hiA,
    ← tree_pairedInverseProfile_const_mul]
  apply congrArg (fun A => pairedInverseProfile A t)
  funext lam
  unfold treeNormalizedScalar
  dsimp only [R]
  rw [← sub_div,← mul_div_assoc]
  exact congrArg (fun v : ℂ => v/(treeLeafModulationWeight u.2:ℂ))
    (tree_physical_profile_sub_leading (zero_lt_one.trans_le hL) δ γ J C u.1.2.val
      (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2 lam)

end WaveTurbulence.RA1Leafwise
