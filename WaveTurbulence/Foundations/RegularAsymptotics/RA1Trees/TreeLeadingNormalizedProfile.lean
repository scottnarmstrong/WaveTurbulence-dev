/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegAsymp.TreeLeadingProfile
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeLeadingSpatialEstimate

/-! # The actual leading profile mixture separates into its original time and spatial factors -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT WithLp Incoh Links IncohInst

/-- The actual normalized leading inverse profile has its original coefficient time
factor; the one leaf-moment divisor remains only with the singular spatial factor. -/
theorem tree_paired_normalized_approxApp_eq {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (L δ γ : ℝ)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    {C : ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hiC : Integrable (Function.uncurry C))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ)
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    pairedInverseProfile (fun lam => treeNormalizedScalar hX
      (fun lam β γ' z => approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) t =
      (((L^(2*(d:ℝ)-2*γ)*δ⁻¹:ℝ):ℂ)^(X.treeLinks (G.sig 0)).length *
        (∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1))) *
          treeNormalizedScalar hX (fun _ β γ' z => singInt J (halfCellAmplitude z β γ')) S (0,0) u := by
  unfold treeNormalizedScalar
  dsimp only
  rw [tree_pairedInverseProfile_div_const,tree_paired_approxApp_eq_time_coefficient L δ γ J hiC]
  ring

/-- The actual leading source mixture factors into the original integrated coefficient
and the checked singular spatial mixture, before recursive Nstar identification. -/
theorem tree_leading_profile_mixture_eq {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (L δ γ : ℝ)
    (J : Finset (Fin (X.treeLinks (G.sig 0)).length))
    {C : ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J} → ℝ) → ℝ × ℝ → ℂ}
    (hiC : Integrable (Function.uncurry C))
    (f : Fin (Fintype.card (TPlus G)) → Mom d → ℂ)
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ) (k : Mom d) :
    (∫ u, rootAmplitudeSum (treeRootLeafAmplitude f S) k u *
      pairedInverseProfile (fun lam => treeNormalizedScalar hX
        (fun lam β γ' z => approxApp L δ γ J (fun Ω => C (ofLp Ω) lam) (halfCellAmplitude z β γ')) S lam u) t
          ∂treeLeafCellMeasure S) =
      (((L^(2*(d:ℝ)-2*γ)*δ⁻¹:ℝ):ℂ)^(X.treeLinks (G.sig 0)).length *
        (∫ β, ∫ lam, C β lam*e2 lam (t 0) (t 1))) * treeLeadingSpatialProfile hX J f S k := by
  simp_rw [tree_paired_normalized_approxApp_eq hX L δ γ J hiC]
  unfold treeLeadingSpatialProfile
  conv_rhs => rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => by ring)

end WaveTurbulence.RegAsymp
