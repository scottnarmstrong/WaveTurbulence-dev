/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeFiniteProfileScalar
public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeBoundedScalarProfile

/-! # Exact finite source profiles after the original tree leaf-moment normalization -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory ClassJR ApproxNT WithLp Incoh Links IncohInst

/-- The tree's single leaf-moment divisor commutes exactly with the original temporal
inverse profile and the finite source special-set expansion. -/
theorem treeBoundedScalar_finite_profiles {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L) (μ : ℝ)
    (W : ((Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ) ×
      (Fin (X.treeLinks (G.sig 0)).length → Fin d → ℤ)) → ℂ)
    (a : ι → ℂ) (J : ι → Finset (Fin (X.treeLinks (G.sig 0)).length))
    (C : (i : ι) → ({j : Fin (X.treeLinks (G.sig 0)).length // j ∉ J i} → ℝ) → ℝ × ℝ → ℂ)
    (hC : ∀ i, SymReg (C i))
    (S : (Fin (Fintype.card (TPlus G)+1) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (G.sig 0)).length × Fin 2) → Fin d → ℤ))
    (t : Fin 2 → ℝ)
    (u : SourceCellIndex S × (Fin (Fintype.card (TPlus G)+1) → Fin d → ℝ)) :
    treeBoundedScalar hX L (fun g => W g *
      ∑ i, a i * ∫ lam, resProfile (J i) (fun Ω => C i (ofLp Ω) lam)
        (fun j => μ*inner ℝ (latticePoint L (g.1 j)) (latticePoint L (g.2 j)))*e2 lam (t 0) (t 1)) S u =
      ∑ i, a i * pairedInverseProfile
        (fun lam => treeNormalizedScalar hX
          (fun lam β γ z => treeProfileArrayScalar L μ W z β γ (J i) (C i) lam) S lam u) t := by
  classical
  unfold treeBoundedScalar treeNormalizedScalar
  dsimp only
  rw [treeHalfCellLatticeScalar_finite_profiles hL μ W a J C hC _ _ _ t]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold pairedInverseProfile
  have he : (∫ lam, (treeProfileArrayScalar L μ W u.1.2.val
      (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2 (J i) (C i) lam /
        (treeLeafModulationWeight u.2:ℂ))*e2 lam (t 0) (t 1)) =
      (∫ lam, treeProfileArrayScalar L μ W u.1.2.val
        (treeLeafModulations hX u.2).1 (treeLeafModulations hX u.2).2 (J i) (C i) lam *
          e2 lam (t 0) (t 1)) / (treeLeafModulationWeight u.2:ℂ) := by
    simp only [div_eq_mul_inv]
    rw [← integral_mul_const]
    apply integral_congr_ae
    apply ae_of_all
    intro lam
    ring
  rw [he]
  ring

end WaveTurbulence.RegAsymp
