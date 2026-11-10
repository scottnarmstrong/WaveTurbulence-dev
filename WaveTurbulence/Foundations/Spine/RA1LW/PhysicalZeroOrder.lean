/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceGardenSign
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceZeroMomentum
public import WaveTurbulence.Foundations.Spine.RA1LW.ActualTimeExpansion

/-! # The original physical couple kernel at order zero -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh MainCoef ClassJR Set

/-- The original trivial physical couple has precisely its single input
and no phase, coupling, Wick or lattice factor. -/
theorem coupleLeaves_triv {d : ℕ} (L γ δ : ℝ) (H : LGSpine.LeafProfiles 2 d)
    (LG : LayeredGarden 2) (h0 : ∀ a, LG.layer a = 0)
    (hQ : RegCpl.triv.Decodes LG.garden) {t s : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) (k : Mom d) :
    LGSpine.coupleLeaves L γ δ LG H t s k = (H (0,[]) k:ℂ) := by
  classical
  have horder : LG.garden.order = 0 := Reg.size_eq_order hQ
  have hz : LG.garden.zeta = 1 := by
    rw [decoded_couple_zeta hQ]
    unfold zetaOfTrees
    apply Finset.prod_eq_one
    intro j _
    fin_cases j <;> rfl
  have hcoeff (p : (Fin RegCpl.triv.links.length × Fin 2) → Fin d → ℤ) :
      coupleLatticeTimeCoefficient L γ δ LG hQ t s k p = 1 := by
    unfold coupleLatticeTimeCoefficient
    have hp : (∏ j : Fin RegCpl.triv.links.length, epsXY (p (j,0)) (p (j,1))^2:ℝ) = 1 := by
      rfl
    rw [hp,Complex.ofReal_one,one_mul,phaseIntegral_kDomain_eq_BtJR L γ δ LG h0 hQ _
      (by simp only [RegCpl.links,RegCpl.linksAt,List.not_mem_nil,false_implies,implies_true]) ht hs]
    rfl
  rw [coupleLeaves_latticeArray L γ δ H LG hQ t s k,horder,pow_zero,hz,one_mul,one_mul]
  simp_rw [hcoeff,one_mul]
  have hleaf (p : (Fin RegCpl.triv.links.length × Fin 2) → Fin d → ℤ) :
      (coupleMomentumData hQ hQ.1).sourceLeafWeight (leafFam hQ hQ.1 H) k
        (fun i j => latticePoint L (p (i,j))) = (H (0,[]) k:ℂ) :=
    source_input_triv hQ hQ.1 H k _
  simp_rw [hleaf]
  change (∑' _p : (Fin 0 × Fin 2) → Fin d → ℤ, (H (0,[]) k:ℂ)) = (H (0,[]) k:ℂ)
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_unique,one_nsmul]

end WaveTurbulence.RA1Leafwise
