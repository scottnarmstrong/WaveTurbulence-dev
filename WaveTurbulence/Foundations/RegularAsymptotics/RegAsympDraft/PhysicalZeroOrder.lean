/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceGardenSign
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceZeroMomentum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.ActualTimeExpansion

/-! # The original physical couple kernel at order zero -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Links Incoh MainCoef ClassJR Set

/-- The original trivial physical couple has precisely its single input
and no phase, coupling, Wick or lattice factor. -/
theorem KQstar_triv {d : ℕ} (L γ δ : ℝ) (F : Mom d → ℝ)
    (LG : LayeredGarden 2) (h0 : ∀ a, LG.layer a = 0)
    (hQ : RegCpl.triv.Decodes LG.garden) {t s : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) (k : Mom d) :
    KQstar L γ δ (fun _ => F) LG t s k = (F k:ℂ) := by
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
  rw [KQstar_latticeArray L γ δ F LG hQ t s k,horder,pow_zero,hz,one_mul,one_mul]
  simp_rw [hcoeff,one_mul]
  have hleaf (p : (Fin RegCpl.triv.links.length × Fin 2) → Fin d → ℤ) :
      (coupleMomentumData hQ hQ.1).sourceLeafWeight (fun _ k => (F k:ℂ)) k
        (fun i j => latticePoint L (p (i,j))) = (F k:ℂ) :=
    source_input_triv hQ hQ.1 (fun k => (F k:ℂ)) k _
  simp_rw [hleaf]
  change (∑' _p : (Fin 0 × Fin 2) → Fin d → ℤ, (F k:ℂ)) = (F k:ℂ)
  rw [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_unique,one_nsmul]

end WaveTurbulence.RegAsymp
