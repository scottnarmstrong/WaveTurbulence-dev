/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.CLLinearSumintDatum

/-! # Exact algebraic hypotheses of the frozen signed sumint consumer -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract TTree RegRed
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- The algebraic clauses of frozen Admissible, kept visibly separate
from the later analytic weight and bad-case extraction clauses. -/
def SumintAlgebraicHypotheses (D : SumintDatum d) (A : ℝ) : Prop :=
  (∀ v, (∀ p, IsUnitCoeff (D.σk v p)) ∧ (∀ c, IsUnitCoeff (D.σe v c)) ∧
    ((Finset.univ.filter fun p => D.σk v p ≠ 0).card+
      (Finset.univ.filter fun c => D.σe v c ≠ 0).card ≤ D.Λ v) ∧
    (∀ u, D.prev v = some u → D.S.LexLt u v) ∧
    (∀ j, D.T₂ v j-(D.prev v).elim 0 (fun u => D.T₂ u j) = ∑ p, D.σk v p*D.T₁ p j) ∧
    ∀ c, D.H₂ v c-(D.prev v).elim 0 (fun u => D.H₂ u c) = (∑ p, D.σk v p*D.H₁ p c)+D.σe v c) ∧
  (∀ v, 1 ≤ D.Λ v) ∧ ((∏ v, (D.Λ v : ℝ)) ≤ A^D.S.M) ∧
  (∀ v, ∃ p q : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4,
    (∀ j, sumintFormRowT D.T₁ D.T₂ p j-sumintFormRowT D.T₁ D.T₂ q j = if j = v then 1 else 0) ∧
    ∀ c, sumintFormRowH D.H₁ D.H₂ p c-sumintFormRowH D.H₁ D.H₂ q c = 0) ∧
  (∀ i j c, IsUnitCoeff (D.ζc i j c)) ∧ ∀ i c, IsUnitCoeff (D.ξc i c)

private theorem coeff_neg {a : ℤ} (h : IsUnitCoeff a) : IsUnitCoeff (-a) := by
  rcases h with h | h | h <;> norm_num [h,IsUnitCoeff]

theorem assemblyZeta_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n)
    (i : Fin n) (j : Fin ((assemblyChartAt hM9 B i).indexing.shape.m)) (c : Fin 3) :
    IsUnitCoeff (assemblyZeta hM9 B i j c) := by
  unfold assemblyZeta
  split
  · exact (assemblyChartAt hM9 B i).ζ_unit j c
  · exact coeff_neg ((assemblyChartAt hM9 B i).ζ_unit j c)

theorem assemblyXi_unit (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (i : Fin n) (c : Fin 4) :
    IsUnitCoeff (assemblyXi hM9 B i c) := by
  unfold assemblyXi
  split
  · exact (assemblyChartAt hM9 B i).ξ_unit c
  · exact coeff_neg ((assemblyChartAt hM9 B i).ξ_unit c)

/-- The exact frozen datum satisfies every algebraic clause without any
hypothesis about a proposed reparametrization or a desired conclusion. -/
theorem sourceSumintDatum_algebraic_hypotheses (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (W : SumintWeightClockData (assemblyShape hM9 B) d) :
    SumintAlgebraicHypotheses (sourceSumintDatum hM9 B hG W) 6561 := by
  have hp := normalized_predecessor_system hM9 B hG
  exact ⟨hp.1,hp.2.1,hp.2.2,normalized_affine_difference_system hM9 B hG,
    assemblyZeta_unit hM9 B,assemblyXi_unit hM9 B⟩

noncomputable def assemblyCoreFirstSign (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (i : Fin n) : ℤˣ :=
  (assemblyChartAt hM9 B i).coreFirstSign

noncomputable def assemblyCoreSign (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (i : Fin n) : ℤˣ :=
  (assemblyChartAt hM9 B i).coreSign

end WaveTurbulence.VineEstS2
