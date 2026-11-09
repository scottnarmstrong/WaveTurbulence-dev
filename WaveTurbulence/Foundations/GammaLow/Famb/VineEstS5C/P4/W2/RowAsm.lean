/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowMatch
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowAsm
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RowMatch
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowAsm` (sha256 3b67d2416b26c02c…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (b2): the row product with exceptional pair and branch rows

`hrow_of_rowwise_exc`: the generalisation of `hrow_of_rowwise` in which the pair rows `Vp` and the branch rows `Vb` of the exceptional records (whose pair row and branch row need not coincide)
are matched jointly (`hX`), every other row row by row. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **`hrow_of_rowwise` with exceptional rows**: the pair rows `Vp` and the branch rows `Vb` are matched jointly (`hX`), every other row row by row. -/
theorem hrow_of_rowwise_excΓ (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)
    (qf : SourcePair G → ℂ) (tf : GBranch G.tree → ℂ)
    (Wv : (assemblyShapeΓ hM9 B).VIdx ⊕ (assemblyShapeΓ hM9 B).VIdx → ℂ) (cK cL : (assemblyShapeΓ hM9 B).VIdx → ℂ)
    (Vp Vb : Finset (assemblyShapeΓ hM9 B).VIdx) (C : ℂ)
    (hK : ∀ v ∉ Vp, qf (assemblyPairOfΓ hM9 B hG v).1 = cK v * Wv (Sum.inl v))
    (hT : ∀ v ∉ Vb, tf (assemblyBranchOfΓ hM9 B v).1 = cL v * Wv (Sum.inr v))
    (hX : (∏ v ∈ Vp, qf (assemblyPairOfΓ hM9 B hG v).1) * (∏ v ∈ Vb, tf (assemblyBranchOfΓ hM9 B v).1) =
      C * (∏ v ∈ Vp, Wv (Sum.inl v)) * ∏ v ∈ Vb, Wv (Sum.inr v)) :
    (∏ p ∈ clRegionalPairs hG U, qf p) * (∏ v ∈ U.erase a, tf v) =
      (C * ((∏ v ∈ Vpᶜ, cK v) * ∏ v ∈ Vbᶜ, cL v)) * ∏ ρ, Wv ρ := by
  classical
  rw [prod_pairs_rowsΓ hM9 B hG, prod_interior_rowsΓ hM9 B, Fintype.prod_sum_type]
  rw [← Finset.prod_mul_prod_compl Vp (fun v => qf (assemblyPairOfΓ hM9 B hG v).1),
    ← Finset.prod_mul_prod_compl Vb (fun v => tf (assemblyBranchOfΓ hM9 B v).1),
    ← Finset.prod_mul_prod_compl Vp (fun v => Wv (Sum.inl v)),
    ← Finset.prod_mul_prod_compl Vb (fun v => Wv (Sum.inr v))]
  have h1 : ∏ v ∈ Vpᶜ, qf (assemblyPairOfΓ hM9 B hG v).1 = (∏ v ∈ Vpᶜ, cK v) * ∏ v ∈ Vpᶜ, Wv (Sum.inl v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v hv => hK v (Finset.mem_compl.mp hv)
  have h2 : ∏ v ∈ Vbᶜ, tf (assemblyBranchOfΓ hM9 B v).1 = (∏ v ∈ Vbᶜ, cL v) * ∏ v ∈ Vbᶜ, Wv (Sum.inr v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v hv => hT v (Finset.mem_compl.mp hv)
  rw [h1, h2]
  calc _ = ((∏ v ∈ Vp, qf (assemblyPairOfΓ hM9 B hG v).1) * (∏ v ∈ Vb, tf (assemblyBranchOfΓ hM9 B v).1)) *
        ((∏ v ∈ Vpᶜ, cK v) * ∏ v ∈ Vpᶜ, Wv (Sum.inl v)) * ((∏ v ∈ Vbᶜ, cL v) * ∏ v ∈ Vbᶜ, Wv (Sum.inr v)) := by ring
    _ = _ := by rw [hX]; ring

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
