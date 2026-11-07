/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RowMatch

/-! # P4-W2 (b2): the row product with exceptional pair and branch rows

`hrow_of_rowwise_exc`: the generalisation of `hrow_of_rowwise` in which the pair rows `Vp` and the branch rows `Vb` of the exceptional records (whose pair row and branch row need not coincide)
are matched jointly (`hX`), every other row row by row. -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng
variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

/-- **`hrow_of_rowwise` with exceptional rows**: the pair rows `Vp` and the branch rows `Vb` are matched jointly (`hX`), every other row row by row. -/
theorem hrow_of_rowwise_exc (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)
    (qf : SourcePair G → ℂ) (tf : GBranch G.tree → ℂ)
    (Wv : (assemblyShape hM9 B).VIdx ⊕ (assemblyShape hM9 B).VIdx → ℂ) (cK cL : (assemblyShape hM9 B).VIdx → ℂ)
    (Vp Vb : Finset (assemblyShape hM9 B).VIdx) (C : ℂ)
    (hK : ∀ v ∉ Vp, qf (assemblyPairOf hM9 B hG v).1 = cK v * Wv (Sum.inl v))
    (hT : ∀ v ∉ Vb, tf (assemblyBranchOf hM9 B v).1 = cL v * Wv (Sum.inr v))
    (hX : (∏ v ∈ Vp, qf (assemblyPairOf hM9 B hG v).1) * (∏ v ∈ Vb, tf (assemblyBranchOf hM9 B v).1) =
      C * (∏ v ∈ Vp, Wv (Sum.inl v)) * ∏ v ∈ Vb, Wv (Sum.inr v)) :
    (∏ p ∈ clRegionalPairs hG U, qf p) * (∏ v ∈ U.erase a, tf v) =
      (C * ((∏ v ∈ Vpᶜ, cK v) * ∏ v ∈ Vbᶜ, cL v)) * ∏ ρ, Wv ρ := by
  classical
  rw [prod_pairs_rows hM9 B hG, prod_interior_rows hM9 B, Fintype.prod_sum_type]
  rw [← Finset.prod_mul_prod_compl Vp (fun v => qf (assemblyPairOf hM9 B hG v).1),
    ← Finset.prod_mul_prod_compl Vb (fun v => tf (assemblyBranchOf hM9 B v).1),
    ← Finset.prod_mul_prod_compl Vp (fun v => Wv (Sum.inl v)),
    ← Finset.prod_mul_prod_compl Vb (fun v => Wv (Sum.inr v))]
  have h1 : ∏ v ∈ Vpᶜ, qf (assemblyPairOf hM9 B hG v).1 = (∏ v ∈ Vpᶜ, cK v) * ∏ v ∈ Vpᶜ, Wv (Sum.inl v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v hv => hK v (Finset.mem_compl.mp hv)
  have h2 : ∏ v ∈ Vbᶜ, tf (assemblyBranchOf hM9 B v).1 = (∏ v ∈ Vbᶜ, cL v) * ∏ v ∈ Vbᶜ, Wv (Sum.inr v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v hv => hT v (Finset.mem_compl.mp hv)
  rw [h1, h2]
  calc _ = ((∏ v ∈ Vp, qf (assemblyPairOf hM9 B hG v).1) * (∏ v ∈ Vb, tf (assemblyBranchOf hM9 B v).1)) *
        ((∏ v ∈ Vpᶜ, cK v) * ∏ v ∈ Vpᶜ, Wv (Sum.inl v)) * ((∏ v ∈ Vbᶜ, cL v) * ∏ v ∈ Vbᶜ, Wv (Sum.inr v)) := by ring
    _ = _ := by rw [hX]; ring

end WaveTurbulence.VineEstS5C.P4.W2
