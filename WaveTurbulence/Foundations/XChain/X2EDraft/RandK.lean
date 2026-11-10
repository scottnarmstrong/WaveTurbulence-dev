/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerFamily
public import WaveTurbulence.Foundations.XChain.FlowerDraft.X2Est

/-!
# X2E-1: the `2P`-th moments of the random kernel `𝒦` of `flowerest1`

**Statement** (`integral_norm_randK_pow_eq`). Under `AnsatzAt` at step `p`, for every kind, pattern, `†`, cutoffs,
`ζ`, `p ≤ s, t ≤ p + 1` and `n, n'`, and `P ≥ 1` with `2P(2(3N_{p+1}+1)+1) ≤ 2R_p`:
`𝔼_p |𝒦^ζ_{nn'}(t, s)|^{2P} = ∑_{(F_j) ∈ 𝒯^{2P}} ∑_Q (∑'_κ flowerKer + flowerError)`.
- `𝒯 = kernelTrees` are the flower trees of `𝒦` (kind, flower sign `ζ`, valid pattern); every one has order
  `≤ 3N_{p+1} + 1` (`order_le_of_mem_kindTrees`).
- `Q` runs over the partitions of the non-flower leaves of `(F_j)`; `κ` over the decorations with roots `n` and
  flowers `n'`; the signs alternate (`altSig P`).
- `flowerKer` has the lower kernel sums `K(𝒢_p)` at the blocks of `Q` (X2E-2/3 identify these with the
  gardens of `flowerSumP`), and `flowerError` collects the `E_p, Ẽ_p` terms (bounded in X2E-4).

Also `integrable_norm_randK_pow`: `|𝒦|^{2P}` is integrable on `F_p` (the first half of O-X2-EXP).
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.X2E

open Finset MeasureTheory Filter Topology Induct SysAPI Cpl
open scoped ENNReal Classical

theorem order_toTree : ∀ F : FTree, F.toTree.order = F.order
  | .flower => rfl
  | .node i F T₁ T₂ => by
    have ih := order_toTree F
    simp only [FTree.toTree, FTree.order]
    split_ifs <;> simp only [TTree.order, ih] <;> omega

theorem order_le_of_mem_kindTrees {N : ℕ} {kind : FlowerKind} {F : FTree} (h : F ∈ kindTrees N kind) :
    F.order ≤ 3 * N + 1 := by
  cases kind with
  | X =>
    have h' := (mem_filter.mp h).1
    have := mem_ftreesLE.mp h'
    omega
  | Y =>
    obtain ⟨x, hx, rfl⟩ := mem_image.mp h
    have hx' := (mem_filter.mp hx).1
    simp only [Rind, mem_product, mem_univ, true_and, mem_ftreesLE, mem_treesLE] at hx'
    simp only [rootOf, FTree.order]
    omega
  | W =>
    obtain ⟨x, hx, rfl⟩ := mem_image.mp h
    have hx' := (mem_filter.mp hx).1
    simp only [Wind', mem_product, mem_univ, true_and, mem_ftreesLE, mem_treesLE] at hx'
    rw [order_bottomOf]
    omega

theorem order_toTree_le_of_mem_kernelTrees {pat : FixPat} {N : ℕ} {kind : FlowerKind} {ζ : ℤˣ} {F : FTree}
    (h : F ∈ kernelTrees pat N kind ζ) : F.toTree.order ≤ 3 * N + 1 := by
  rw [order_toTree]
  exact order_le_of_mem_kindTrees (mem_filter.mp h).1

section RandK

variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2) (hc : |coupling P.d P.L P.γ P.δ| ≤ 1)
    (kind : FlowerKind) (pat : FixPat) (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ)
    (t s : ℝ) (n n' : Fin P.d → ℤ) (Pm : ℕ) (hPm : 1 ≤ Pm)
    (hNR : (Pm + Pm) * (2 * (3 * P.N (p + 1) + 1) + 1) ≤ 2 * P.R p)

omit [MeasurableSpace Ω] in
theorem randK_eq_famFlowerTerm (ω : Ω) :
    randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω =
      famFlowerTerm (kernelTrees pat (P.N (p + 1)) kind ζ) (fkCoef P.L P.γ P.δ p pat dagger cut1 cut2 t s)
        (a ω p) n n' :=
  randFlowerKernel_eq_famFlowerTerm P.L P.γ P.δ p pat dagger cut1 cut2 t s (P.N (p + 1)) (a ω p) kind ζ n n'

include hG ha hrapid hL hδ hsmall hC hF hΛ hc hPm hNR in
/-- **`|𝒦|^{2P}` is integrable on `F_p`.** -/
theorem integrable_norm_randK_pow :
    Integrable (fun ω => ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm)) (μ.restrict (Fev p)) := by
  simp only [randK_eq_famFlowerTerm]
  exact integrable_norm_famFlowerTerm_pow P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
    (kernelTrees pat (P.N (p + 1)) kind ζ) (fun F hF => ne_flower_of_mem_kernelTrees pat hF) (3 * P.N (p + 1) + 1)
    (fun F hF => order_toTree_le_of_mem_kernelTrees hF) (fkCoef P.L P.γ P.δ p pat dagger cut1 cut2 t s)
    (norm_fkCoef_le P.L P.γ P.δ p pat dagger cut1 cut2 t s hc) Pm hPm hNR n n'

end RandK

end WaveTurbulence.X2E
