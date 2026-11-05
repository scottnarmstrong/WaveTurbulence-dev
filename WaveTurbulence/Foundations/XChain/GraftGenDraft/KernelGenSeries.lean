/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.GraftGenDraft.KernelGenGraft

/-!
# GRAFTGEN: summability of the factored `kernelKgen` series

**Statement** (`summable_kernelKgen_graft_series`). Under the hypotheses of `kernelKgen_graft`, the top series
`kt ↦ topGenFactor(kt) · ∏_B kernelK(low B)(lower roots from kt)` is summable. This is the `kernelKgen`
analogue of INDUCT's `summable_graft_kernel_series`, and it allows the sum over the lower families to be
interchanged with this series.

**Proof.** As in `kernelKgen_graft`:
- the graft summand is `topGenFactor · ∏ lower summands` (`kernelGenFactor_graft`) and is summable
  (`summable_kernelGenFactor`);
- so its boundary regrouping is summable, hence summable on the `Σ`-fibres;
- the fibre sums factor (`tsum_independent_prod`, `kernelK_eq_tsum_factors`).
-/

@[expose] public section

namespace WaveTurbulence.GraftGen

open Finset MeasureTheory Induct
open scoped Classical

variable {d w : ℕ} (L γ δ : ℝ)

variable {sig : Fin w → ℤˣ} {top : Fin w → TTree} {P : Finpartition (univ : Finset (GLeaf top))}
  {low : (B : P.parts) → LayeredGarden B.1.card} {p : ℕ}
  {hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1}
  {hbound : ∀ B a, (low B).layer a ≤ p}

theorem summable_kernelKgen_graft_series (F : ℕ → Mom d → ℝ)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (fix : GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Option ℝ)
    (fixT : GBranch top → Option ℝ)
    (hfixT : ∀ b, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inl b)) = fixT b)
    (hfixL : ∀ z, fix (gardenBranchEquiv top P (fun B => (low B).garden) (.inr z)) = none)
    (hfixv : ∀ b v, fixT b = some v → (p : ℝ) ≤ v)
    (off : Finset (GBranch (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree))
    (offT : Finset (GBranch top))
    (hoffT : ∀ b, gardenBranchEquiv top P (fun B => (low B).garden) (.inl b) ∈ off ↔ b ∈ offT)
    (hoffL : ∀ z, gardenBranchEquiv top P (fun B => (low B).garden) (.inr z) ∉ off)
    (wtop : (GNode top → Mom d) → ℝ) (hwtop : ∀ k, |wtop k| ≤ 1)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    Summable fun kt : ForestDecoration top d n =>
      topGenFactor L γ δ sig top fixT offT wtop kt.1 k₀ p t *
        ∏ B : P.parts, kernelK L γ δ F (low B) (fun _ => p) s k₀
          (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl := by
  set wt := fun k : GNode (markedLayeredGardenGraft sig top P low p hsig hbound).garden.tree → Mom d =>
    wtop (fun a => k (topNodeEmbedding top P (fun B => (low B).garden) a))
  set E := fun kt : ForestDecoration top d n => topGenFactor L γ δ sig top fixT offT wtop kt.1 k₀ p t
  set g := fun (kt : ForestDecoration top d n) (B : P.parts)
    (kl : GenDecoration (low B).garden d (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl) =>
      kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀ kl
  have hfac : ∀ x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl,
      kernelGenFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off wt (fun _ => t) k₀
        (assembleGenDecoration sig top P (fun B => (low B).garden) hsig n nfl x) =
        E x.1 * ∏ B, g x.1 B (x.2 B) := by
    intro x
    rw [kernelGenFactor_graft L γ δ F hbranch hn hf fix fixT hfixT hfixL hfixv off offT hoffT hoffL wtop t s
      hpt k₀ n nfl, split_assembleGenDecoration]
  have hsum := summable_kernelGenFactor L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) fix off
    wt (fun k => hwtop _) (fun _ => t) k₀ n nfl (markedLayeredGardenGraft_no_lone sig top P low p hsig hbound hn)
    hF
  have hs : Summable (fun x : BoundaryDecorationData top P (fun B => (low B).garden) d n nfl =>
      E x.1 * ∏ B, g x.1 B (x.2 B)) :=
    ((summable_assembleGenDecoration_iff sig top P (fun B => (low B).garden) hsig n nfl _).mpr hsum).congr hfac
  have hg := hs.sigma.mul_left (∏ B : P.parts, (coupling d L γ δ : ℂ) ^ (low B).garden.order * (low B).garden.zeta)
  apply hg.congr
  intro kt
  simp only [E, g, tsum_mul_left, tsum_independent_prod, kernelK_eq_tsum_factors, prod_mul_distrib]
  ring

end WaveTurbulence.GraftGen
