/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftKernelRegrouping
public import WaveTurbulence.Foundations.XChain.GraftKernelPrefactor
/-! Full kernel graft identity with the lower decoration sums folded into their actual kernels. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem kernelK_graft {d w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → LayeredGarden B.1.card) (p : ℕ)
    (hsig : ∀ B k, (low B).garden.sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1)
    (hbound : ∀ B a, (low B).layer a ≤ p)
    (hbranch : ∀ B (b : GBranch (low B).garden.tree), (low B).layer b.toNode < p)
    (hn : ∀ B ℓ, (low B).garden.mark ℓ ≠ some MarkTag.lower)
    (hf : ∀ B b, ¬ (low B).garden.IsFlowerParent b)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (htp : t ≤ (p : ℝ) + 1)
    (k₀ : Mom d) (n : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hF : ∀ q, Summable fun m : Fin d → ℤ => |F q (k₀ + latticePoint L m)|) :
    kernelK L γ δ F (markedLayeredGardenGraft sig top P low p hsig hbound) (fun _ => t) s k₀ n nfl =
    ((coupling d L γ δ : ℂ) ^ (∑ j, (top j).order) *
      ∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
    ∑' kt : ForestDecoration top d n,
      topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig kt.1 k₀ p t s *
      ∏ B : P.parts, kernelK L γ δ F (low B) (fun _ => p) s k₀
        (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl := by
  let c : ℂ := coupling d L γ δ
  let A := c ^ (∑ j, (top j).order) *
    ∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)
  let C := fun B : P.parts => c ^ (low B).garden.order * (low B).garden.zeta
  let E := fun kt : ForestDecoration top d n =>
    topDecorationFactor L γ δ sig top P (fun B => (low B).garden) hsig kt.1 k₀ p t s
  let g := fun (kt : ForestDecoration top d n) (B : P.parts) =>
    ∑' kl : GenDecoration (low B).garden d
      (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl,
      kernelDecorationFactor L γ δ F (low B) (fun _ => p) s k₀ kl
  have ht := kernelK_graft_eq_tsum_top_factors L γ δ F sig top P low p hsig hbound hbranch hn hf
    t s hpt htp k₀ n nfl hF
  have hp := markedGardenGraft_prefactor c sig top P (fun B => (low B).garden) hsig
  have h₁ := congrArg (fun z : ℂ => z * ∑' kt, E kt * ∏ B, g kt B) hp
  have h₂ := prefactor_mul_tsum_prod A C E g
  have h₃ : (∑' kt, E kt * ∏ B, C B * g kt B) =
      ∑' kt : ForestDecoration top d n, E kt * ∏ B : P.parts,
        kernelK L γ δ F (low B) (fun _ => p) s k₀
          (fun k => kt.1 ((blockRootEquiv top P).symm ⟨B, k⟩).toNode) nfl := by
    apply tsum_congr
    intro kt
    apply congrArg (fun z : ℂ => E kt * z)
    exact Finset.prod_congr rfl (fun B _ => rfl)
  exact ht.trans (h₁.trans (h₂.trans (congrArg (fun z : ℂ => A * z) h₃)))

end WaveTurbulence.Induct
