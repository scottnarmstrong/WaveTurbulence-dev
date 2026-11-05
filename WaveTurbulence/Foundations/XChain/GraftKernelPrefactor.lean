/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftKernelWeights
public import WaveTurbulence.Foundations.XChain.GraftSigns
/-! Coupling and zeta prefactors split across the top forest and all lower components. -/
public section
namespace WaveTurbulence.Induct
open Finset

theorem pow_sum_mul_prod {β : Type*} [Fintype β] (c : ℂ) (n : ℕ)
    (m : β → ℕ) (z : ℂ) (v : β → ℂ) :
    c ^ (n + ∑ B, m B) * (z * ∏ B, v B) =
      (c ^ n * z) * ∏ B, c ^ m B * v B := by
  rw [pow_add, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

theorem markedGardenGraft_prefactor {w : ℕ} (c : ℂ) (sig : Fin w → ℤˣ) (top : Fin w → TTree)
    (P : Finpartition (univ : Finset (GLeaf top))) (low : (B : P.parts) → Garden B.1.card)
    (hsig : ∀ B k, (low B).sig k = nodeSign sig ((blockRootEquiv top P).symm ⟨B, k⟩).1) :
    c ^ (markedGardenGraft sig top P low hsig).order * (markedGardenGraft sig top P low hsig).zeta =
      (c ^ (∑ j, (top j).order) *
        ∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ)) *
      ∏ B : P.parts, c ^ (low B).order * (low B).zeta := by
  have he := congrArg₂ (fun (n : ℕ) (z : ℂ) => c ^ n * z)
    (markedGardenGraft_order sig top P low hsig) (markedGardenGraft_zeta sig top P low hsig)
  exact he.trans (pow_sum_mul_prod c (∑ j, (top j).order) (fun B => (low B).order)
    (∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ))
    (fun B => (low B).zeta))

theorem prefactor_mul_tsum_prod {α β : Type*} [Fintype β] (a : ℂ) (c : β → ℂ)
    (f : α → ℂ) (g : α → β → ℂ) :
    (a * ∏ B, c B) * (∑' x, f x * ∏ B, g x B) =
      a * ∑' x, f x * ∏ B, c B * g x B := by
  rw [mul_assoc, ← tsum_mul_left]
  apply congrArg (fun z : ℂ => a * z)
  apply tsum_congr
  intro x
  rw [Finset.prod_mul_distrib]
  ring

end WaveTurbulence.Induct
