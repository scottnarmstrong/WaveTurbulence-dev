/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.ForestSinglePaths
public import WaveTurbulence.Foundations.XChain.SysDraft.Final
public import WaveTurbulence.Foundations.XChain.SignedSeries
/-! The product of signed single-tree prefactors is the literal top-forest coupling/sign factor. -/
public section
namespace WaveTurbulence.Induct
open Finset
open SysAPI

theorem zpowSign_ofReal (sig : ℤˣ) (r : ℝ) : zpowSign sig (r : ℂ) = (r : ℂ) := by
  simp only [zpowSign, Complex.conj_ofReal, ite_self]

theorem zpowSign_I_unit (sig a : ℤˣ) :
    zpowSign sig (Complex.I * (((a : ℤ) : ℂ))) = Complex.I * ((((sig * a : ℤˣ) : ℤ) : ℂ)) := by
  rcases Int.units_eq_one_or sig with rfl | rfl <;>
    simp [zpowSign, map_mul]

theorem prod_signed_treePrefactor_eq {w d : ℕ} (L γ δ : ℝ) (top : Fin w → TTree) (sig : Fin w → ℤˣ) :
    (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j))) =
      (coupling d L γ δ : ℂ) ^ (∑ j, (top j).order) *
        ∏ b : GBranch top, Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ) := by
  have hj (j : Fin w) : zpowSign (sig j) (treePrefactor L γ δ d (top j)) =
      (coupling d L γ δ : ℂ) ^ (top j).order *
        ∏ b : GBranch (single (top j)), Complex.I *
          (((nodeSign sig (singleBranchToForest top j b).toNode.1 : ℤˣ) : ℤ) : ℂ) := by
    unfold treePrefactor
    rw [zpowSign_mul, zpowSign_prod]
    have hreal : zpowSign (sig j) ((coupling d L γ δ : ℂ) ^ (top j).order) =
        (coupling d L γ δ : ℂ) ^ (top j).order := by
      rw [← Complex.ofReal_pow]
      exact zpowSign_ofReal _ _
    rw [hreal]
    apply congrArg (fun z : ℂ => (coupling d L γ δ : ℂ) ^ (top j).order * z)
    apply prod_congr rfl
    intro b _
    exact (zpowSign_I_unit (sig j) (treeSign (top j) b.toNode)).trans
      (congrArg (fun a : ℤˣ => Complex.I * (((a : ℤ) : ℂ))) (nodeSign_single_mul sig top j b.toNode))
  rw [prod_congr rfl (fun j _ => hj j), prod_mul_distrib, prod_pow_eq_pow_sum]
  apply congrArg (fun z : ℂ => (coupling d L γ δ : ℂ) ^ (∑ j, (top j).order) * z)
  have he := Fintype.prod_equiv (forestSingleBranchEquiv top)
    (fun b : GBranch top => Complex.I * (((nodeSign sig b.toNode.1 : ℤˣ) : ℤ) : ℂ))
    (fun z : Σ j : Fin w, GBranch (single (top j)) =>
      Complex.I * (((nodeSign sig (singleBranchToForest top z.1 z.2).toNode.1 : ℤˣ) : ℤ) : ℂ))
    (fun _ => rfl)
  exact (he.trans (Fintype.prod_sigma _)).symm

end WaveTurbulence.Induct
