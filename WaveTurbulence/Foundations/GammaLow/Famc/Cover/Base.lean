/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.Molecule.MoleculeJointSymmetry
public import WaveTurbulence.Foundations.Molecule.MoleculeBondsBetween
public import WaveTurbulence.Foundations.Spine.SourceChainSwap
/-! # Base facts on the `𝒱_γ` family for the counting cover (packet L5c)

* The members of `𝒱_γ` do not depend on the order of their joints: `Molecule.IsTVine` is symmetric (the closure of
  D11 is symmetric in `j₁, j₂`), hence so are `IsVineEnl`, `IsVineGamma` and L6's `Src.IsSomeVine`.
* `canonicalSub_subset` over `Src` (main: `Spine/SourceCanonicalDef.lean`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.GammaLow.FinalCount.Src

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem sigma_comm (M : Molecule V D) (a b : V) : M.sigma a b = M.sigma b a :=
  Mole.bondsBetween_symm M a b

/-- The D11 closure is symmetric in the two joints. -/
theorem isClosure_swap {M : Molecule V D} {S : Finset V} {j₁ j₂ : V} {G : TVine.UMultigraph V}
    (h : M.IsClosure S j₁ j₂ G) : M.IsClosure S j₂ j₁ G := by
  obtain ⟨hσ, hv, hl, added, hadd, hm⟩ := h
  refine ⟨by rw [sigma_comm]; exact hσ, by rw [hv, Finset.erase_right_comm], hl, added, ?_, ?_⟩
  · rcases hadd with ⟨h0, a, b, c, d, ha, hc, he⟩ | ⟨h1, x, y, hx, hy, he⟩
    · exact Or.inl ⟨by rw [sigma_comm]; exact h0, c, d, a, b, hc, ha, by rw [he, Multiset.pair_comm]⟩
    · exact Or.inr ⟨by rw [sigma_comm]; exact h1, y, x, hy, hx, by rw [he, Sym2.eq_swap]⟩
  · intro e
    rw [hm e]
    congr 2
    exact Multiset.filter_congr (fun f _ => and_comm)

/-- **T-vines do not depend on the order of the joints.** -/
theorem isTVine_swap {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsTVine S a b) :
    M.IsTVine S b a := by
  obtain ⟨hB, h2, G, G', hcl, hr, hT⟩ := h
  exact ⟨Mole.block_swap_joints M hB, h2, G, G', isClosure_swap hcl, hr, hT⟩

theorem isVineEnl_swap {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsVineEnl S a b) :
    M.IsVineEnl S b a := by
  rcases h with h | h | h
  · exact Or.inl (LGSpine.SourceVine.isVine_swap h)
  · exact Or.inr (Or.inl (LGSpine.SourceVine.isVine_swap h))
  · exact Or.inr (Or.inr (isTVine_swap h))

theorem isVineGamma_swap {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsVineGamma γ S a b) :
    M.IsVineGamma γ S b a := by
  rcases h with ⟨hγ, h⟩ | ⟨hγ, X, h⟩
  · exact Or.inl ⟨hγ, isVineEnl_swap h⟩
  · exact Or.inr ⟨hγ, X, LGSpine.SourceVine.isVine_swap h⟩

/-- `Src.IsSomeVine` does not depend on the order of the joints (main: `SourceVine.isSomeVine_swap`). -/
theorem isSomeVine_swap {γ : ℝ} {M : Molecule V D} {S : Finset V} {a b : V} (h : IsSomeVine γ M S a b) :
    IsSomeVine γ M S b a :=
  isVineGamma_swap h

/-- Containment of source objects implies atom-set inclusion (main: `SourceVine.Object.contained_atoms_subset`). -/
theorem Object.contained_atoms_subset {γ : ℝ} {M : Molecule V D} (P Q : Object γ M) (h : P.IsContained Q) :
    P.atoms ⊆ Q.atoms := by
  rcases P with ⟨A, x, y, Psh⟩
  rcases Q with ⟨S, a, b, Qsh⟩
  cases Psh <;> cases Qsh
  · exact h
  · exact h
  · exact h
  · exact h.1

end WaveTurbulence.GammaLow.Famc
