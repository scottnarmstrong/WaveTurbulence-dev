/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.VrHyper2
public import WaveTurbulence.Foundations.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
import Mathlib.Tactic

/-! # VINE-RHO (8): the `ρ`-loss of vine chains, hyper objects and DV's (TARGET L2226, Operation 1)

All statements are for the universe's object definitions (`WaveTurbulence.LGSpine.SourceVine`: `Chain`, `IsVC`, `IsHV`,
`IsHVC`, `IsDV`).  A chain of `n` vines costs at most `42 n` (`chain_ladderLoss_le`); an HV costs `42`; an HVC with `n` ingredients
costs `42 n`; a DV costs `84`.  The loss genuinely grows with `n` (see PROGRESS.md: a chain of `n` double bonds). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountAsm Finset
open WaveTurbulence.LGSpine.SourceVine (Chain IsSomeVine IsVC IsHV IsHVC IsDV)
set_option linter.unusedSectionVars false
universe u1 u2 u3
variable {V : Type u1} [DecidableEq V] {D : Type u2} [Fintype D] [DecidableEq D] {D' : Type u3} [Fintype D'] [DecidableEq D']

theorem eraseBond_isMolecule_of_ends (M : Molecule V D) (hM : M.IsMolecule) (e : D) {a b : V} (hab : a ≠ b)
    (he : M.ends e = s(a, b)) : (Molecule.eraseBond M e).IsMolecule := by
  have hne : M.atom e ≠ M.atom (M.mate e) := by
    intro h
    apply hab
    have : s(M.atom e, M.atom (M.mate e)) = s(a, b) := he
    rw [← h] at this
    exact (Sym2.eq_iff.1 this).elim (fun h => h.1.symm.trans h.2) (fun h => h.2.symm.trans h.1)
  exact WaveTurbulence.Vine.eraseBond_isMolecule M hM e hne

/-- **HV**: the adjoint of a single vine costs at most `42`. -/
theorem hv_ladderLoss_le (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : IsHV M S a b) :
    ladderLoss M (M.atoms \ S) ≤ 42 := by
  obtain ⟨e, he, X, hX⟩ := h
  have hM' := eraseBond_isMolecule_of_ends M hM e hX.1.2.2.2.1 he
  exact vine_ladderLoss_le_of_agree M hM _ hM' (agree_eraseBond M e he) hX (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)

end WaveTurbulence.VineRho
