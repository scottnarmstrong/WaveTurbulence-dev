/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm14a
public import WaveTurbulence.Foundations.FinalCount.AsmTerm12
public import WaveTurbulence.Foundations.FinalCount.AsmTerm3
public import WaveTurbulence.Foundations.FinalCount.AsmProp96b
/-! **FINALCOUNT-ASSEMBLY, `hterm` part 14b: the per-component exponent `exa` and its sum.** -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The classes of a state, in G8's type. -/
noncomputable def cl8 (hf : HSt V D₀) : V → WaveTurbulence.FinalCountG8.Cls := fun a => g8Cls (toCls (hf.s.cls a))

/-- The component of `a` is tame-free and (even, or the odd component with `R = 1`): handled by `prop96`. -/
def UntC (hf : HSt V D₀) (Tm : V → Prop) (R : ℕ) (a : V) : Prop := TameFree hf Tm a ∧ (CompOdd hf a → R = 1)

/-- The exponent of the component bound for the component of `a` in the Operation-5 molecule. -/
noncomputable def exa (γ η : ℝ) (hf : HSt V D₀) (Tm : V → Prop) (R : ℕ) (a : V) : ℝ :=
  (gam0 γ + 2 * η ^ 2) *
      ((WaveTurbulence.FinalCountG8.betaAtoms (compMol (hf.op5 Tm).s.M a).atoms (cl8 hf)).card : ℝ)
    - (if UntC hf Tm R a ∧ ¬ CompOdd hf a then eraseA γ η else 0)
    - η ^ 5 * ((compMol (hf.op5 Tm).s.M a).rho : ℝ)
    + (if UntC hf Tm R a then 0 else
        η * (WaveTurbulence.FinalCountG8.epsDefect (compMol (hf.op5 Tm).s.M a) (cl8 hf) : ℝ))

/-- The `β`-atoms add up over components. -/
theorem sum_beta_comp {N : Molecule V D₀} {Rs : Finset V} (hR : CompRep N Rs) (cl : V → WaveTurbulence.FinalCountG8.Cls) :
    ∑ a ∈ Rs, (WaveTurbulence.FinalCountG8.betaAtoms (compMol N a).atoms cl).card =
      (WaveTurbulence.FinalCountG8.betaAtoms N.atoms cl).card := by
  unfold WaveTurbulence.FinalCountG8.betaAtoms
  simp only [Finset.card_filter, compMol_atoms_eq]
  exact (hR.sum_atoms (fun v => if (cl v).IsBeta then 1 else 0)).symm

theorem betaAtoms_le_vBeta {hf : HSt V D₀} {Tm : V → Prop} (hC : Clean hf.s) :
    (WaveTurbulence.FinalCountG8.betaAtoms (hf.op5 Tm).s.M.atoms (cl8 hf)).card ≤ vBeta hf.s := by
  unfold WaveTurbulence.FinalCountG8.betaAtoms vBeta
  refine Finset.card_le_card fun v hv => ?_
  obtain ⟨hv1, hv2⟩ := Finset.mem_filter.1 hv
  refine Finset.mem_filter.2 ⟨(Op5.atoms_sub hv1).1, ?_⟩
  have h := (g8Cls_isBeta (c := toCls (hf.s.cls v))).1 hv2
  rcases toCls_isBeta.1 h with h | h
  · exact h
  · exact absurd h (hC v (Op5.atoms_sub hv1).1)

end WaveTurbulence.FinalCountAsm
