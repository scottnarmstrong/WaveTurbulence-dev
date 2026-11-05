/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.TopPartitionErrorConvergence
public import WaveTurbulence.Foundations.XChain.GraftExpansionFinite
/-! The concrete T.cmattr error and its independent top-tree kernel expansion. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset MeasureTheory
open SysAPI
open scoped Classical

noncomputable def treeKernelExpansion {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
    (sig : Fin w → ℤˣ) (p Ntop Natt : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑ top : Fin w → TrTree Ntop,
    (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j).1)) *
    ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
        TopPartitionIrreducible (fun j => (top j).1) P},
      ∑' κ : ForestDecoration (fun j => (top j).1) d n,
        topPartitionKernelIntegrand L γ δ F sig (fun j => (top j).1) P.1 p Natt t n κ

noncomputable def cmattrError {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (sig : Fin w → ℤˣ)
    (c : Ω → (Fin d → ℤ) → ℂ) (p Ntop Natt : ℕ) (t : ℝ) (n : Fin w → (Fin d → ℤ)) : ℂ :=
  ∑ top : Fin w → TrTree Ntop,
    (∏ j, zpowSign (sig j) (treePrefactor L γ δ d (top j).1)) *
    ∑ P : {P : Finpartition (univ : Finset (GLeaf (fun j => (top j).1))) //
        TopPartitionIrreducible (fun j => (top j).1) P},
      topPartitionError μ L γ δ F sig (fun j => (top j).1) P.1 c p Natt t n

end WaveTurbulence.Induct
