/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.TableRealization
import Mathlib.Tactic

/-! # Distinct unordered table endpoints force distinct actual bonds -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem table_edges_injective_of_simple (M : Molecule V D) (P : AppbPattern)
    (f : ℕ → V) (hf : Set.InjOn f (P.vertices : Set ℕ))
    (hs : Function.Injective fun i : Fin P.edges.length => s(P.edges[i].1,P.edges[i].2))
    (edge : Fin P.edges.length → D)
    (hend : ∀ i,M.ends (edge i) = s(f P.edges[i].1,f P.edges[i].2)) :
    Function.Injective edge := by
  intro i j hij
  apply hs
  have hh := (hend i).symm.trans ((congrArg M.ends hij).trans (hend j))
  rcases Sym2.eq_iff.mp hh with h | h
  · apply Sym2.eq_iff.mpr
    exact Or.inl ⟨hf (P.edge_fst_mem i) (P.edge_fst_mem j) h.1,
      hf (P.edge_snd_mem i) (P.edge_snd_mem j) h.2⟩
  · apply Sym2.eq_iff.mpr
    exact Or.inr ⟨hf (P.edge_fst_mem i) (P.edge_snd_mem j) h.1,
      hf (P.edge_snd_mem i) (P.edge_fst_mem j) h.2⟩

end WaveTurbulence.Mole.AppbAlgorithm
