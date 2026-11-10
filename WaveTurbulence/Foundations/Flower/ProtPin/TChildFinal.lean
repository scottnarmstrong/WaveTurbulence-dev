/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildWrap
public import WaveTurbulence.Foundations.Flower.ProtPin.FinalTwo

/-! # D3 PROT-PIN (P7): `termChild` for protected paired trees in `X^{θ,30d,0}`, given the root-trace bound

`tc_termChild_final_of`: the configuration `termChild i` of `ProtBoundAt` for trees at the weight `θ = η`
(`PieceLoss P θ 0`, `c ≥ 31d + 6`), from the uniform root-trace bound `TcTraceU θ Ct` of side couples.
`ProtCfg.Valid (termChild i)` puts a branch of layer `p` at the child `i ≠ lone` of the terminal node, i.e. at the
bottom tree of the red (`i = m.red.2`) or the green (`i = m.green.2`) side couple; the per-output bounds
`tc_perk_red`/`tc_perk_green` and `final_two` (two cuts, `a = 1`) conclude. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem tc_rBase_bot (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    ∃ j, rBase m inner ζ j = bPath m inner ++ [m.red.2] := by
  by_cases hs : slotSign ζ m.red.1 = 1
  · exact ⟨1, by simp [rBase, hs]⟩
  · exact ⟨0, by simp [rBase, hs]⟩

theorem tc_gBase_bot (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    ∃ j, gBase m inner ζ j = bPath m inner ++ [m.green.2] := by
  by_cases hs : slotSign ζ m.green.1 = 1
  · exact ⟨1, by simp [gBase, hs]⟩
  · exact ⟨0, by simp [gBase, hs]⟩

theorem tc_gBase_ne (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) :
    gBase m inner ζ j ≠ bPath m inner ++ [m.red.2] := by
  rcases gBase_cases m inner ζ j with h | h <;> rw [h] <;> intro h'
  · have := congrArg List.length h'
    simp [bPath] at this
  · have h2 := List.append_cancel_left h'
    simp only [List.cons.injEq, and_true] at h2
    exact red2_ne_green2 m h2.symm

theorem tc_rBase_ne (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) :
    rBase m inner ζ j ≠ bPath m inner ++ [m.green.2] := by
  rcases rBase_cases m inner ζ j with h | h <;> rw [h] <;> intro h'
  · have := congrArg List.length h'
    simp [bPath] at this
  · have h2 := List.append_cancel_left h'
    simp only [List.cons.injEq, and_true] at h2
    exact red2_ne_green2 m h2

end WaveTurbulence.Flower.ProtPin
