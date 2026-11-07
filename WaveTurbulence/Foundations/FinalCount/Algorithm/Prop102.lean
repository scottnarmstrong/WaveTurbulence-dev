/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.ForestProp102
public import WaveTurbulence.Foundations.FinalCount.Algorithm.SGMain
import Mathlib.Tactic

/-! # DH23 Proposition 10.2 (`moleprop2`, Revision_Submit.tex L1834)

> If `M` is a molecule that contains no triple bond and `E = 2V-1`, then `Af ≲ L^(-3γ₀/5)`; if
> `M` contains no triple bond and `E = 2V-2 > 0`, then `Af ≲ L^(-η/3)`.  Furthermore, if the
> number of atoms in `M` not of degree `4` is `w`, and we also allow at most `w` atoms to be SG
> in the decoration, then we have `Af ≲ L^(-η²·ρ + C(w+1))`.

Reading of the statement.  `p.value γ δ C1` is `Af` of DH23 (`defequan`, L1829 setting:
decoration count `E`, circuit-rank normalisation `(C1⁻¹ δ^(1/2) L^(-(d-γ)))^χ`, link product
`Π`).  `Problem` is the actual decoration problem of a connected molecule with every atom
large gap at level `L^(-γ+η)` (L1829: "the decoration is LG at `v`"); `ProblemSG` allows at
most `wn` atoms off which the large-gap condition fails, the set depending on the decoration
(L1834).  `ρ = sourceRho` is the source ladder complexity (`ρ = q + m'` of L1829).

Hypotheses, each with its source:
* `3 ≤ d`, `γ ∈ (0,1)`: L438 (standing assumption `d ≥ 3`, `0 < γ < 1`).
* `η ≤ min γ (1-γ)` and `4·1440061·η ≤ 1`: L438 "fix `η` as a small absolute constant with
  `η ≪_{d,γ} 1`" (the numeral `1440061 = 60·24000+61` is the absolute combinatorial constant of
  the algorithm; it does not depend on `d`, `γ`).
* `δ ∈ (0,1]`, `C1 ≥ C₀`, `L ≥ L₀`: L438 (`δ ≪ 1`, constants `C⁺` large, `L` large).
* `c ≥ 1`, `m`: typing data (ladder gap constant of the problem; the exponent of the size bound).
* R34 (G8-QUANT): `C₀` depends only on `(d, γ, η, c)`; the size exponent `m` is quantified AFTER `C₀`
  (`∃ C₀, 1 ≤ C₀ ∧ ∀ m, ∀ δ, ∀ C1 ≥ C₀, ∃ L₀, …`) and enters only through `L₀`.
* `GraphOk`: `AppbNoTripleBonds` is "contains no triple bond" of L1834; the size bound
  `atoms.card ≤ (1+log L)^m` is a recorded DEVIATION (the statement has none; the proof's
  logarithmic losses `(log L)^(8 n)` need one, and it holds for all molecules the algorithm meets).
* connected, nonempty: L1829 ("we always consider a connected molecule").
* `E = 2V-1`, `E = 2V-2 > 0`, number of atoms of degree `≠ 4` at most `w`: premises of L1834
  (the source says "is `w`"; `≤ w` is the same statement for the same bound).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole.AppbAlgorithm
open scoped ENNReal
open Set
universe u v

/-- DH23 Proposition 10.2, all three bounds. -/
theorem dh23_prop_10_2 (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1-γ)) (hηs : 4*1440061*η ≤ 1) (c : ℝ) (hc : 1 ≤ c) :
    ∃ C₀ : ℝ,1 ≤ C₀ ∧ ∀ m : ℕ,∀ δ ∈ Ioc (0 : ℝ) 1,∀ C1 ≥ C₀,∃ L₀ : ℝ,
    ∀ (V : Type v) [DecidableEq V] (w : Mom d),∀ L ≥ L₀,
    -- bounds 1 and 2: no triple bond, `E = 2V-1` or `E = 2V-2 > 0`
    (∀ p : Problem.{u,v} V d L w c (L^(-γ+η)),GraphOk L m p.state →
      (∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b) →
      p.state.graph.atoms.Nonempty →
      (((p.state.graph.bonds.card : ℤ) = 2*(p.state.graph.atoms.card : ℤ)-1 →
          p.value γ δ C1 ≤ ENNReal.ofReal (L^(-3*min γ (1-γ)/5))) ∧
        ((p.state.graph.bonds.card : ℤ) = 2*(p.state.graph.atoms.card : ℤ)-2 →
          0 < p.state.graph.bonds.card →
          p.value γ δ C1 ≤ ENNReal.ofReal (L^(-η/3))))) ∧
    -- bound 3: `w` atoms of degree `≠ 4`, at most `w` SG atoms
    (∀ wn : ℕ,∀ p : ProblemSG.{u,v} V d L w c (L^(-γ+η)) wn,GraphOk L m p.state →
      (∀ a ∈ p.state.graph.atoms,∀ b ∈ p.state.graph.atoms,p.state.graph.SameComponent a b) →
      p.state.graph.atoms.Nonempty →
      (p.state.graph.atoms.filter (fun a => p.state.graph.deg a ≠ 4)).card ≤ wn →
      p.value γ δ C1 ≤ ENNReal.ofReal
        (L^(-η^2*(sourceRho p.state.graph : ℝ)+(16*(d : ℝ)+28)*((wn : ℝ)+1)))) := by
  obtain ⟨C₁,hC₁,h1⟩ := prop102_dense.{u,v} d hd γ η hγ hη hηγ c hc
  obtain ⟨C₂,hC₂,h2⟩ := prop102_rho_sg.{u,v} d hd γ η hγ hη hηγ hηs c hc
  refine ⟨max C₁ C₂,le_max_of_le_left hC₁,fun m δ hδ C1 hC1 => ?_⟩
  obtain ⟨L₁,hL₁⟩ := h1 m δ hδ C1 (le_trans (le_max_left _ _) hC1)
  obtain ⟨L₂,hL₂⟩ := h2 m δ hδ C1 (le_trans (le_max_right _ _) hC1)
  refine ⟨max L₁ L₂,fun V _ w L hL => ⟨?_,?_⟩⟩
  · exact fun p => hL₁ V w L (le_trans (le_max_left _ _) hL) p
  · exact fun wn p => hL₂ V w wn L (le_trans (le_max_right _ _) hL) p

end WaveTurbulence.Mole.AppbAlgorithm
