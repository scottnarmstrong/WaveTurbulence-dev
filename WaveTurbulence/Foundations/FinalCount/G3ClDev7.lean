/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev6
public import WaveTurbulence.Foundations.FinalCount.G3ClConn
/-! **FINALCOUNT-G3 (R29 item 4): `erase_cluster_deviation`.**  For a connected tame cluster `K` (all darts at atoms of `K` carry one label),
`m = |K|`, `e = e_K`, `j = e + ib - m + 1 - c`:
`𝔄(M) ≤ L^{-η³ + a(m-j) - η e - C₀ η⁵ (m+e)} · 𝔄(M - K)` for `L` large, `d ≥ 3`, where `a = 2γ₀ + 5η²`; pinned `K` by `N = 1`, unpinned by the box
`N = (⌊2L⌋+1)^d` and `j ≥ m + 1`.  Named inputs: `hfix` (subpro (3): an atom of degree `< 4` has its label fixed) and `hlad`
(the ladder-weight ratio `≤ (log L)^{c₀ (m+e)}`, O3 of R29 item 6). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem eDart_le {M : Molecule V D} {K : Finset V} (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hK : K ⊆ M.atoms) :
    eDart M K ≤ 4 * K.card := by
  have h1 := sum_deg_K hK
  have h2 : ∑ a ∈ K, M.deg a ≤ ∑ _a ∈ K, 4 := Finset.sum_le_sum fun a ha => hM4 a (hK ha)
  simp at h2
  omega

end WaveTurbulence.FinalCountG3
