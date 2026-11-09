/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceFlowKind
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
/-! # Flows of chain ingredients over `𝒱_γ` (packet L5c, item E)

L5c port of main `Vine.chainIngredient_flow_eq` (Molecule/VineChainFlows.lean) and `RedSplice.pair_norm_ingredient`
(FinalCount/RedSpliceFlowKind.lean) (sha256 in COPIED-SHA256SUMS) for L5a's chain ingredients `Fama.ChainIngredientG γ`
over `𝒱_γ`. The proofs are main's; a member of `𝒱_γ` enters only through its block (`Src.isBlock_of_isSomeVine`), and the
prefix of a chain through L5a's `Fama.chain_prefix_isBlock`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc.Subpro
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.RedSplice WaveTurbulence.GammaLow.FinalCount

variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every ordered ingredient of an actual `𝒱_γ` chain has initial flow equal to the initial chain flow, and final
flow its negative (main `Vine.chainIngredient_flow_eq`). -/
theorem chainIngredientG_flow_eq {γ : ℝ} (M : Molecule V D) (hM : M.IsMolecule)
    (k : D → E) (hk : ∀ d, k (M.mate d) = k d)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ d ∈ M.dartsAt v, M.dartSign d • k d = 0)
    {U A : Finset V} {a b x y : V} {n : ℕ} (h : Fama.ChainIngredientG γ M U a b n A x y) :
    M.IsBlock U a b →
      groupFlow M A k x = groupFlow M U k a ∧ groupFlow M A k y = -groupFlow M U k a := by
  induction h with
  | single _h =>
    intro hU
    exact ⟨rfl, by rw [block_jointFlow_neg M hM hU k hk hc, neg_neg]⟩
  | @append_left S T A a b c x y n hI hT hi _hne ih =>
    intro hU
    have hS := Fama.chain_prefix_isBlock M hM (Fama.chainIngredientG_spec hI).1 hT hi hU
    have he := nested_groupFlow_eq M (show S ⊆ S ∪ T from Finset.subset_union_left) a
      ((Mole.block_joint_degrees M hS).1.trans (Mole.block_joint_degrees M hU).1.symm) k
    obtain ⟨hl, hr⟩ := ih hS
    exact ⟨hl.trans he, hr.trans (congrArg Neg.neg he)⟩
  | append_last _hS hT _hi _hne =>
    intro hU
    have hX := Src.isBlock_of_isSomeVine hT
    have he := terminal_block_initialFlow M hM hX hU Finset.subset_union_right k hk hc
    exact ⟨he, by rw [← he, block_jointFlow_neg M hM hX k hk hc, neg_neg]⟩

/-- The gap norm of an out/in pair at a joint of a `𝒱_γ` chain ingredient is the norm of the chain flow (main
`RedSplice.pair_norm_ingredient`). -/
theorem pair_norm_ingredientG {γ : ℝ} (M : Molecule V D) (hM : M.IsMolecule) {U A : Finset V} {a b x0 y0 j : V}
    {n : ℕ} (hI : Fama.ChainIngredientG γ M U a b n A x0 y0) (hU : M.IsBlock U a b) (hj : j = x0 ∨ j = y0)
    (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0)
    {x y : D} (hx : M.atom x = j) (hy : M.atom y = j) (hgx : M.InGroup A x) (hgy : M.InGroup A y)
    (hne : M.out x ≠ M.out y) :
    ‖k x - k y‖ = ‖groupFlow M U k a‖ := by
  have hX := Src.isBlock_of_isSomeVine (Fama.chainIngredientG_spec hI).2.1
  have h1 := pair_norm_block' M hM hX hj k hk hc hx hy hgx hgy hne
  have h2 := (chainIngredientG_flow_eq M hM k hk hc hI hU).1
  rw [h1, h2]

end WaveTurbulence.GammaLow.Famc.Subpro
