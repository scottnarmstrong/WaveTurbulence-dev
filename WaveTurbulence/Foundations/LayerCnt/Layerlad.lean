/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.LadderSum
public import WaveTurbulence.Foundations.LayerCnt.GardenParents

/-! # TARGET Proposition `layerlad` (L1501–L1512)

The weighted sum over layerings of a ladder of `𝕄(𝒢)` with incoherency index `g` is at most `C_0^m C_2^{g+1}`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine TTree
variable {w : ℕ}

/-- **TARGET `layerlad`** (L1501–L1512). Let `u, v : Fin (m+1) → GBranch G.tree` be a ladder of length `m` in the
molecule `𝕄(𝒢)` of a garden `𝒢`. A *layering of the atoms* is the restriction to the atoms of a pre-layering
`f` of `𝒢` (monotone along the parent relation, `IsBranchPrelayering`) with all values `≤ 𝔇` (for `𝒢 ∈ 𝒢_{p+1}`:
`0 ≤ 𝔏 ≤ p ≤ 𝔇`). For every finite family `𝓕` of such pre-layerings that are pairwise distinct on the atoms of the
ladder, the sum over the members whose incoherency index (`cohmol`, `Vine.incoherencyIndex f (ladderGroups u v)`)
equals `g` of `∏_ℓ B^{|𝔏_v − 𝔏_{v'}|}`, the product over the bonds `ℓ` joining atoms of the ladder, is at most
`C_0^m C_2^{g+1}`. Here `B` is TARGET's `C_0` in the product (an absolute constant `≥ 1`), `C_0` on the right is
"possibly different" and depends only on `B`, and `C_2` is any constant `≥ C_0^{𝔇+1}` (TARGET: `C_2` is arbitrarily
large depending on `𝔇`). The statement for the family of *all* layerings is the supremum over finite families. -/
theorem layerlad (B : ℝ) (hB : 1 ≤ B) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ {w : ℕ} (G : Garden w) {m : ℕ} (u v : Fin (m + 1) → GBranch G.tree),
      G.molecule.IsLadder u v → ∀ (𝔇 : ℕ) (C₂ : ℝ), C₀ ^ (𝔇 + 1) ≤ C₂ → ∀ g : ℕ, g ≤ m + 1 →
      ∀ 𝓕 : Finset (GBranch G.tree → ℕ),
        (∀ f ∈ 𝓕, LFTwist.IsBranchPrelayering G f ∧ ∀ x, f x ≤ 𝔇) →
        (∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ Molecule.ladderAtoms u v, f x = f' x) → f = f') →
        ∑ f ∈ 𝓕.filter (fun f => incoherencyIndex f (ladderGroups u v) = g),
            ∏ x ∈ bondsIn G.molecule (Molecule.ladderAtoms u v),
              B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) ≤
          C₀ ^ m * C₂ ^ (g + 1) := by
  refine ⟨max 9 ((2 : ℝ) ^ 6 * 3 ^ 16 * B ^ 28), le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro w G m u v hL 𝔇 C₂ hC₂ g _ 𝓕 hf hinj
  set C₀ : ℝ := max 9 ((2 : ℝ) ^ 6 * 3 ^ 16 * B ^ 28) with hC₀
  have hC1 : 1 ≤ C₀ := le_trans (by norm_num) (le_max_left _ _)
  have key := ladder_sum_le G.molecule (Mole.garden_isMolecule G) hL (depth := depthB G) B hB 𝓕
    (fun f hf' => ⟨(hf f hf').2, fun x hx => garden_parent_step G (hf f hf').1 x hx⟩) hinj g
  have hpr : ∀ f : GBranch G.tree → ℕ,
      ∏ x ∈ bondsIn G.molecule (Molecule.ladderAtoms u v),
        B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) =
      B ^ bondExp G.molecule (Molecule.ladderAtoms u v) f := fun f => by
    unfold bondExp; rw [Finset.prod_pow_eq_pow_sum]
  simp only [hpr]
  refine key.trans ?_
  have h9 : (9 : ℝ) ^ m ≤ C₀ ^ m := pow_le_pow_left₀ (by norm_num) (le_max_left _ _) m
  have hK : ((2 : ℝ) ^ 6 * 3 ^ 16 * B ^ 28) ^ 𝔇 ≤ C₂ := by
    calc _ ≤ C₀ ^ 𝔇 := pow_le_pow_left₀ (by positivity) (le_max_right _ _) 𝔇
      _ ≤ C₀ ^ (𝔇 + 1) := pow_le_pow_right₀ hC1 (by omega)
      _ ≤ C₂ := hC₂
  have hK0 : (0 : ℝ) ≤ ((2 : ℝ) ^ 6 * 3 ^ 16 * B ^ 28) ^ 𝔇 := by positivity
  exact mul_le_mul h9 (pow_le_pow_left₀ hK0 hK (g + 1)) (by positivity) (by positivity)

end WaveTurbulence.LayerCnt
