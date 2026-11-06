/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.PL234Draft.ConstProfile
public import WaveTurbulence.Foundations.Spine.PL234Draft.LeafSummable

/-!
# The leafwise kernel is multilinear in the leaf profiles (TARGET L1247)

TARGET's proof of Prop 6.2 (L1247): "the difference … contains those terms with at least one input being
`𝓡_p(k_𝔩)`". For leaf profiles `H₀ + H₁`, the leafwise kernel is the sum, over the subsets `S` of the input
leaves, of the kernels with profile `H₁` on `S` and `H₀` off `S` (`kernelLeaves_add`), given absolute
summability of each term.
-/

@[expose] public section

open Finset

namespace WaveTurbulence.PL234

open TTree WaveTurbulence.LGSpine

variable {w d : ℕ}

/-- The profile `H₁` at the leaves of `S`, `H₀` elsewhere. -/
noncomputable def mixProfile (LG : LayeredGarden w) (S : Finset (GLeaf LG.garden.tree))
    (H₀ H₁ : LeafProfiles w d) : LeafProfiles w d := by
  classical
  exact fun a => if a ∈ S.map (leafEmb LG.garden.tree) then H₁ a else H₀ a

theorem mixProfile_mem (LG : LayeredGarden w) {S : Finset (GLeaf LG.garden.tree)}
    (H₀ H₁ : LeafProfiles w d) {ℓ : GLeaf LG.garden.tree} (h : ℓ ∈ S) :
    mixProfile LG S H₀ H₁ ℓ.1 = H₁ ℓ.1 := by
  classical
  unfold mixProfile
  have hm : ℓ.1 ∈ S.map (leafEmb LG.garden.tree) := Finset.mem_map_of_mem (leafEmb LG.garden.tree) h
  exact ite_eq_left hm

theorem mixProfile_not_mem (LG : LayeredGarden w) {S : Finset (GLeaf LG.garden.tree)}
    (H₀ H₁ : LeafProfiles w d) {ℓ : GLeaf LG.garden.tree} (h : ℓ ∉ S) :
    mixProfile LG S H₀ H₁ ℓ.1 = H₀ ℓ.1 := by
  classical
  unfold mixProfile
  refine ite_eq_right fun hm => h ?_
  obtain ⟨ℓ', hℓ', he⟩ := Finset.mem_map.mp hm
  have : ℓ' = ℓ := Subtype.ext he
  rwa [← this]

/-- **The leafwise kernel is multilinear in the profiles.** -/
theorem kernelLeaves_add (L γ δ : ℝ) (LG : LayeredGarden w) (H₀ H₁ : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ)
    (hsum : ∀ S ∈ (inputLeaves LG.garden).powerset,
      Summable fun κ : GenDecoration LG.garden d nroot nfl =>
        leavesSummand L γ δ LG (mixProfile LG S H₀ H₁) up s k₀ κ) :
    kernelLeaves L γ δ LG (fun a x => H₀ a x + H₁ a x) up s k₀ nroot nfl =
      ∑ S ∈ (inputLeaves LG.garden).powerset,
        kernelLeaves L γ δ LG (mixProfile LG S H₀ H₁) up s k₀ nroot nfl := by
  classical
  simp only [kernelLeaves_eq_tsum]
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hsum]
  congr 1
  refine tsum_congr fun κ => ?_
  unfold leavesSummand
  rw [← Finset.mul_sum]
  congr 1
  simp only [Complex.ofReal_add]
  have hc : ∀ ℓ ∈ inputLeaves LG.garden,
      ((H₀ ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) +
        (H₁ ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)) =
      (H₁ ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) +
        (H₀ ℓ.1 (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ) := fun _ _ => add_comm _ _
  rw [Finset.prod_congr rfl hc, Finset.prod_add]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.mem_powerset] at hS
  rw [← Finset.union_sdiff_of_subset hS, Finset.prod_union Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset hS]
  congr 1
  · exact Finset.prod_congr rfl fun ℓ hℓ => by rw [mixProfile_mem LG H₀ H₁ hℓ]
  · exact Finset.prod_congr rfl fun ℓ hℓ => by
      rw [mixProfile_not_mem LG H₀ H₁ (Finset.mem_sdiff.mp hℓ).2]

end WaveTurbulence.PL234
