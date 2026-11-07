/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Improved
public import WaveTurbulence.Foundations.LayerCnt.LowerHalf
import Mathlib.Tactic

/-! # TARGET `layervine`, improved bound (L1522–L1532), modulo the canonical pair criterion on the vine region

For a (CL) vine with incoherency index zero, the layer range `[𝔏_{v_2}, 𝔏_{v_1}]` of its atoms is proved
(`layer_le_upper`, `lower_half_aux`); the pair criterion `canonequiv` (ii) on the nodes of the vine region
(`CanonPairs G f p (RegV G S a)`, discharged in `Source` from the source hypotheses) is the only input, and it is what the source obtains by replacing the coherent regular
attachments of the region by single nodes (Remark `sublayer`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine TTree
variable {w : ℕ}

/-- The nodes of the vine region `G_sk[V] \ {u₁}` whose attachments are erased: the branching nodes of the vine other than the
top joint `a`, and the leaves paired with a leaf whose parent is such a node. -/
@[expose] def RegV (G : Garden w) (S : Finset (GBranch G.tree)) (a : GBranch G.tree) (n : GNode G.tree) : Prop :=
  (∃ x ∈ S, x ≠ a ∧ x.toNode = n) ∨ (∃ ℓ : GLeaf G.tree, ∃ hr : ℓ.1.2 ≠ [], GNode.parent ℓ.toNode hr ∈ S ∧
    GNode.parent ℓ.toNode hr ≠ a ∧ (ℓ.toNode = n ∨ (G.pair ℓ).toNode = n))

theorem layer_range (G : Garden w) {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine X S a b) (hCL : Mole.CLParentPattern G S a b)
    (R : VineRealization G.molecule X S a b) {f : GBranch G.tree → ℕ} {p : ℕ}
    (hf : LFTwist.IsBranchPrelayering G f) (hcoh : realizedIncoherencyIndex R f = 0)
    (hC : CanonPairs G f p (RegV G S a)) : ∀ x ∈ S, f b ≤ f x ∧ f x ≤ f a := by
  intro x hx
  have hco := (realizedIncoherencyIndex_eq_zero_iff R f).mp hcoh
  exact ⟨lower_half_aux hf hC hV.1 hCL (fun y hy hya => Or.inl ⟨y, hy, hya, rfl⟩)
      (fun ℓ hr hp hpa => Or.inr ⟨ℓ, hr, hp, hpa, Or.inr rfl⟩) X R hco x hx,
    layer_le_upper G hV.1 hCL hf x hx⟩

/-- **`layervine`, improved bound** (T L1522–L1532), for a (CL) vine and layerings with `g = 0` satisfying the canonical pair
criterion on the vine region (the effect of coherent attachments, Remark `sublayer`). -/
theorem layervine_improved (B : ℝ) (hB : 1 ≤ B) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ {w : ℕ} (G : Garden w) (X : VineType) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree)
      (hV : G.molecule.IsVine X S a b) (hCL : Mole.CLParentPattern G S a b)
      (R : VineRealization G.molecule X S a b) (m : ℕ),
      (X.IsBad = true → S.card = 2 * m + 2) → (X.IsBad = false → S.card = 2 * m + 5) →
      ∀ (p q q' : ℕ) (𝓕 : Finset (GBranch G.tree → ℕ)),
        (∀ f ∈ 𝓕, LFTwist.IsBranchPrelayering G f) →
        (∀ f ∈ 𝓕, realizedIncoherencyIndex R f = 0) →
        (∀ f ∈ 𝓕, f a = q ∧ f b = q') →
        (∀ f ∈ 𝓕, CanonPairs G f p (RegV G S a)) →
        (∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, f x = f' x) → f = f') →
        ∑ f ∈ 𝓕, ∏ x ∈ bondsIn G.molecule S,
            B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) ≤
          C₀ ^ (m + (q - q')) := by
  classical
  obtain ⟨C₀, hC₀, h⟩ := layervine_improved_of_range B hB
  refine ⟨C₀, hC₀, ?_⟩
  intro w G X S a b hV hCL R m hbad hnorm p q q' 𝓕 hpre hcoh hjoint hC hinj
  by_cases hne : 𝓕 = ∅
  · subst hne
    simp only [Finset.sum_empty]
    positivity
  · obtain ⟨f0, hf0⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hr0 := layer_range G hV hCL R (hpre f0 hf0) (hcoh f0 hf0) (hC f0 hf0) a
      hV.1.2.1
    have hqq : q' ≤ q := by
      have := hjoint f0 hf0
      have := hr0.1
      omega
    refine h G X S a b R m hbad hnorm q q' hqq 𝓕 hpre hcoh ?_ hinj
    intro f hf x hx
    have := layer_range G hV hCL R (hpre f hf) (hcoh f hf) (hC f hf) x hx
    have hj := hjoint f hf
    omega

end WaveTurbulence.LayerCnt
