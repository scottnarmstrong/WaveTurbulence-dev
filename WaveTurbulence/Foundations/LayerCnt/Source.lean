/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Unconditional
public import WaveTurbulence.Foundations.LayerCnt.RegionBridge
import Mathlib.Tactic

/-! # TARGET Proposition `layervine` (L1513–L1532), literal source hypotheses

`G` is the skeleton (a plain garden); each pre-layering `f` of the family is the layering induced by a canonical layered
object `LG` decoding `G` (Definition `lftwist`); the regular trees at the branching nodes of `𝕍 \ {u₁}` and the regular
couples at the leaf pairs having a leaf below such a node are coherent.  Then (with `g = 0`) the bound improves to
`C₀^{m + |q - q'|}`; the first bound holds for every vine.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine TTree Reg Reg.Skeleton LFTwist
variable {w : ℕ}

theorem CanonPairs.mono {G : Garden w} {f : GBranch G.tree → ℕ} {p : ℕ} {Reg Reg' : GNode G.tree → Prop}
    (h : CanonPairs G f p Reg') (hR : ∀ n, Reg n → Reg' n) : CanonPairs G f p Reg :=
  fun a a' ha ha' hinc hcp => h a a' (hR _ ha) (hR _ ha') hinc hcp

open Classical in
/-- The source hypothesis of the improved bound: `f` is induced by a canonical layered object whose regular attachments
at `𝕍 \ {u₁}` are coherent. -/
@[expose] def SourceRegion (G : Garden w) (hG : G.IsPlain) (p : ℕ) (S : Finset (GBranch G.tree)) (a : GBranch G.tree)
    (f : GBranch G.tree → ℕ) : Prop :=
  ∃ (kind : Bool) (LG : LayeredGarden w) (D : ReconstructionData G) (hd : D.Decodes hG LG.garden),
    CanonicalObject p kind LG ∧ f = inducedPrelayer LG D hG hd ∧
    (∀ x ∈ S, x ≠ a → CohT LG D x) ∧
    (∀ q : SourcePair G, (∃ ℓ : GLeaf G.tree, ∃ hr : ℓ.1.2 ≠ [], pairOfLeaf G hG ℓ = q ∧
      GNode.parent ℓ.toNode hr ∈ S ∧ GNode.parent ℓ.toNode hr ≠ a) → CohQ LG D hG q)

theorem SourceRegion.prelayering {G : Garden w} {hG : G.IsPlain} {p : ℕ} {S : Finset (GBranch G.tree)}
    {a : GBranch G.tree} {f : GBranch G.tree → ℕ} (h : SourceRegion G hG p S a f) :
    IsBranchPrelayering G f := by
  obtain ⟨kind, LG, D, hd, _, rfl, _⟩ := h
  exact inducedPrelayer_isBranchPrelayering LG D hG hd

theorem SourceRegion.canonPairs {G : Garden w} {hG : G.IsPlain} {p : ℕ} {S : Finset (GBranch G.tree)}
    {a : GBranch G.tree} {f : GBranch G.tree → ℕ} (h : SourceRegion G hG p S a f) :
    CanonPairs G f p (RegV G S a) := by
  classical
  obtain ⟨kind, LG, D, hd, hc, rfl, hT, hQ⟩ := h
  have hmain := canonPairs_of_region hG D hd hc (S.erase a)
    (Finset.univ.filter (fun q : SourcePair G => ∃ ℓ : GLeaf G.tree, ∃ hr : ℓ.1.2 ≠ [], pairOfLeaf G hG ℓ = q ∧
      GNode.parent ℓ.toNode hr ∈ S ∧ GNode.parent ℓ.toNode hr ≠ a))
    (fun c hc => hT c (Finset.mem_erase.mp hc).2 (Finset.mem_erase.mp hc).1)
    (fun q hq => hQ q (Finset.mem_filter.mp hq).2)
  refine hmain.mono ?_
  rintro n (⟨x, hx, hxa, rfl⟩ | ⟨ℓ, hr, hp, hpa, hn⟩)
  · exact Or.inl ⟨x, Finset.mem_erase.mpr ⟨hxa, hx⟩, rfl⟩
  · have hq : pairOfLeaf G hG ℓ ∈ Finset.univ.filter (fun q : SourcePair G => ∃ ℓ : GLeaf G.tree, ∃ hr : ℓ.1.2 ≠ [],
        pairOfLeaf G hG ℓ = q ∧ GNode.parent ℓ.toNode hr ∈ S ∧ GNode.parent ℓ.toNode hr ≠ a) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ℓ, hr, rfl, hp, hpa⟩
    rcases hn with hn | hn
    · exact Or.inr ⟨ℓ, hn, hq⟩
    · exact Or.inr ⟨G.pair ℓ, hn, by rw [pairOfLeaf_partner]; exact hq⟩

/-- **TARGET `layervine`, improved bound**, with the source hypotheses: for a (CL) vine and layerings of incoherency
index `0` induced by canonical layered objects whose regular attachments at `𝕍 \ {u₁}` are coherent. -/
theorem layervine_improved_source (B : ℝ) (hB : 1 ≤ B) :
    ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ {w : ℕ} (G : Garden w) (hG : G.IsPlain) (X : VineType) (S : Finset (GBranch G.tree))
      (a b : GBranch G.tree) (hV : G.molecule.IsVine X S a b) (hCL : Mole.CLParentPattern G S a b)
      (R : VineRealization G.molecule X S a b) (m : ℕ),
      (X.IsBad = true → S.card = 2 * m + 2) → (X.IsBad = false → S.card = 2 * m + 5) →
      ∀ (p q q' : ℕ) (𝓕 : Finset (GBranch G.tree → ℕ)),
        (∀ f ∈ 𝓕, SourceRegion G hG p S a f) →
        (∀ f ∈ 𝓕, realizedIncoherencyIndex R f = 0) →
        (∀ f ∈ 𝓕, f a = q ∧ f b = q') →
        (∀ f ∈ 𝓕, ∀ f' ∈ 𝓕, (∀ x ∈ S, f x = f' x) → f = f') →
        ∑ f ∈ 𝓕, ∏ x ∈ bondsIn G.molecule S,
            B ^ dst (f (G.molecule.atom x)) (f (G.molecule.atom (G.molecule.mate x))) ≤
          C₀ ^ (m + (q - q')) := by
  obtain ⟨C₀, hC₀, h⟩ := layervine_improved B hB
  refine ⟨C₀, hC₀, ?_⟩
  intro w G hG X S a b hV hCL R m hbad hnorm p q q' 𝓕 hsrc hcoh hjoint hinj
  exact h G X S a b hV hCL R m hbad hnorm p q q' 𝓕 (fun f hf => (hsrc f hf).prelayering) hcoh hjoint
    (fun f hf => (hsrc f hf).canonPairs) hinj

end WaveTurbulence.LayerCnt
