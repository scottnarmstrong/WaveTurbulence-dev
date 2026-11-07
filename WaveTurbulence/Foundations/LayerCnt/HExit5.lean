/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.HExit4
import Mathlib.Tactic

/-! # The exit lemma, general form (TARGET layervine, L1531)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open TTree
variable {w : ℕ}

/-- The up-dart `d₁` and any second exit `d₂`: the conclusion of the exit lemma. -/
theorem exit_with_up {G : Garden w} {f : GBranch G.tree → ℕ} (hf : LFTwist.IsBranchPrelayering G f)
    {p : ℕ} {Reg : GNode G.tree → Prop} (hC : CanonPairs G f p Reg) {K S : Finset (GBranch G.tree)}
    (hKS : K ⊆ S) {c1 : GBranch G.tree} (hc1 : c1.1.2 ≠ []) {d2 : GardenDart G}
    (h : ExitData G K (upDart G c1 hc1) d2) (h12 : upDart G c1 hc1 ≠ d2)
    (hc1K : c1 ∈ K) (hp1 : GNode.parent c1.toNode hc1 ∉ K)
    (h2in : G.molecule.atom d2 ∈ K) (h2out : G.molecule.atom (G.molecule.mate d2) ∉ K)
    (hco : f c1 = f (G.molecule.atom d2))
    (hSn : ∀ d, G.molecule.atom d ∈ K → G.molecule.atom (G.molecule.mate d) ∈ S)
    (hRegK : ∀ x ∈ K, Reg x.toNode)
    (hRegLeafK : ∀ ℓ : GLeaf G.tree, ∀ hr : ℓ.1.2 ≠ [], GNode.parent ℓ.toNode hr ∈ K →
      Reg (G.pair ℓ).toNode) :
    min (f (GNode.parent c1.toNode hc1)) (f (G.molecule.atom (G.molecule.mate d2))) ≤ f c1 := by
  rcases d2 with ⟨⟨c2, hc2⟩, _ | _⟩ | ⟨ℓ0, hm, hr, hp⟩
  · -- up-up
    have h2in' : c2 ∈ K := h2in
    have h2out' : GNode.parent c2.toNode hc2 ∉ K := h2out
    exact exit_up_up hC hc1 hc2 h h12 hc1K h2in' hp1 h2out' (hRegK _ hc1K) (hRegK _ h2in') |>
      fun h' => (by
        have hco' : f c1 = f c2 := hco
        have : max (f c1) (f c2) = f c1 := by rw [← hco']; simp
        exact this ▸ h')
  · -- up-down
    have h2in' : GNode.parent c2.toNode hc2 ∈ K := h2in
    have h2out' : c2 ∉ K := h2out
    have hco' : f c1 = f (GNode.parent c2.toNode hc2) := hco
    have := garden_parent_step_le G hf c2 hc2
    show min _ (f c2) ≤ _
    omega
  · -- up-lp
    have hz4 : GNode.parent ℓ0.toNode hr ∈ K := h2in
    have hz3 : GNode.parent (G.pair ℓ0).toNode hp ∉ K := h2out
    have hz3S : GNode.parent (G.pair ℓ0).toNode hp ∈ S := hSn _ h2in
    exact exit_up_lp hC hc1 hm hr hp h hc1K hz4 hz3 (hRegK _ hc1K)
      (hRegLeafK _ hr hz4) hco

/-- **The exit lemma.** -/
theorem exit_lemma {G : Garden w} {f : GBranch G.tree → ℕ} (hf : LFTwist.IsBranchPrelayering G f)
    {p : ℕ} {Reg : GNode G.tree → Prop} (hC : CanonPairs G f p Reg) {K S : Finset (GBranch G.tree)}
    (hKS : K ⊆ S) {d1 d2 : GardenDart G} (h : ExitData G K d1 d2) (h12 : d1 ≠ d2)
    (h1in : G.molecule.atom d1 ∈ K) (h1out : G.molecule.atom (G.molecule.mate d1) ∉ K)
    (h2in : G.molecule.atom d2 ∈ K) (h2out : G.molecule.atom (G.molecule.mate d2) ∉ K)
    (hco : f (G.molecule.atom d1) = f (G.molecule.atom d2))
    (hSn : ∀ d, G.molecule.atom d ∈ K → G.molecule.atom (G.molecule.mate d) ∈ S)
    (hRegK : ∀ x ∈ K, Reg x.toNode)
    (hRegLeafK : ∀ ℓ : GLeaf G.tree, ∀ hr : ℓ.1.2 ≠ [], GNode.parent ℓ.toNode hr ∈ K →
      Reg (G.pair ℓ).toNode) :
    min (f (G.molecule.atom (G.molecule.mate d1))) (f (G.molecule.atom (G.molecule.mate d2))) ≤
      f (G.molecule.atom d1) := by
  obtain ⟨c, hc, hcd, _⟩ := h.exit_tops _ h1in
  rcases hcd with rfl | rfl
  · have := exit_with_up hf hC hKS hc h h12 h1in h1out h2in h2out hco hSn hRegK hRegLeafK
    exact this
  · -- the second exit is the up-dart
    have h' : ExitData G K (upDart G c hc) d1 :=
      ⟨h.deg4, fun d hd1 hd2 => (h.ex d hd1 hd2).symm⟩
    have := exit_with_up hf hC hKS hc h' h12.symm h2in h2out h1in h1out hco.symm hSn hRegK hRegLeafK
    rw [min_comm]
    exact hco ▸ this

end WaveTurbulence.LayerCnt
