/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Decomp
/-! # A3b CAPS-COMP: the capped geometry of the class members (ruling R163)

Every member of a component class satisfies MkDefs's `CapGeo` (caps are leaves, layers `≤ p`, capped stems in layer
`p`, at most one capped flower per tree) and `CapPatValid` (a `dChild` pin is in layer `p`). Both are derived from
the class predicate: the capped stems from `CapStem`, one flower per tree from the cap matching, and the `dChild`
layer from `CapPatExist` (the per-tree form of the frozen `PatValid`) with the uniqueness of the flower parent. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs

variable {w : ℕ} {P : WTParams} {p N : ℕ} {kind : FlowerKind} {pat : Fin w → FixPat} {ζ : ℤˣ}

theorem leaf_path_nil_of_tree_leaf {W : ℕ} {G : Garden W} (ℓ : GLeaf G.tree) (h : G.tree ℓ.1.1 = TTree.leaf) :
    ℓ.1.2 = [] := by
  have := ℓ.2
  rw [h] at this
  simpa [TTree.leaves] using this

/-- **`CapGeo` and `CapPatValid` for the class members** (R163). -/
theorem capGeo_of_mem_classX {x : RawStr w N} {hx : ValidStr x} {c : Fin x.m} {G : LayeredGarden (2 * x.R c)}
    (hG : G ∈ classX P p N kind pat ζ x hx c) :
    CapGeo G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) p ∧
      CapPatValid G (resJ (x.sigmaX hx (capSgn ζ)) (capJ w) c) (resF (x.sigmaX hx (capSgn ζ)) (capExt pat .plain) c) p := by
  unfold classX at hG
  obtain ⟨⟨hmk, -⟩, hcaps, hmatch, hlab⟩ := mem_classOf.1 hG
  set σx := x.sigmaX hx (capSgn ζ) with hσx
  set J := resJ σx (capJ w) c with hJ
  -- the cap of a capped flower determines the flower's tree
  have hcap : ∀ ℓ : GLeaf G.garden.tree, IsCapFlower G J ℓ →
      σx ⟨c, ℓ.1.1⟩ = capσ w (.inl (origIdx (σx ⟨c, (G.garden.pair ℓ).1.1⟩))) := by
    intro ℓ hℓ
    have := hmatch (G.garden.pair ℓ) hℓ.2
    rw [G.garden.pair_pair] at this
    exact this
  have hone : ∀ ℓ ℓ' : GLeaf G.garden.tree, IsCapFlower G J ℓ → IsCapFlower G J ℓ' → ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ' := by
    intro ℓ ℓ' hℓ hℓ' he
    have e1 := hcap ℓ hℓ
    have e2 := hcap ℓ' hℓ'
    rw [he, e2] at e1
    have e3 : origIdx (σx ⟨c, (G.garden.pair ℓ').1.1⟩) = origIdx (σx ⟨c, (G.garden.pair ℓ).1.1⟩) :=
      Sum.inl_injective ((capσ w).injective e1)
    have hm1 := hℓ.2
    have hm2 := hℓ'.2
    rw [hJ, mem_resJ, mem_capJ_iff] at hm1 hm2
    obtain ⟨j1, hj1⟩ := hm1
    obtain ⟨j2, hj2⟩ := hm2
    rw [hj1, hj2, origIdx_inr, origIdx_inr] at e3
    have e4 : σx ⟨c, (G.garden.pair ℓ).1.1⟩ = σx ⟨c, (G.garden.pair ℓ').1.1⟩ := by rw [hj1, hj2, e3]
    have e5 := σx.injective e4
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e5
    have p1 := leaf_path_nil_of_tree_leaf _ (hcaps _ hℓ.2)
    have p2 := leaf_path_nil_of_tree_leaf _ (hcaps _ hℓ'.2)
    have e6 : G.garden.pair ℓ = G.garden.pair ℓ' := Subtype.ext (Prod.ext e5 (p1.trans p2.symm))
    have := congrArg G.garden.pair e6
    rwa [G.garden.pair_pair, G.garden.pair_pair] at this
  refine ⟨⟨hcaps, Canon.layer_le_of_isCanonGC hmk.1, fun a ha => ?_, hone⟩, ?_⟩
  · obtain ⟨ℓ, hℓ, hd⟩ := ha
    exact (hlab ℓ.1.1 hℓ.1).1 a hd.1 ⟨ℓ, hℓ, hd⟩
  · intro b cc i hcc hpat hb
    obtain ⟨ℓ, hℓ, hpar⟩ := hcc
    have htree : ℓ.1.1 = cc.1.1 := hpar.1
    have hnot : cc.1.1 ∉ J := htree ▸ hℓ.1
    have hlb := (hlab cc.1.1 hnot).2.2
    rw [hpat] at hlb
    obtain ⟨b', c', hc', hc'1, hb'1, hb'2, hb'3⟩ := hlb
    obtain ⟨ℓ', hℓ', hpar'⟩ := hc'
    have hll : ℓ = ℓ' := hone ℓ ℓ' hℓ hℓ' (by rw [htree, ← hc'1, ← hpar'.1])
    subst hll
    obtain ⟨k, hk⟩ := hpar.2
    obtain ⟨k', hk'⟩ := hpar'.2
    have e1 : cc.1.2 = c'.1.2 := by
      have := congrArg List.dropLast (hk.symm.trans hk')
      simpa using this
    have e2 : b = b' := Subtype.ext (by rw [hb, Prod.ext_iff]; exact ⟨hb'1.symm, by rw [hb'2, e1]⟩)
    rw [e2]; exact hb'3

end WaveTurbulence.Flower.CapsComp
