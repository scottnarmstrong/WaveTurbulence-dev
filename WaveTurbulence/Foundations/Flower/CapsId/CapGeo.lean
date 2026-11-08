/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsId.Transport
/-! # A2-R2 CAPS-ID: the capped geometry (`MkDefs.CapGeo`, `MkDefs.CapPatValid`) of a carrier garden

On the frozen flower carrier (`IsCanonH (p + 1) LG`, `PatValid` per tree) the capped garden `capLayered LG p` with cap
trees `capJ w` satisfies D2b's standing geometry `CapGeo` (cap trees are leaves, layers `≤ p`, capped stems in layer
`p`, one capped flower per tree) and the capped `dChild` clause `CapPatValid` for the pattern `capExt pat .plain`
(ruling R163). Components inherit both by restriction (A3b). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsId
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {w : ℕ}

/-- With one flower per tree, a tree has at most one flower parent. -/
theorem flowerParent_unique (G : Garden w) (hF : OneFlower G) {c c' : GBranch G.tree} (hc : G.IsFlowerParent c)
    (hc' : G.IsFlowerParent c') (h : c.1.1 = c'.1.1) : c = c' := by
  obtain ⟨ℓ, hℓ, h1, i, h2⟩ := hc
  obtain ⟨ℓ', hℓ', h1', i', h2'⟩ := hc'
  have hl : ℓ = ℓ' := (hF c.1.1).unique ⟨h1, hℓ⟩ ⟨h1'.trans h.symm, hℓ'⟩
  have e1 : c.1.2 = ℓ.1.2.dropLast := by rw [h2, List.dropLast_concat]
  have e2 : c'.1.2 = ℓ.1.2.dropLast := by rw [hl, h2', List.dropLast_concat]
  exact Subtype.ext (Prod.ext h (e1.trans e2.symm))

/-- **`CapGeo` on the carrier**: the capped garden of a canonical flower garden. -/
theorem capGeo_capLayered (LG : LayeredGarden w) (p : ℕ) (h : IsCanonH (p + 1) LG) :
    CapGeo (capLayered LG p) (capJ w) p := by
  have hF := oneFlower_of_isFlowerGarden h.1
  have hfl := flower_layer_of_isCanonH h
  refine ⟨fun j hj => capGarden_tree_of_mem_capJ LG.garden hj, fun x => ?_, fun x hx => ?_, fun x x' hx hx' he => ?_⟩
  · rcases node_cases LG.garden x with ⟨a, rfl⟩ | ⟨j, rfl⟩
    · show capLayer LG p (embN LG.garden a) ≤ p
      rw [capLayer_embN]
      exact h.2.2.1 a
    · exact (capLayered_layer_capN_of LG p hfl j).le
  · rcases node_cases LG.garden x with ⟨a, rfl⟩ | ⟨j, rfl⟩
    · show capLayer LG p (embN LG.garden a) = p
      rw [capLayer_embN]
      exact h.2.1 a ((onCapStem_embN LG p hF a).1 hx)
    · exfalso
      obtain ⟨y, hy, hd⟩ := hx
      obtain ⟨ℓ, -, rfl⟩ := (isCapFlower_iff LG p hF y).1 hy
      have := hd.1
      simp only [capN_val, embL_toNode, embN_val, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq] at this
  · obtain ⟨ℓ, hℓ, rfl⟩ := (isCapFlower_iff LG p hF x).1 hx
    obtain ⟨ℓ', hℓ', rfl⟩ := (isCapFlower_iff LG p hF x').1 hx'
    simp only [embL_val, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at he
    rw [(hF ℓ.1.1).unique ⟨rfl, hℓ⟩ ⟨he.symm, hℓ'⟩]

/-- **`CapPatValid` on the carrier**: the capped `dChild` clause of the pattern `capExt pat .plain`. -/
theorem capPatValid_capLayered (LG : LayeredGarden w) (p : ℕ) (h : IsCanonH (p + 1) LG) (pat : Fin w → FixPat)
    (hpat : ∀ j, LG.PatValid p j (pat j)) : CapPatValid (capLayered LG p) (capJ w) (capExt pat .plain) p := by
  have hF := oneFlower_of_isFlowerGarden h.1
  intro b c i hc hpc hb
  obtain ⟨b, rfl⟩ := (cBranch LG.garden).surjective b
  obtain ⟨c, rfl⟩ := (cBranch LG.garden).surjective c
  have hc0 := (isCapFlowerParent_cBranch LG p hF c).1 hc
  have hpc0 : pat c.1.1 = FixPat.dChild i := by simpa only [cBranch_val, capExt_inl] using hpc
  simp only [cBranch_val, Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq] at hb
  show capLayer LG p (embN LG.garden b.toNode) = p
  rw [capLayer_embN]
  have hv := hpat c.1.1
  rw [hpc0] at hv
  obtain ⟨b', c', hc', hcj, hbj, hb'p, hlay⟩ := hv
  have hcc : c' = c := flowerParent_unique LG.garden hF hc' hc0 hcj
  subst hcc
  have hbb : b' = b := Subtype.ext (Prod.ext (hbj.trans hb.1.symm) (hb'p.trans hb.2.symm))
  rw [← hbb]
  exact hlay

end WaveTurbulence.Flower.CapsId
