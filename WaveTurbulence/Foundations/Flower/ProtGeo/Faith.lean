/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Extract
public import WaveTurbulence.Foundations.RegStruct.AddressSigns

/-! # D2b PROT-GEO (10): the extracted objects are faithful to the carrier

For the identification of a protected object's sub-kernel of the carrier with `kernelProt` of its extraction
(B3s), the extraction carries the carrier's tree, layers (by definition), pairing and signs:
* `objTree_pair`: the pairing of `objTree` relocates to the carrier pairing (non-lone leaves);
* `objTree_nodeSign`: carrier signs are `σ_u ζ` times the extracted signs (`σ_u` the carrier sign at the root), so
  they agree when `ζ = σ_u` (`objTree_nodeSign_of`);
* `objCpl_nodeSign0`, `objCpl_nodeSign_cap`: carrier signs are `σ_u` times the extracted ones on both trees. For
  `σ_u = -1` the normalized cap couple (`ProtShape`'s `sig = ![1,-1]`) is the conjugate of the carrier object
  (finding F-D2b-2). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ} {LG : LayeredGarden w} {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {h : TTree}

theorem pathSign_eq_mul (σ : ℤˣ) (q : Path) : pathSign σ q = σ * pathSign 1 q := by
  simp [pathSign]

/-- **Pairing.** A non-lone leaf of the extracted paired tree is paired as its carrier leaf. -/
theorem objTree_pair (hE : ChainEmb LG.garden X ζ u h) (ℓ : GLeaf (objTree LG X ζ u hE).garden.tree)
    (hℓ : ℓ.1.2 ≠ X.lonePath) (ℓc : GLeaf LG.garden.tree) (hc : ℓc.1 = addrExt u ℓ.1.2) :
    (LG.garden.pair ℓc).1 = addrExt u ((objTree LG X ζ u hE).garden.pair ℓ).1.2 := by
  obtain ⟨-, -, hpair⟩ := decodedTree_decodes X ζ
  rcases mem_symmPairs.mp (hpair ℓ hℓ) with h1 | h1
  · exact hE.pairs _ (pairsAt_reloc X ζ u (0 : Fin 1) h1) ℓc hc
  · have hr := pairsAt_reloc X ζ u (0 : Fin 1) h1
    have hm : reloc u ((decodedTree X ζ).pair ℓ).1 ∈ pairEndpoints (X.pairsAt ζ u) :=
      (mem_pairEndpoints_iff _ _).mpr ⟨_, hr, Or.inl rfl⟩
    let g : GLeaf LG.garden.tree := ⟨_, (emb_endpoint_leaf hE hm).1⟩
    have hg : LG.garden.pair g = ℓc := Subtype.ext ((hE.pairs _ hr g rfl).trans hc.symm)
    rw [← hg, LG.garden.pair_pair]
    rfl

/-- **Signs (paired trees).** -/
theorem objTree_nodeSign (hE : ChainEmb LG.garden X ζ u h) (q : Path) :
    nodeSign LG.garden.sig (addrExt u q) =
      nodeSign LG.garden.sig u * ζ * nodeSign (objTree LG X ζ u hE).garden.sig ((0 : Fin 1), q) := by
  rw [nodeSign_addrExt]
  show pathSign (nodeSign LG.garden.sig u) q = _ * ζ * pathSign ζ q
  rw [pathSign_eq_mul (nodeSign LG.garden.sig u), pathSign_eq_mul ζ]
  rw [mul_assoc, ← mul_assoc ζ ζ, Int.units_mul_self, one_mul]

/-- **Signs (paired trees), faithful case**: with `ζ` the carrier sign at the root, the signs agree. -/
theorem objTree_nodeSign_of (hE : ChainEmb LG.garden X ζ u h) (hζ : ζ = nodeSign LG.garden.sig u) (q : Path) :
    nodeSign LG.garden.sig (addrExt u q) = nodeSign (objTree LG X ζ u hE).garden.sig ((0 : Fin 1), q) := by
  rw [objTree_nodeSign hE q]
  have : nodeSign LG.garden.sig u * ζ = 1 := by rw [hζ, Int.units_mul_self]
  rw [this, one_mul]

end WaveTurbulence.Flower.ProtGeo
