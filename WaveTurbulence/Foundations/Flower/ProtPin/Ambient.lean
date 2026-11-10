/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtDefs.Defs
public import WaveTurbulence.Foundations.Flower.ProtGeo.Extract
public import WaveTurbulence.Foundations.Flower.MkDefs.Defs
public import WaveTurbulence.Foundations.Flower.ProtCut.Cap
public import WaveTurbulence.Foundations.VineEst.ZpSurj.ConjTree1

/-! # D3 PROT-PIN: the canonical ambient of a protected object (R172)

* Copied by source from D0-PROT's probe `scope/D0-PROT/probe/AmbientProbe.lean` (sha256 in COPIED-SHA256SUMS), with
  its local `ProtAmbient` replaced by `ProtDefs.ProtAmbient` (the same text): `protAmbient_objTree`,
  `protAmbient_objCpl`, `canon_of_mkCarries` (supply, for D2b/B3s) and `protAmbient_termCut`,
  `protAmbient_cap_chain` (transport).
* `TreeAmb p X LG`: the sign-free part of the tree clause of `ProtAmbient` (canonical `H`, chain embedding with the
  object's root sign, the object's layers read in `H`): all that the layer arguments use.
* `capAmb_norm`: the ambient of a cap couple normalized to the sign `ζ = 1` by conjugating `H` (main `conjLayered`,
  `chainEmb_conj`, `layerAt_conj`; the canonicity transfer is main's `isCoherentCoupleAt_conj` argument, copied):
  the object's code `X = ConjCoh.conjChain X₀` is embedded with sign `1` in the conjugate canonical garden. This is
  the conjugation transfer of R163 F-D2b-2 at the level of the ambient (the object itself is already normalized).
* `treeAmb_of_cap`: the paired tree of a cap couple (D2c `CapData`) inherits the ambient. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct WaveTurbulence.Links WaveTurbulence.Reg Set Finset
open scoped Classical

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.MkDefs

/-! ## (2a) Supply from `MkCarries` (copied from the D0 probe) -/

/-- Paired trees: D2b's `objTree` of a stem chain, with the ambient root sign. -/
theorem protAmbient_objTree {w : ℕ} {LG : LayeredGarden w} {p : ℕ} (hcan : IsCanonGC (p + 1) LG)
    {X : RegChain} {ζ : ℤˣ} {u : Fin w × TTree.Path} {h : TTree} (hE : ChainEmb LG.garden X ζ u h)
    (hζ : nodeSign LG.garden.sig u = ζ) :
    ProtAmbient p X (objTree LG X ζ u hE) :=
  ⟨w, LG, u, h, hcan, hE, hζ, fun _ => rfl⟩

/-! ## (2b) Transport to the pieces of the terminal cut (copied from the D0 probe) -/

/-! ## The sign-free tree ambient -/

/-- **The tree ambient used by the layer arguments**: a canonical `H` of level `p + 1`, the chain `X` embedded at `a`
with the object's root sign, and the object's layers read in `H`. -/
def TreeAmb (p : ℕ) (X : RegChain) (LG : LayeredGarden 1) : Prop :=
  ∃ (w' : ℕ) (H : LayeredGarden w') (a : Fin w' × TTree.Path) (h : TTree),
    IsCanonGC (p + 1) H ∧ ChainEmb H.garden X (LG.garden.sig 0) a h ∧
    ∀ z : GNode LG.garden.tree, LG.layer z = layerAt H (addrExt a z.1.2)

theorem treeAmb_of_protAmbient {p : ℕ} {X : RegChain} {LG : LayeredGarden 1} (h : ProtAmbient p X LG) :
    TreeAmb p X LG := by
  obtain ⟨w', H, a, t, hc, hE, -, hl⟩ := h
  exact ⟨w', H, a, t, hc, hE, hl⟩

/-! ## Conjugating the canonical ambient -/

/-- A canonical garden has a canonical conjugate (along the identity for width `≥ 4`, along the swap of the two
roots for width `2`); main's `isCoherentCoupleAt_conj`, copied. -/
theorem exists_conj_canon {p w : ℕ} {H : LayeredGarden w} (hc : IsCanonGC (p + 1) H) :
    ∃ e : Fin w ≃ Fin w, IsCanonGC (p + 1) (ConjCoh.conjLayered H e) := by
  obtain ⟨hplain, hirr, hcrit⟩ := hc
  rcases hirr with ⟨hw4, hI⟩ | ⟨hw2, hsig⟩
  · have hconj := ConjCoh.conjLayered_isConjugateBy H (Equiv.refl (Fin w))
    exact ⟨Equiv.refl (Fin w), ⟨ConjCoh.conj_isPlain hconj hplain,
      Or.inl ⟨hw4, ConjCoh.conj_irreducible hconj hI⟩, ConjCoh.conj_canonCriterion hconj hcrit⟩⟩
  · subst hw2
    have hconj := ConjCoh.conjLayered_isConjugateBy H (Equiv.swap (0 : Fin 2) 1)
    refine ⟨Equiv.swap (0 : Fin 2) 1, ⟨ConjCoh.conj_isPlain hconj hplain, Or.inr ⟨rfl, fun j => ?_⟩,
      ConjCoh.conj_canonCriterion hconj hcrit⟩⟩
    show -H.garden.sig ((Equiv.swap (0 : Fin 2) 1).symm j) = (-1) ^ (j : ℕ)
    fin_cases j
    · simp [hsig]
    · simp [hsig]

theorem units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := fun h => by
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  simp at h'

/-- **The cap ambient with the sign normalized to `1`** (R163 F-D2b-2): the object's own code `X` is embedded with
sign `1` in a canonical garden, the cap tree root at `b`, with the object's layers. -/
theorem capAmb_norm {p : ℕ} {X : RegChain} {LG : LayeredGarden 2} (hA : ProtAmbient p X LG) :
    ∃ (w' : ℕ) (H : LayeredGarden w') (a b : Fin w' × TTree.Path), IsCanonGC (p + 1) H ∧
      ChainEmb H.garden X 1 a .leaf ∧
      ∀ z : GNode LG.garden.tree,
        LG.layer z = (if z.1.1 = 0 then layerAt H (addrExt a z.1.2) else layerAt H b) := by
  obtain ⟨w', H, a, b, ζ, X₀, hc, hE, -, hX, -, -, -, hl⟩ := hA
  rcases Int.units_eq_one_or ζ with rfl | rfl
  · rw [if_pos rfl] at hX
    subst hX
    exact ⟨w', H, a, b, hc, hE, hl⟩
  · rw [if_neg units_neg_one_ne_one] at hX
    subst hX
    obtain ⟨e, hce⟩ := exists_conj_canon hc
    have hconj := ConjCoh.conjLayered_isConjugateBy H e
    have hE' := ZpSurj.chainEmb_conj hconj hE
    rw [neg_neg] at hE'
    refine ⟨w', ConjCoh.conjLayered H e, ConjCoh.phi e a, ConjCoh.phi e b, hce, hE', fun z => ?_⟩
    rw [hl z]
    split_ifs
    · exact (ConjCoh.layerAt_conj hconj (addrExt a z.1.2)).symm
    · exact (ConjCoh.layerAt_conj hconj b).symm

/-- **The paired tree of a cap couple inherits the ambient** (D2c `CapData`: same tree `0`, sign `1`, layers of
tree `0`). -/
theorem treeAmb_of_cap {p : ℕ} {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1}
    (hA : ProtAmbient p X LG) (D : ProtCut.CapData X LG LG1) : TreeAmb p X LG1 := by
  obtain ⟨w', H, a, b, hc, hE, hl⟩ := capAmb_norm hA
  refine ⟨w', H, a, .leaf, hc, by rw [D.sig1]; exact hE, fun z => ?_⟩
  rw [D.lay z]
  have hz0 : z.1.1 = 0 := Subsingleton.elim _ _
  have hz : z.1.2 ∈ (LG.garden.tree (0 : Fin 2)).nodes := by
    have h2 := z.2
    rw [hz0, D.treeT] at h2
    rw [D.tree0]
    exact h2
  rw [layerAt_of_mem LG (z := ((0 : Fin 2), z.1.2)) hz, hl ⟨((0 : Fin 2), z.1.2), hz⟩]
  exact if_pos rfl

end WaveTurbulence.Flower.ProtPin
