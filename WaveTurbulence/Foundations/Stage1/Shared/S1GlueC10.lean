/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.S1GlueC9
import Mathlib.Tactic

/-!
# Transfer of the layer pattern of a regular couple along a relabelling of layers
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LFTwist

variable {w : ℕ}

theorem cohOn_links_map {LG LG' : LayeredGarden w} (f : (Fin w × Path) → (Fin w × Path))
    (Q : RegCpl) (a b : Fin w × Path) (ha : RespectsAt f a) (hb : RespectsAt f b)
    (hlay : ∀ x, InRegion a b x → layerAt LG' x = layerAt LG (f x))
    (h : CohOn LG (Q.linksAt (f a) (f b))) : CohOn LG' (Q.linksAt a b) := by
  intro l hl
  have hmem : (f l.1, f l.2) ∈ Q.linksAt (f a) (f b) := by
    rw [couple_linksAt_map_local Q f a b ha hb]
    exact List.mem_map.mpr ⟨l, hl, rfl⟩
  have h1 : l.1 ∈ cplNodes Q a b :=
    Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).mpr ⟨l, hl, Or.inl rfl⟩)
  have h2 : l.2 ∈ cplNodes Q a b :=
    Finset.mem_union_left _ ((mem_pairEndpoints_iff _ _).mpr ⟨l, hl, Or.inr rfl⟩)
  rw [hlay _ (cplNodes_region h1), hlay _ (cplNodes_region h2)]
  exact h _ hmem

theorem layerPattern_map {LG LG' : LayeredGarden w} (f : (Fin w × Path) → (Fin w × Path))
    (Q : RegCpl) (a b : Fin w × Path) (p : ℕ) (ha : RespectsAt f a) (hb : RespectsAt f b)
    (hlay : ∀ x, InRegion a b x → layerAt LG' x = layerAt LG (f x))
    (hpa : parAt LG' p a = parAt LG p (f a)) (hpb : parAt LG' p b = parAt LG p (f b))
    (h : LayerPattern LG p Q (f a) (f b)) : LayerPattern LG' p Q a b := by
  obtain ⟨hcoh, hrest⟩ := h
  refine ⟨cohOn_links_map f Q a b ha hb hlay hcoh, ?_⟩
  have hlayA : ∀ x, Under a x → layerAt LG' x = layerAt LG (f x) := fun x hx => hlay x (Or.inl hx)
  have hlayB : ∀ x, Under b x → layerAt LG' x = layerAt LG (f x) := fun x hx => hlay x (Or.inr hx)
  cases Q with
  | triv =>
    intro z hz
    have hz' : f z ∈ cplNodes RegCpl.triv (f a) (f b) := by
      rw [cplNodes_map _ f a b ha hb]; exact Finset.mem_image_of_mem f hz
    rw [hlay z (cplNodes_region hz), hpa, hpb]
    exact hrest _ hz'
  | type1 c Q₁ Q₂ Q₃ =>
    intro z hz
    have hz' : f z ∈ cplNodes (RegCpl.type1 c Q₁ Q₂ Q₃) (f a) (f b) := by
      rw [cplNodes_map _ f a b ha hb]; exact Finset.mem_image_of_mem f hz
    rw [hlay z (cplNodes_region hz), hpa, hpb]
    exact hrest _ hz'
  | type2 Xp Xm Qlp =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrest
    have hfa : ∀ q, f (addrExt a q) = addrExt (f a) q := ha
    have hfb : ∀ q, f (addrExt b q) = addrExt (f b) q := hb
    refine ⟨?_, chainPairLayers_map f Xp 1 a ha hlayA h2, chainPairLayers_map f Xm (-1) b hb hlayB h3,
      ?_, ?_⟩
    · intro z hz
      have hz' : f z ∈ cplNodes Qlp (addrExt (f a) Xp.lonePath) (addrExt (f b) Xm.lonePath) := by
        rw [← hfa, ← hfb, cplNodes_map _ f _ _ (ha.child _) (hb.child _)]
        exact Finset.mem_image_of_mem f hz
      have hr := cplNodes_region hz
      have hreg : InRegion a b z := by
        rcases hr with hr | hr
        · exact Or.inl (under_trans (under_ext a _) hr)
        · exact Or.inr (under_trans (under_ext b _) hr)
      rw [hlay z hreg, hpa, hpb]
      exact h1 _ hz'
    · intro z hz
      have hu := chainNodesSet_under hz
      have hz' : f z ∈ chainNodesSet Xp 1 (f a) := by
        rw [chainNodesSet_map _ _ f a ha]; exact Finset.mem_image_of_mem f hz
      rw [hlayA z hu, hpa, hpb]
      rw [hpa] at *
      exact h4 _ hz'
    · intro z hz
      have hu := chainNodesSet_under hz
      have hz' : f z ∈ chainNodesSet Xm (-1) (f b) := by
        rw [chainNodesSet_map _ _ f b hb]; exact Finset.mem_image_of_mem f hz
      rw [hlayB z hu, hpa, hpb]
      exact h5 _ hz'

end WaveTurbulence.Stage1
