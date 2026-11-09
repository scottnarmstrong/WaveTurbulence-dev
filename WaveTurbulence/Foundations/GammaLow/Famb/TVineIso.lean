/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.Bridge
public import WaveTurbulence.Foundations.Molecule.IsoVineTransport
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects

/-!
# T-vines and `𝒱_γ` under directed garden isomorphisms

Main transports the drawn vines along a directed garden isomorphism (`Twist.iso_isVine`; used for the unit twists of
TARGET Definition `twist`, L1429, through `unitTwistDirectedIso`). This module does the same for the T-vines (pinned
`Molecule.IsTVine`) and their pieces (`Molecule.tvineGroups`), hence for every member of `𝒱_γ`
(`FinalCount.Src.IsSomeVine γ`). The proof reads a T-vine in its undirected multigraph (L1's bridge
`TVine.Core.isTVine_iff`, `tvineGroups_eq`) and relabels that multigraph along the branch bijection (`mapG`):
blocks, closures, (Y2) moves, the doubled triangle and the 2-cuts are relabelling invariant.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.GammaLow.Famb.TVineIso

open WaveTurbulence.TVine WaveTurbulence.TVine.Core Finset

section relabel

variable {V W : Type*} [DecidableEq V] [DecidableEq W] (e : V ≃ W)

/-- Relabel a multigraph along an equivalence of the vertex types. -/
def mapG (G : UMultigraph V) : UMultigraph W where
  verts := G.verts.map e.toEmbedding
  mult s := G.mult (Sym2.map e.symm s)
  supp s hs x hx := Finset.mem_map_equiv.mpr (G.supp _ hs (e.symm x) (Sym2.mem_map.mpr ⟨x, hx, rfl⟩))

theorem symm_map_map (t : Sym2 V) : Sym2.map e.symm (Sym2.map e t) = t := by
  rw [Sym2.map_map]; simp

theorem map_symm_map (s : Sym2 W) : Sym2.map e (Sym2.map e.symm s) = s := by
  rw [Sym2.map_map]; simp

theorem mapG_mult (G : UMultigraph V) (s : Sym2 W) : (mapG e G).mult s = G.mult (Sym2.map e.symm s) := rfl

theorem mapG_mult_map (G : UMultigraph V) (t : Sym2 V) : (mapG e G).mult (Sym2.map e t) = G.mult t := by
  rw [mapG_mult, symm_map_map]

theorem mapG_mult_mk (G : UMultigraph V) (a b : V) : (mapG e G).mult s(e a, e b) = G.mult s(a, b) := by
  rw [show s(e a, e b) = Sym2.map e s(a, b) from rfl, mapG_mult_map]

theorem mapG_verts (G : UMultigraph V) : (mapG e G).verts = G.verts.map e.toEmbedding := rfl

theorem mem_mapG_verts (G : UMultigraph V) (v : V) : e v ∈ (mapG e G).verts ↔ v ∈ G.verts := by
  rw [mapG_verts, Finset.mem_map_equiv, Equiv.symm_apply_apply]

theorem mem_map_iff (t : Sym2 V) (v : V) : e v ∈ Sym2.map e t ↔ v ∈ t := by
  rw [Sym2.mem_map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    rwa [← e.injective hxv]
  · intro h
    exact ⟨v, h, rfl⟩

theorem map_eq_mk_iff (t : Sym2 V) (c d : V) : Sym2.map e t = s(e c, e d) ↔ t = s(c, d) := by
  rw [show s(e c, e d) = Sym2.map e s(c, d) from rfl]
  exact (Sym2.map.injective e.injective).eq_iff

theorem exists_map (s : Sym2 W) : ∃ t : Sym2 V, s = Sym2.map e t := ⟨_, (map_symm_map e s).symm⟩

theorem map_erase_eq (S : Finset V) (a : V) : (S.erase a).map e.toEmbedding = (S.map e.toEmbedding).erase (e a) := by
  rw [Finset.map_erase]; rfl

/-! ### (Y2) moves, the doubled triangle -/

theorem y2Step_mapG {G G' : UMultigraph V} (h : Y2Step G G') : Y2Step (mapG e G) (mapG e G') := by
  obtain ⟨a, b, c, d, hab, hcd, hca, hcb, hda, hdb, h3, hc, hd, hax, hbx, hv, hm⟩ := h
  refine ⟨e a, e b, e c, e d, e.injective.ne hab, e.injective.ne hcd, e.injective.ne hca, e.injective.ne hcb,
    e.injective.ne hda, e.injective.ne hdb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mapG_mult_mk]; exact h3
  · rw [mapG_mult_mk]; exact hc
  · rw [mapG_mult_mk]; exact hd
  · intro x hxb hxc
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [mapG_mult_mk]
    exact hax y (fun h => hxb (by rw [h])) (fun h => hxc (by rw [h]))
  · intro x hxa hxd
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [mapG_mult_mk]
    exact hbx y (fun h => hxa (by rw [h])) (fun h => hxd (by rw [h]))
  · rw [mapG_verts, mapG_verts, hv, map_erase_eq, map_erase_eq]
  · intro s
    obtain ⟨t, rfl⟩ := exists_map e s
    rw [mapG_mult_map, mapG_mult_map, hm t]
    simp only [mem_map_iff, map_eq_mk_iff]

theorem isDoubledTriangle_mapG {G : UMultigraph V} (h : IsDoubledTriangle G) : IsDoubledTriangle (mapG e G) := by
  obtain ⟨a, b, c, hab, hac, hbc, hv, hm⟩ := h
  refine ⟨e a, e b, e c, e.injective.ne hab, e.injective.ne hac, e.injective.ne hbc, ?_, ?_⟩
  · rw [mapG_verts, hv]
    simp [Finset.map_insert, Finset.map_singleton]
  · intro s
    obtain ⟨t, rfl⟩ := exists_map e s
    rw [mapG_mult_map, hm t]
    simp only [map_eq_mk_iff]

theorem reducesToT_mapG {C : UMultigraph V} (h : ReducesToT C) : ReducesToT (mapG e C) := by
  obtain ⟨C', hr, hT⟩ := h
  exact ⟨mapG e C', Relation.ReflTransGen.lift (mapG e) (fun _ _ h => y2Step_mapG e h) _ _ hr,
    isDoubledTriangle_mapG e hT⟩

/-! ### Degrees, neighbours, blocks, closures -/

theorem deg_mapG (G : UMultigraph V) (v : V) : deg (mapG e G) (e v) = deg G v := by
  unfold deg
  rw [mapG_verts, Finset.sum_map]
  simp only [Equiv.coe_toEmbedding, mapG_mult_mk]

theorem nbrs_mapG (G : UMultigraph V) (v : V) : nbrs (mapG e G) (e v) = (nbrs G v).map e := by
  unfold nbrs
  rw [mapG_verts, Finset.sum_map, Multiset.map_add, Multiset.map_replicate, mapG_mult_mk]
  congr 1
  rw [← Multiset.coe_mapAddMonoidHom, map_sum]
  simp only [Equiv.coe_toEmbedding, mapG_mult_mk, Multiset.coe_mapAddMonoidHom, Multiset.map_replicate]

theorem isBlockU_mapG {G : UMultigraph V} {j₁ j₂ : V} (h : IsBlockU G j₁ j₂) :
    IsBlockU (mapG e G) (e j₁) (e j₂) := by
  obtain ⟨h1, h2, hne, hd1, hd2, hdeg, hconn⟩ := h
  refine ⟨(mem_mapG_verts e G j₁).mpr h1, (mem_mapG_verts e G j₂).mpr h2, e.injective.ne hne,
    by rw [deg_mapG]; exact hd1, by rw [deg_mapG]; exact hd2, ?_, ?_⟩
  · intro v hv hv1 hv2
    obtain ⟨u, rfl⟩ := e.surjective v
    rw [deg_mapG]
    exact hdeg u ((mem_mapG_verts e G u).mp hv) (fun h => hv1 (by rw [h])) (fun h => hv2 (by rw [h]))
  · intro u' hu' w' hw'
    obtain ⟨u, rfl⟩ := e.surjective u'
    obtain ⟨w, rfl⟩ := e.surjective w'
    have hp := hconn u ((mem_mapG_verts e G u).mp hu') w ((mem_mapG_verts e G w).mp hw')
    exact Relation.ReflTransGen.lift e (fun a b hab => (⟨(mem_mapG_verts e G a).mpr hab.1,
      (mem_mapG_verts e G b).mpr hab.2.1, by rw [mapG_mult_mk]; exact hab.2.2⟩ : AdjIn (mapG e G) (mapG e G).verts (e a)
        (e b))) _ _ hp

theorem isClosureU_mapG {G C : UMultigraph V} {j₁ j₂ : V} (h : IsClosureU G j₁ j₂ C) :
    IsClosureU (mapG e G) (e j₁) (e j₂) (mapG e C) := by
  obtain ⟨hσ, hv, hl, added, hcase, hm⟩ := h
  refine ⟨by rw [mapG_mult_mk]; exact hσ, ?_, ?_, added.map (Sym2.map e), ?_, ?_⟩
  · rw [mapG_verts, mapG_verts, hv, map_erase_eq, map_erase_eq]
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [mapG_mult_mk]
    exact hl y
  · rcases hcase with ⟨h0, a, b, c, d, h1, h2, hadd⟩ | ⟨h1', x, y, h1, h2, hadd⟩
    · refine Or.inl ⟨by rw [mapG_mult_mk]; exact h0, e a, e b, e c, e d, ?_, ?_, ?_⟩
      · rw [nbrs_mapG, h1]; simp
      · rw [nbrs_mapG, h2]; simp
      · rw [hadd]; simp
    · refine Or.inr ⟨by rw [mapG_mult_mk]; exact h1', e x, e y, ?_, ?_, ?_⟩
      · rw [nbrs_mapG, h1]; simp
      · rw [nbrs_mapG, h2]; simp
      · rw [hadd]; simp
  · intro s
    obtain ⟨t, rfl⟩ := exists_map e s
    rw [mapG_mult_map, mapG_mult_map, hm t,
      Multiset.count_map_eq_count' _ _ (Sym2.map.injective e.injective)]
    simp only [mem_map_iff]

/-- **A T-vine multigraph relabels to a T-vine multigraph.** -/
theorem isTVineU_mapG {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) :
    IsTVineU (mapG e G) (e j₁) (e j₂) := by
  obtain ⟨hB, hm, C, hC, hR⟩ := h
  refine ⟨isBlockU_mapG e hB, ?_, mapG e C, isClosureU_mapG e hC, reducesToT_mapG e hR⟩
  intro u' hu' v' hv' hne
  obtain ⟨u, rfl⟩ := e.surjective u'
  obtain ⟨v, rfl⟩ := e.surjective v'
  rw [mapG_mult_mk]
  exact hm u ((mem_mapG_verts e G u).mp hu') v ((mem_mapG_verts e G v).mp hv') (fun h => hne (by rw [h]))

/-! ### Cuts and pieces -/

theorem cut_mapG (G : UMultigraph V) (X : Finset V) :
    cut (mapG e G) (X.map e.toEmbedding) = cut G X := by
  unfold cut
  rw [mapG_verts, ← Finset.map_sdiff, Finset.sum_map]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.sum_map]
  simp only [Equiv.coe_toEmbedding, mapG_mult_mk]

theorem samePieceU_mapG_iff (G : UMultigraph V) (u w : V) :
    SamePieceU (mapG e G) (e u) (e w) ↔ SamePieceU G u w := by
  constructor
  · intro h X hX hc
    have hX' : X.map e.toEmbedding ⊆ (mapG e G).verts := by
      rw [mapG_verts]; exact Finset.map_subset_map.mpr hX
    have := h _ hX' (by rw [cut_mapG]; exact hc)
    simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using this
  · intro h X' hX' hc
    have hXe : X' = (X'.map e.symm.toEmbedding).map e.toEmbedding := by
      rw [Finset.map_map]; ext x; simp
    rw [hXe] at hc ⊢
    rw [cut_mapG] at hc
    have hX : X'.map e.symm.toEmbedding ⊆ G.verts := by
      intro x hx
      rw [Finset.mem_map_equiv, Equiv.symm_symm] at hx
      have := hX' hx
      rwa [mapG_verts, Finset.mem_map_equiv, Equiv.symm_apply_apply] at this
    have := h _ hX hc
    simpa only [Finset.mem_map_equiv, Equiv.symm_apply_apply] using this

theorem interior_mapG (G : UMultigraph V) (j₁ j₂ : V) :
    Core.interior (mapG e G) (e j₁) (e j₂) = (Core.interior G j₁ j₂).map e.toEmbedding := by
  unfold Core.interior
  rw [mapG_verts, map_erase_eq, map_erase_eq]

/-- **The pieces relabel**: the pieces of the relabelled multigraph are the relabelled pieces. -/
theorem piecesU_mapG (G : UMultigraph V) (j₁ j₂ : V) :
    piecesU (mapG e G) (e j₁) (e j₂) = (piecesU G j₁ j₂).image (Finset.map e.toEmbedding) := by
  classical
  unfold piecesU
  rw [interior_mapG, Finset.map_eq_image, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro u _
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  ext x
  obtain ⟨y, rfl⟩ := e.surjective x
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_map_equiv, Equiv.symm_apply_apply,
    samePieceU_mapG_iff]
  constructor
  · rintro ⟨⟨z, hz, hzy⟩, hp⟩
    rw [e.injective hzy] at hz
    exact ⟨hz, hp⟩
  · rintro ⟨hz, hp⟩
    exact ⟨⟨y, hz, rfl⟩, hp⟩

end relabel

/-! ## Molecules of gardens -/

section garden

open WaveTurbulence.Twist

variable {w : ℕ} (G H : Garden w) (f : GardenDirectedIso G H)

/-- The undirected multigraph of a transported atomic group is the relabelled one. -/
theorem groupGraph_iso (S : Finset (GBranch G.tree)) :
    groupGraph H.molecule (isoAtoms G H f S) = mapG f.branches (groupGraph G.molecule S) := by
  apply TVine.Core.ext
  · show S.image f.branches = S.map f.branches.toEmbedding
    rw [Finset.map_eq_image]; rfl
  · intro s
    obtain ⟨t, rfl⟩ := exists_map f.branches s
    rw [mapG_mult_map, groupGraph_mult, groupGraph_mult, iso_groupBonds,
      Multiset.count_map_eq_count' _ _ (Sym2.map.injective f.branches.injective)]

/-- **T-vines are transported by directed garden isomorphisms.** -/
theorem iso_isTVine {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (h : G.molecule.IsTVine S a b) :
    H.molecule.IsTVine (isoAtoms G H f S) (f.branches a) (f.branches b) := by
  rw [isTVine_iff] at h ⊢
  obtain ⟨hB, hU⟩ := h
  refine ⟨iso_isBlock G H f hB, ?_⟩
  rw [groupGraph_iso]
  exact isTVineU_mapG f.branches hU

/-- **The T-vine groups (pieces) are transported.** -/
theorem iso_tvineGroups (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) :
    H.molecule.tvineGroups (isoAtoms G H f S) (f.branches a) (f.branches b) =
      (G.molecule.tvineGroups S a b).image (Finset.image f.branches) := by
  rw [tvineGroups_eq, tvineGroups_eq, groupGraph_iso, piecesU_mapG]
  apply Finset.image_congr
  intro P _
  exact Finset.map_eq_image _ _

/-- **Every member of `𝒱_γ` is transported by directed garden isomorphisms.** -/
theorem iso_isSomeVine {γ : ℝ} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (h : FinalCount.Src.IsSomeVine γ G.molecule S a b) :
    FinalCount.Src.IsSomeVine γ H.molecule (isoAtoms G H f S) (f.branches a) (f.branches b) := by
  rcases h with ⟨hγ, hI | hII | hT⟩ | ⟨hγ, X, hX⟩
  · exact Or.inl ⟨hγ, Or.inl (iso_isVine G H f hI)⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inl (iso_isVine G H f hII))⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inr (iso_isTVine G H f hT))⟩
  · exact Or.inr ⟨hγ, X, iso_isVine G H f hX⟩

end garden

end WaveTurbulence.GammaLow.Famb.TVineIso
