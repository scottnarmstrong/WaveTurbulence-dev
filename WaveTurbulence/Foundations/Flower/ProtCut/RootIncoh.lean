/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootBook

/-! # D2c PROT-CUT: incoherency at the root cut

* `RootData.incoherency_rootCut`: incoherency(X) = Σ pieces + [the root link is incoherent];
* `RootData.incoherency_rootCut_of_chainIn`: on a protected object (`ChainIn p X LG`) the root link is coherent, so
  the incoherency indices of the suffix, interior and side couples add up to that of `X`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace RootData

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

theorem layerAt_S (x : Fin 1 × Path) (hx : x.2 ∈ (LGs.garden.tree x.1).nodes) :
    layerAt LGs x = layerAt LG ((0 : Fin 1), lonePos m inner ++ x.2) :=
  (layerAt_node LGs (⟨x, hx⟩ : GNode LGs.garden.tree)).trans (D.layS _)

theorem layerAt_I (x : Fin 1 × Path) (hx : x.2 ∈ (LGi.garden.tree x.1).nodes) :
    layerAt LGi x = layerAt LG ((0 : Fin 1), m.c :: x.2) :=
  (layerAt_node LGi (⟨x, hx⟩ : GNode LGi.garden.tree)).trans (D.layI _)

theorem layerAt_R (x : Fin 2 × Path) (hx : x.2 ∈ (LGr.garden.tree x.1).nodes) :
    layerAt LGr x = layerAt LG ((0 : Fin 1), rBase m inner (LG.garden.sig 0) x.1 ++ x.2) :=
  (layerAt_node LGr (⟨x, hx⟩ : GNode LGr.garden.tree)).trans (D.layR _)

theorem layerAt_G (x : Fin 2 × Path) (hx : x.2 ∈ (LGg.garden.tree x.1).nodes) :
    layerAt LGg x = layerAt LG ((0 : Fin 1), gBase m inner (LG.garden.sig 0) x.1 ++ x.2) :=
  (layerAt_node LGg (⟨x, hx⟩ : GNode LGg.garden.tree)).trans (D.layG _)

/-- **The incoherency index splits over the pieces of the root cut.** -/
theorem incoherency_rootCut :
    LG.incoherency ((RegChain.pair m Qr Qg inner rest).treeLinks (LG.garden.sig 0)) =
      LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) + LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) +
        LGr.incoherency Qr.links + LGg.incoherency Qg.links +
        (if layerAt LG ((0 : Fin 1), []) = layerAt LG ((0 : Fin 1), bPath m inner) then 0 else 1) := by
  classical
  set ζ := LG.garden.sig 0
  set P : (Fin 1 × Path) × (Fin 1 × Path) → Bool := fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2)
  rw [tree_incoherency_eq_count D.dec, tree_incoherency_eq_count D.decS, tree_incoherency_eq_count D.decI,
    incoherency_eq_count D.decR, incoherency_eq_count D.decG]
  -- the suffix
  let fs : Fin 1 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), lonePos m inner ++ x.2)
  have hfs : ∀ x q, fs (addrExt x q) = addrExt (fs x) q := by intro x q; simp [fs, addrExt]
  have hS : (rest.linksAt ζ ((0 : Fin 1), lonePos m inner)).filter P =
      ((rest.treeLinks (LGs.garden.sig 0)).filter (fun l => layerAt LGs l.1 ≠ layerAt LGs l.2)).map
        (fun l => (fs l.1, fs l.2)) := by
    have e0 : ((0 : Fin 1), lonePos m inner) = fs ((0 : Fin 1), []) := by simp [fs]
    rw [e0, chain_linksAt_map rest fs hfs, RegChain.treeLinks, D.sigS, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have h1 := (tree_mem_pairEndpoints_links_iff D.decS l.1).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks, D.sigS]; exact hl, Or.inl rfl⟩)
    have h2 := (tree_mem_pairEndpoints_links_iff D.decS l.2).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks, D.sigS]; exact hl, Or.inr rfl⟩)
    simp only [Function.comp_apply, P]
    rw [D.layerAt_S l.1 (TTree.branching_subset_nodes _ h1), D.layerAt_S l.2 (TTree.branching_subset_nodes _ h2)]
  -- the interior
  let fi : Fin 1 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), m.c :: x.2)
  have hfi : ∀ x q, fi (addrExt x q) = addrExt (fi x) q := by intro x q; simp [fi, addrExt]
  have hI : (inner.linksAt (slotSign ζ m.c) (addrExt ((0 : Fin 1), []) [m.c])).filter P =
      ((inner.treeLinks (LGi.garden.sig 0)).filter (fun l => layerAt LGi l.1 ≠ layerAt LGi l.2)).map
        (fun l => (fi l.1, fi l.2)) := by
    have e0 : addrExt ((0 : Fin 1), ([] : Path)) [m.c] = fi ((0 : Fin 1), []) := by simp [fi, addrExt]
    rw [e0, chain_linksAt_map inner fi hfi, RegChain.treeLinks, D.sigI, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have h1 := (tree_mem_pairEndpoints_links_iff D.decI l.1).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks, D.sigI]; exact hl, Or.inl rfl⟩)
    have h2 := (tree_mem_pairEndpoints_links_iff D.decI l.2).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks, D.sigI]; exact hl, Or.inr rfl⟩)
    simp only [Function.comp_apply, P]
    rw [D.layerAt_I l.1 (TTree.branching_subset_nodes _ h1), D.layerAt_I l.2 (TTree.branching_subset_nodes _ h2)]
  -- the couples
  let fr : Fin 2 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), rBase m inner ζ x.1 ++ x.2)
  have hfr : ∀ x q, fr (addrExt x q) = addrExt (fr x) q := by intro x q; simp [fr, addrExt]
  have hR : (Qr.linksAt (addrExt ((0 : Fin 1), []) (rBase m inner ζ 0))
        (addrExt ((0 : Fin 1), []) (rBase m inner ζ 1))).filter P =
      ((Qr.links).filter (fun l => layerAt LGr l.1 ≠ layerAt LGr l.2)).map (fun l => (fr l.1, fr l.2)) := by
    have e0 : addrExt ((0 : Fin 1), ([] : Path)) (rBase m inner ζ 0) = fr (0, []) := by simp [fr, addrExt]
    have e1 : addrExt ((0 : Fin 1), ([] : Path)) (rBase m inner ζ 1) = fr (1, []) := by simp [fr, addrExt]
    rw [e0, e1, couple_linksAt_map Qr fr hfr, RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching D.decR hl
    simp only [Function.comp_apply, P]
    rw [D.layerAt_R l.1 (TTree.branching_subset_nodes _ hb.1), D.layerAt_R l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  let fg : Fin 2 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), gBase m inner ζ x.1 ++ x.2)
  have hfg : ∀ x q, fg (addrExt x q) = addrExt (fg x) q := by intro x q; simp [fg, addrExt]
  have hG : (Qg.linksAt (addrExt ((0 : Fin 1), []) (gBase m inner ζ 0))
        (addrExt ((0 : Fin 1), []) (gBase m inner ζ 1))).filter P =
      ((Qg.links).filter (fun l => layerAt LGg l.1 ≠ layerAt LGg l.2)).map (fun l => (fg l.1, fg l.2)) := by
    have e0 : addrExt ((0 : Fin 1), ([] : Path)) (gBase m inner ζ 0) = fg (0, []) := by simp [fg, addrExt]
    have e1 : addrExt ((0 : Fin 1), ([] : Path)) (gBase m inner ζ 1) = fg (1, []) := by simp [fg, addrExt]
    rw [e0, e1, couple_linksAt_map Qg fg hfg, RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching D.decG hl
    simp only [Function.comp_apply, P]
    rw [D.layerAt_G l.1 (TTree.branching_subset_nodes _ hb.1), D.layerAt_G l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  -- assemble
  have hL : (RegChain.pair m Qr Qg inner rest).treeLinks ζ =
      ((((0 : Fin 1), []), addrExt ((0 : Fin 1), []) ([m.c] ++ inner.lonePath)) ::
        (Qr.linksAt (addrExt ((0 : Fin 1), []) (rBase m inner ζ 0)) (addrExt ((0 : Fin 1), []) (rBase m inner ζ 1)) ++
          Qg.linksAt (addrExt ((0 : Fin 1), []) (gBase m inner ζ 0)) (addrExt ((0 : Fin 1), []) (gBase m inner ζ 1)) ++
          inner.linksAt (slotSign ζ m.c) (addrExt ((0 : Fin 1), []) [m.c]) ++ [])) ++
        rest.linksAt ζ ((0 : Fin 1), lonePos m inner) := by
    rw [RegChain.treeLinks, show RegChain.pair m Qr Qg inner rest = appendChain (cpair m Qr Qg inner) rest from rfl,
      appendChain_linksAt, cpair_lonePath]
    congr 1
    simp only [RegChain.linksAt]
    rw [CutTermData.oriented_links_r, CutTermData.oriented_links_g]
  rw [hL]
  simp only [List.filter_append, List.filter_cons, List.length_append, List.filter_nil, List.length_nil,
    add_zero]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (inner.linksAt (slotSign ζ m.c) (addrExt ((0 : Fin 1), []) [m.c])) =
      (inner.linksAt (slotSign ζ m.c) (addrExt ((0 : Fin 1), []) [m.c])).filter P from rfl, hI]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (Qr.linksAt (addrExt ((0 : Fin 1), []) (rBase m inner ζ 0)) (addrExt ((0 : Fin 1), []) (rBase m inner ζ 1))) =
      (Qr.linksAt (addrExt ((0 : Fin 1), []) (rBase m inner ζ 0))
        (addrExt ((0 : Fin 1), []) (rBase m inner ζ 1))).filter P from rfl, hR]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (Qg.linksAt (addrExt ((0 : Fin 1), []) (gBase m inner ζ 0)) (addrExt ((0 : Fin 1), []) (gBase m inner ζ 1))) =
      (Qg.linksAt (addrExt ((0 : Fin 1), []) (gBase m inner ζ 0))
        (addrExt ((0 : Fin 1), []) (gBase m inner ζ 1))).filter P from rfl, hG]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (rest.linksAt ζ ((0 : Fin 1), lonePos m inner)) =
      (rest.linksAt ζ ((0 : Fin 1), lonePos m inner)).filter P from rfl, hS]
  try simp only [List.length_map]
  have eb : addrExt ((0 : Fin 1), ([] : Path)) ([m.c] ++ inner.lonePath) = ((0 : Fin 1), bPath m inner) := by
    simp [addrExt, bPath]
  split_ifs with h1 h2 h2 <;>
    simp only [List.length_cons, List.length_append, List.length_map, List.length_nil] <;>
    simp_all [addrExt, bPath] <;> omega

/-- On a protected object the root link is coherent: **the incoherency indices add**. -/
theorem incoherency_rootCut_of_chainIn {p : ℕ} (hch : ChainIn p (RegChain.pair m Qr Qg inner rest) LG) :
    LG.incoherency ((RegChain.pair m Qr Qg inner rest).treeLinks (LG.garden.sig 0)) =
      LGs.incoherency (rest.treeLinks (LGs.garden.sig 0)) + LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) +
        LGr.incoherency Qr.links + LGg.incoherency Qg.links := by
  rw [D.incoherency_rootCut]
  have hlp : (RegChain.pair m Qr Qg inner rest).lonePath = bPath m inner ++ (m.lone :: rest.lonePath) := by
    simp [RegChain.lonePath, bPath]
  have layer_of : ∀ (q : Path) (hq : q <+: (RegChain.pair m Qr Qg inner rest).lonePath)
      (hne : q ≠ (RegChain.pair m Qr Qg inner rest).lonePath) (hb : q ∈ (LG.garden.tree 0).branching),
      layerAt LG ((0 : Fin 1), q) = p := by
    intro q hq hne hb
    have := hch ⟨((0 : Fin 1), q), hb⟩ rfl hq hne
    rw [← layerAt_node] at this
    exact this
  have hab : layerAt LG ((0 : Fin 1), []) = layerAt LG ((0 : Fin 1), bPath m inner) := by
    rw [layer_of [] (List.nil_prefix) (by rw [hlp]; simp [bPath])
        (by have := D.aR.2; rw [D.aR_path] at this; exact this),
      layer_of (bPath m inner) (by rw [hlp]; exact List.prefix_append _ _) (by rw [hlp]; simp)
        (by have := D.bR.2; rw [D.bR_path] at this; exact this)]
  simp [hab]

end RootData

end WaveTurbulence.Flower.ProtCut
