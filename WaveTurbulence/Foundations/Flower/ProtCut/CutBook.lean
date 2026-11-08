/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutTerm
public import WaveTurbulence.Foundations.RegStruct.CodeOrders

/-! # D2c PROT-CUT: sizes and incoherency indices of the (cut-term) pieces

* `size_cutTerm`: `X.size = Xp.size + inner.size + Qr.size + Qg.size + 2` (the two cut nodes), every size even.
* `incoherency_cutTerm`: the incoherency index of the protected tree is the sum of those of the four pieces, plus
  `1` exactly when the cut link `(𝔫_a, 𝔫_b)` is incoherent;
* `incoherency_cutTerm_of_chainIn`: on a protected object (`ChainIn p`) the cut link is coherent, so the indices add
  to `g`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

theorem size_cutTerm (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) :
    (appendChain Xp (cpair m Qr Qg inner)).size = Xp.size + inner.size + Qr.size + Qg.size + 2 := by
  rw [appendChain_size]
  simp only [cpair, RegChain.size]
  ring

/-! ### The configuration `ProtCfg.term` -/

theorem lonePath_dropLast_cutTerm (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) :
    (appendChain Xp (cpair m Qr Qg inner)).lonePath.dropLast = Xp.lonePath ++ bPath m inner := by
  rw [appendChain_lonePath, cpair_lonePath, lonePos, ← List.append_assoc, List.dropLast_concat]

/-- `ProtCfg.term` on the code `appendChain Xp (pair m Qr Qg inner nil)` is the terminal pin `termFix`. -/
theorem termFix_eq_cfg (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (s t up : ℝ)
    {T : Fin 1 → TTree} :
    (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t up : GBranch T → Option ℝ) =
      termFix Xp m inner s := by
  funext b
  unfold ProtCfg.fix ProtCfg.pins termFix
  rw [if_pos (Fin.val_eq_zero b.1.1), lonePath_dropLast_cutTerm]
  simp only [List.lookup]
  by_cases h1 : b.1.2 = Xp.lonePath ++ bPath m inner
  · rw [if_pos h1, show (b.1.2 == Xp.lonePath ++ bPath m inner) = true from beq_iff_eq.mpr h1]
  · rw [if_neg h1, show (b.1.2 == Xp.lonePath ++ bPath m inner) = false from beq_eq_false_iff_ne.mpr h1]

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}
variable (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
include D

theorem layerAt_P (x : Fin 1 × Path) (hx : x.2 ∈ (LGp.garden.tree x.1).nodes) :
    layerAt LGp x = layerAt LG ((0 : Fin 1), x.2) := by
  exact (layerAt_node LGp (⟨x, hx⟩ : GNode LGp.garden.tree)).trans (D.layP _)

theorem layerAt_I (x : Fin 1 × Path) (hx : x.2 ∈ (LGi.garden.tree x.1).nodes) :
    layerAt LGi x = layerAt LG ((0 : Fin 1), Xp.lonePath ++ m.c :: x.2) := by
  exact (layerAt_node LGi (⟨x, hx⟩ : GNode LGi.garden.tree)).trans (D.layI _)

theorem layerAt_R (x : Fin 2 × Path) (hx : x.2 ∈ (LGr.garden.tree x.1).nodes) :
    layerAt LGr x = layerAt LG ((0 : Fin 1), Xp.lonePath ++ (rBase m inner (LG.garden.sig 0) x.1 ++ x.2)) := by
  exact (layerAt_node LGr (⟨x, hx⟩ : GNode LGr.garden.tree)).trans (D.layR _)

theorem layerAt_G (x : Fin 2 × Path) (hx : x.2 ∈ (LGg.garden.tree x.1).nodes) :
    layerAt LGg x = layerAt LG ((0 : Fin 1), Xp.lonePath ++ (gBase m inner (LG.garden.sig 0) x.1 ++ x.2)) := by
  exact (layerAt_node LGg (⟨x, hx⟩ : GNode LGg.garden.tree)).trans (D.layG _)

omit D in
theorem oriented_links_r (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (Q : RegCpl) (a : Fin 1 × Path) :
    (if slotSign ζ m.red.1 = 1 then Q.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Q.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) =
      Q.linksAt (addrExt a (rBase m inner ζ 0)) (addrExt a (rBase m inner ζ 1)) := by
  by_cases hs : slotSign ζ m.red.1 = 1 <;> simp [rBase, hs, bPath]

omit D in
theorem oriented_links_g (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (Q : RegCpl) (a : Fin 1 × Path) :
    (if slotSign ζ m.green.1 = 1 then
        Q.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Q.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) =
      Q.linksAt (addrExt a (gBase m inner ζ 0)) (addrExt a (gBase m inner ζ 1)) := by
  by_cases hs : slotSign ζ m.green.1 = 1 <;> simp [gBase, hs, bPath]

/-- **The incoherency index splits over the pieces of the cut.** -/
theorem incoherency_cutTerm :
    LG.incoherency ((appendChain Xp (cpair m Qr Qg inner)).treeLinks (LG.garden.sig 0)) =
      LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) + LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) +
        LGr.incoherency Qr.links + LGg.incoherency Qg.links +
        (if layerAt LG ((0 : Fin 1), Xp.lonePath) = layerAt LG ((0 : Fin 1), Xp.lonePath ++ bPath m inner)
          then 0 else 1) := by
  classical
  set ζ := LG.garden.sig 0
  set P : (Fin 1 × Path) × (Fin 1 × Path) → Bool := fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2)
  rw [tree_incoherency_eq_count D.dec, tree_incoherency_eq_count D.decP, tree_incoherency_eq_count D.decI,
    incoherency_eq_count D.decR, incoherency_eq_count D.decG]
  -- the prefix
  have hP : (Xp.treeLinks (LGp.garden.sig 0)).filter (fun l => layerAt LGp l.1 ≠ layerAt LGp l.2) =
      (Xp.linksAt ζ ((0 : Fin 1), [])).filter P := by
    rw [RegChain.treeLinks, D.sigP]
    refine List.filter_congr fun l hl => ?_
    have h1 := (tree_mem_pairEndpoints_links_iff D.decP l.1).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks, D.sigP]; exact hl, Or.inl rfl⟩)
    have h2 := (tree_mem_pairEndpoints_links_iff D.decP l.2).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks, D.sigP]; exact hl, Or.inr rfl⟩)
    rw [D.layerAt_P l.1 (TTree.branching_subset_nodes _ h1), D.layerAt_P l.2 (TTree.branching_subset_nodes _ h2)]
    have e1 : ((0 : Fin 1), l.1.2) = l.1 := Prod.ext (Subsingleton.elim _ _) rfl
    have e2 : ((0 : Fin 1), l.2.2) = l.2 := Prod.ext (Subsingleton.elim _ _) rfl
    rw [e1, e2]
  -- the interior
  let fi : Fin 1 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), Xp.lonePath ++ m.c :: x.2)
  have hfi : ∀ x q, fi (addrExt x q) = addrExt (fi x) q := by intro x q; simp [fi, addrExt]
  have hI : (inner.linksAt (slotSign ζ m.c) (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) [m.c])).filter P =
      ((inner.treeLinks (LGi.garden.sig 0)).filter (fun l => layerAt LGi l.1 ≠ layerAt LGi l.2)).map
        (fun l => (fi l.1, fi l.2)) := by
    have e0 : addrExt (addrExt ((0 : Fin 1), ([] : Path)) Xp.lonePath) [m.c] = fi ((0 : Fin 1), []) := by
      simp [fi, addrExt]
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
  let fr : Fin 2 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), Xp.lonePath ++ (rBase m inner ζ x.1 ++ x.2))
  have hfr : ∀ x q, fr (addrExt x q) = addrExt (fr x) q := by intro x q; simp [fr, addrExt]
  have hR : (Qr.linksAt (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (rBase m inner ζ 0))
        (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (rBase m inner ζ 1))).filter P =
      ((Qr.links).filter (fun l => layerAt LGr l.1 ≠ layerAt LGr l.2)).map (fun l => (fr l.1, fr l.2)) := by
    have e0 : addrExt (addrExt ((0 : Fin 1), ([] : Path)) Xp.lonePath) (rBase m inner ζ 0) = fr (0, []) := by
      simp [fr, addrExt]
    have e1 : addrExt (addrExt ((0 : Fin 1), ([] : Path)) Xp.lonePath) (rBase m inner ζ 1) = fr (1, []) := by
      simp [fr, addrExt]
    rw [e0, e1, couple_linksAt_map Qr fr hfr, RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching D.decR hl
    simp only [Function.comp_apply, P]
    rw [D.layerAt_R l.1 (TTree.branching_subset_nodes _ hb.1), D.layerAt_R l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  let fg : Fin 2 × Path → Fin 1 × Path := fun x => ((0 : Fin 1), Xp.lonePath ++ (gBase m inner ζ x.1 ++ x.2))
  have hfg : ∀ x q, fg (addrExt x q) = addrExt (fg x) q := by intro x q; simp [fg, addrExt]
  have hG : (Qg.linksAt (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (gBase m inner ζ 0))
        (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (gBase m inner ζ 1))).filter P =
      ((Qg.links).filter (fun l => layerAt LGg l.1 ≠ layerAt LGg l.2)).map (fun l => (fg l.1, fg l.2)) := by
    have e0 : addrExt (addrExt ((0 : Fin 1), ([] : Path)) Xp.lonePath) (gBase m inner ζ 0) = fg (0, []) := by
      simp [fg, addrExt]
    have e1 : addrExt (addrExt ((0 : Fin 1), ([] : Path)) Xp.lonePath) (gBase m inner ζ 1) = fg (1, []) := by
      simp [fg, addrExt]
    rw [e0, e1, couple_linksAt_map Qg fg hfg, RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching D.decG hl
    simp only [Function.comp_apply, P]
    rw [D.layerAt_G l.1 (TTree.branching_subset_nodes _ hb.1), D.layerAt_G l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  -- assemble
  have hL : (appendChain Xp (cpair m Qr Qg inner)).treeLinks ζ = Xp.linksAt ζ ((0 : Fin 1), []) ++
      ((addrExt ((0 : Fin 1), []) Xp.lonePath, addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath)
          ([m.c] ++ inner.lonePath)) ::
        (Qr.linksAt (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (rBase m inner ζ 0))
            (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (rBase m inner ζ 1)) ++
          Qg.linksAt (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (gBase m inner ζ 0))
            (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (gBase m inner ζ 1)) ++
          inner.linksAt (slotSign ζ m.c) (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) [m.c]) ++ [])) := by
    rw [RegChain.treeLinks, appendChain_linksAt]
    congr 1
    simp only [cpair, RegChain.linksAt]
    rw [oriented_links_r, oriented_links_g]
  rw [hL]
  simp only [List.filter_append, List.filter_cons, List.length_append, List.filter_nil, List.length_nil,
    add_zero]
  rw [show (List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2)) (Xp.linksAt ζ ((0 : Fin 1), []))) =
    (Xp.linksAt ζ ((0 : Fin 1), [])).filter P from rfl, ← hP]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (inner.linksAt (slotSign ζ m.c) (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) [m.c])) =
      (inner.linksAt (slotSign ζ m.c) (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) [m.c])).filter P from rfl,
    hI]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (Qr.linksAt (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (rBase m inner ζ 0))
        (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (rBase m inner ζ 1))) =
      (Qr.linksAt (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (rBase m inner ζ 0))
        (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (rBase m inner ζ 1))).filter P from rfl, hR]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (Qg.linksAt (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (gBase m inner ζ 0))
        (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (gBase m inner ζ 1))) =
      (Qg.linksAt (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (gBase m inner ζ 0))
        (addrExt (addrExt ((0 : Fin 1), []) Xp.lonePath) (gBase m inner ζ 1))).filter P from rfl, hG]
  try simp only [List.length_map]
  have eb : addrExt ((0 : Fin 1), Xp.lonePath) ([m.c] ++ inner.lonePath) =
      ((0 : Fin 1), Xp.lonePath ++ bPath m inner) := by simp [addrExt, bPath]
  split_ifs with h1 h2 h2 <;>
    simp only [List.length_cons, List.length_append, List.length_map, List.length_nil] <;>
    simp_all [addrExt, bPath] <;> omega

/-- On a protected object the cut link is coherent: **the incoherency indices add**. -/
theorem incoherency_cutTerm_of_chainIn {p : ℕ}
    (hch : ChainIn p (appendChain Xp (cpair m Qr Qg inner)) LG) :
    LG.incoherency ((appendChain Xp (cpair m Qr Qg inner)).treeLinks (LG.garden.sig 0)) =
      LGp.incoherency (Xp.treeLinks (LGp.garden.sig 0)) + LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) +
        LGr.incoherency Qr.links + LGg.incoherency Qg.links := by
  rw [D.incoherency_cutTerm]
  have hlp : (appendChain Xp (cpair m Qr Qg inner)).lonePath = Xp.lonePath ++ (bPath m inner ++ [m.lone]) := by
    rw [appendChain_lonePath, cpair_lonePath]; rfl
  obtain ⟨GZ, hsZ, hZ⟩ := D.exists_GZ
  have layer_of : ∀ (q : Path) (hq : q <+: (appendChain Xp (cpair m Qr Qg inner)).lonePath)
      (hne : q ≠ (appendChain Xp (cpair m Qr Qg inner)).lonePath) (hb : q ∈ (LG.garden.tree 0).branching),
      layerAt LG ((0 : Fin 1), q) = p := by
    intro q hq hne hb
    have := hch ⟨((0 : Fin 1), q), hb⟩ rfl hq hne
    rw [← layerAt_node] at this
    exact this
  have hab : layerAt LG ((0 : Fin 1), Xp.lonePath) = layerAt LG ((0 : Fin 1), Xp.lonePath ++ bPath m inner) := by
    rw [layer_of Xp.lonePath (by rw [hlp]; exact List.prefix_append _ _)
        (by rw [hlp]; simp [bPath])
        (by have := (D.aB hZ hsZ).2; rw [D.aB_path hZ hsZ] at this; exact this),
      layer_of (Xp.lonePath ++ bPath m inner) (by rw [hlp, ← List.append_assoc]; exact List.prefix_append _ _)
        (by rw [hlp]; simp)
        (by have := (D.bG hZ hsZ).2; rw [D.bG_path hZ hsZ] at this; exact this)]
  simp [hab]

end CutTermData

end WaveTurbulence.Flower.ProtCut
