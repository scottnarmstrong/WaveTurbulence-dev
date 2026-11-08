/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ABook

/-! # D3-HELPER (P7), shape (a+): layers and the incoherency split

For `Root2Data LG m Qr Qg inner LGZ LGB` and `PairOnly LGZ …`: the layers of the four pieces read in `LG`
(`tc2a_layB`, `tc2a_layI`, `tc2a_layR`, `tc2a_layG`) and **`tc2a_incoh`**: the incoherency index of the couple is that
of the rest couple, the interior and the side couples, plus the root link `(𝔫_1, 𝔫_b)` when it is incoherent (the
couple version of D2c's `RootData.incoherency_rootCut`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The links of a rest couple. -/
theorem tc2a_closeCouple_linksAt {w : ℕ} (rest Xm : RegChain) (Qlp : RegCpl) (a b : Fin w × TTree.Path) :
    (SourceApp.closeCouple rest Xm Qlp).linksAt a b =
      rest.linksAt 1 a ++ Xm.linksAt (-1) b ++ Qlp.linksAt (addrExt a rest.lonePath) (addrExt b Xm.lonePath) := by
  unfold SourceApp.closeCouple
  cases rest <;> cases Xm <;> simp [RegChain.isNil, RegCpl.linksAt, RegChain.linksAt, RegChain.lonePath, addrExt]

theorem tc2a_oriented_r {w : ℕ} (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (Q : RegCpl) (a : Fin w × TTree.Path) :
    (if slotSign ζ m.red.1 = 1 then Q.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Q.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) =
      Q.linksAt (addrExt a (rBase m inner ζ 0)) (addrExt a (rBase m inner ζ 1)) := by
  by_cases hs : slotSign ζ m.red.1 = 1 <;> simp [rBase, hs, bPath]

theorem tc2a_oriented_g {w : ℕ} (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (Q : RegCpl) (a : Fin w × TTree.Path) :
    (if slotSign ζ m.green.1 = 1 then
        Q.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Q.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) =
      Q.linksAt (addrExt a (gBase m inner ζ 0)) (addrExt a (gBase m inner ζ 1)) := by
  by_cases hs : slotSign ζ m.green.1 = 1 <;> simp [gBase, hs, bPath]

section Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D

theorem tc2a_layZ (x : Fin 1 × TTree.Path) (hx : x.2 ∈ (LGZ.garden.tree x.1).nodes) :
    layerAt LGZ x = layerAt LG ((0 : Fin 2), x.2) :=
  (layerAt_node LGZ (⟨x, hx⟩ : GNode LGZ.garden.tree)).trans (D.layZ _)

theorem tc2a_layB (x : Fin 2 × TTree.Path) (hx : x.2 ∈ (LGB.garden.tree x.1).nodes) :
    layerAt LGB x = layerAt LG (botAddr (cpair m Qr Qg inner).lonePath x) :=
  (layerAt_node LGB (⟨x, hx⟩ : GNode LGB.garden.tree)).trans (D.layB _)

include P

theorem tc2a_layI (x : Fin 1 × TTree.Path) (hx : x.2 ∈ (LGi.garden.tree x.1).nodes) :
    layerAt LGi x = layerAt LG ((0 : Fin 2), m.c :: x.2) :=
  ((layerAt_node LGi (⟨x, hx⟩ : GNode LGi.garden.tree)).trans (P.layI _)).trans
    (tc2a_layZ D _ (P.hp.ιi ⟨x, hx⟩).2)

theorem tc2a_layR (x : Fin 2 × TTree.Path) (hx : x.2 ∈ (LGr.garden.tree x.1).nodes) :
    layerAt LGr x = layerAt LG ((0 : Fin 2), rBase m inner (LGZ.garden.sig 0) x.1 ++ x.2) :=
  ((layerAt_node LGr (⟨x, hx⟩ : GNode LGr.garden.tree)).trans (P.layR _)).trans
    (tc2a_layZ D _ (P.hp.ιr ⟨x, hx⟩).2)

theorem tc2a_layG (x : Fin 2 × TTree.Path) (hx : x.2 ∈ (LGg.garden.tree x.1).nodes) :
    layerAt LGg x = layerAt LG ((0 : Fin 2), gBase m inner (LGZ.garden.sig 0) x.1 ++ x.2) :=
  ((layerAt_node LGg (⟨x, hx⟩ : GNode LGg.garden.tree)).trans (P.layG _)).trans
    (tc2a_layZ D _ (P.hp.ιg ⟨x, hx⟩).2)

/-- **The incoherency index splits** over the rest couple, the interior, the side couples and the root link. -/
theorem tc2a_incoh {rest Xm : RegChain} {Qlp : RegCpl}
    (hdec : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).Decodes LG.garden)
    (hdB : (SourceApp.closeCouple rest Xm Qlp).Decodes LGB.garden) (hsZ : LGZ.garden.sig 0 = 1) :
    LG.incoherency (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).links =
      LGB.incoherency (SourceApp.closeCouple rest Xm Qlp).links +
        LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links + LGg.incoherency Qg.links +
        (if layerAt LG ((0 : Fin 2), []) = layerAt LG ((0 : Fin 2), bPath m inner) then 0 else 1) := by
  classical
  set ζ := LGZ.garden.sig 0 with hζ
  set lp := (cpair m Qr Qg inner).lonePath with hlp
  set Pr : (Fin 2 × TTree.Path) × (Fin 2 × TTree.Path) → Bool := fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2)
    with hPr
  rw [incoherency_eq_count hdec, incoherency_eq_count hdB, tree_incoherency_eq_count P.decI,
    incoherency_eq_count P.decR, incoherency_eq_count P.decG]
  -- the rest couple
  have hB : ((SourceApp.closeCouple rest Xm Qlp).linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) lp)
        ((1 : Fin 2), ([] : TTree.Path))).filter Pr =
      (((SourceApp.closeCouple rest Xm Qlp).links).filter (fun l => layerAt LGB l.1 ≠ layerAt LGB l.2)).map
        (fun l => (botAddr lp l.1, botAddr lp l.2)) := by
    have e0 : addrExt ((0 : Fin 2), ([] : TTree.Path)) lp = botAddr lp ((0 : Fin 2), []) := by
      simp [botAddr, addrExt]
    have e1 : ((1 : Fin 2), ([] : TTree.Path)) = botAddr lp ((1 : Fin 2), []) := by simp [botAddr]
    rw [e0, e1, couple_linksAt_map _ (botAddr lp) (botAddr_hom lp), RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching hdB hl
    simp only [Function.comp_apply, Pr]
    rw [tc2a_layB D l.1 (TTree.branching_subset_nodes _ hb.1), tc2a_layB D l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  -- the interior
  let fi : Fin 1 × TTree.Path → Fin 2 × TTree.Path := fun x => ((0 : Fin 2), m.c :: x.2)
  have hfi : ∀ x q, fi (addrExt x q) = addrExt (fi x) q := by intro x q; simp [fi, addrExt]
  have hI : (inner.linksAt (slotSign ζ m.c) (addrExt ((0 : Fin 2), ([] : TTree.Path)) [m.c])).filter Pr =
      ((inner.treeLinks (LGi.garden.sig 0)).filter (fun l => layerAt LGi l.1 ≠ layerAt LGi l.2)).map
        (fun l => (fi l.1, fi l.2)) := by
    have e0 : addrExt ((0 : Fin 2), ([] : TTree.Path)) [m.c] = fi ((0 : Fin 1), []) := by simp [fi, addrExt]
    rw [e0, ← P.sigI, chain_linksAt_map inner fi hfi, RegChain.treeLinks, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have h1 := (tree_mem_pairEndpoints_links_iff P.decI l.1).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks]; exact hl, Or.inl rfl⟩)
    have h2 := (tree_mem_pairEndpoints_links_iff P.decI l.2).1
      ((mem_pairEndpoints_iff _ _).2 ⟨l, by rw [RegChain.treeLinks]; exact hl, Or.inr rfl⟩)
    simp only [Function.comp_apply, Pr]
    rw [tc2a_layI D P l.1 (TTree.branching_subset_nodes _ h1), tc2a_layI D P l.2 (TTree.branching_subset_nodes _ h2)]
  -- the side couples
  let fr : Fin 2 × TTree.Path → Fin 2 × TTree.Path := fun x => ((0 : Fin 2), rBase m inner ζ x.1 ++ x.2)
  have hfr : ∀ x q, fr (addrExt x q) = addrExt (fr x) q := by intro x q; simp [fr, addrExt]
  have hR : (Qr.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 0))
        (addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 1))).filter Pr =
      ((Qr.links).filter (fun l => layerAt LGr l.1 ≠ layerAt LGr l.2)).map (fun l => (fr l.1, fr l.2)) := by
    have e0 : addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 0) = fr (0, []) := by simp [fr, addrExt]
    have e1 : addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 1) = fr (1, []) := by simp [fr, addrExt]
    rw [e0, e1, couple_linksAt_map Qr fr hfr, RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching P.decR hl
    simp only [Function.comp_apply, Pr]
    rw [tc2a_layR D P l.1 (TTree.branching_subset_nodes _ hb.1),
      tc2a_layR D P l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  let fg : Fin 2 × TTree.Path → Fin 2 × TTree.Path := fun x => ((0 : Fin 2), gBase m inner ζ x.1 ++ x.2)
  have hfg : ∀ x q, fg (addrExt x q) = addrExt (fg x) q := by intro x q; simp [fg, addrExt]
  have hG : (Qg.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 0))
        (addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 1))).filter Pr =
      ((Qg.links).filter (fun l => layerAt LGg l.1 ≠ layerAt LGg l.2)).map (fun l => (fg l.1, fg l.2)) := by
    have e0 : addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 0) = fg (0, []) := by simp [fg, addrExt]
    have e1 : addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 1) = fg (1, []) := by simp [fg, addrExt]
    rw [e0, e1, couple_linksAt_map Qg fg hfg, RegCpl.links, List.filter_map]
    congr 1
    refine List.filter_congr fun l hl => ?_
    have hb := link_branching P.decG hl
    simp only [Function.comp_apply, Pr]
    rw [tc2a_layG D P l.1 (TTree.branching_subset_nodes _ hb.1),
      tc2a_layG D P l.2 (TTree.branching_subset_nodes _ hb.2.1)]
  -- the links of the couple
  have hL : (RegCpl.type2 (.pair m Qr Qg inner rest) Xm Qlp).links =
      ((((0 : Fin 2), []), addrExt ((0 : Fin 2), ([] : TTree.Path)) ([m.c] ++ inner.lonePath)) ::
        (Qr.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 0))
            (addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 1)) ++
          Qg.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 0))
            (addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 1)) ++
          inner.linksAt (slotSign ζ m.c) (addrExt ((0 : Fin 2), ([] : TTree.Path)) [m.c]) ++ [])) ++
        (SourceApp.closeCouple rest Xm Qlp).linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) lp)
          ((1 : Fin 2), []) := by
    rw [tc2a_closeCouple_linksAt, addrExt_append, hlp]
    unfold RegCpl.links
    rw [show RegChain.pair m Qr Qg inner rest = appendChain (cpair m Qr Qg inner) rest from rfl]
    simp only [RegCpl.linksAt, appendChain_linksAt, appendChain_lonePath]
    simp only [hsZ]
    simp only [cpair, RegChain.linksAt]
    rw [tc2a_oriented_r, tc2a_oriented_g]
    simp [addrExt]
  rw [hL]
  simp only [List.filter_append, List.filter_cons, List.length_append, List.filter_nil, List.length_nil,
    add_zero]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (inner.linksAt (slotSign ζ m.c) (addrExt ((0 : Fin 2), ([] : TTree.Path)) [m.c])) =
      (inner.linksAt (slotSign ζ m.c) (addrExt ((0 : Fin 2), ([] : TTree.Path)) [m.c])).filter Pr from rfl, hI]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (Qr.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 0))
        (addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 1))) =
      (Qr.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 0))
        (addrExt ((0 : Fin 2), ([] : TTree.Path)) (rBase m inner ζ 1))).filter Pr from rfl, hR]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      (Qg.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 0))
        (addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 1))) =
      (Qg.linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 0))
        (addrExt ((0 : Fin 2), ([] : TTree.Path)) (gBase m inner ζ 1))).filter Pr from rfl, hG]
  rw [show List.filter (fun l => decide (layerAt LG l.1 ≠ layerAt LG l.2))
      ((SourceApp.closeCouple rest Xm Qlp).linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) lp)
        ((1 : Fin 2), [])) =
      ((SourceApp.closeCouple rest Xm Qlp).linksAt (addrExt ((0 : Fin 2), ([] : TTree.Path)) lp)
        ((1 : Fin 2), [])).filter Pr from rfl, hB]
  try simp only [List.length_map]
  have eb : addrExt ((0 : Fin 2), ([] : TTree.Path)) ([m.c] ++ inner.lonePath) = ((0 : Fin 2), bPath m inner) := by
    simp [addrExt, bPath]
  split_ifs with h1 h2 h2 <;>
    simp only [List.length_cons, List.length_append, List.length_map, List.length_nil] <;>
    simp_all [addrExt, bPath] <;> omega

end Data

end WaveTurbulence.Flower.ProtPin
