/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeSpineEndpoints
public import WaveTurbulence.Foundations.IncohInst.TreeLinkCoordinates
public import WaveTurbulence.Foundations.Incoh.SelectedClocksOfLinks

/-! # Source link indices containing the root and the lone parent -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links TTree Reg

/-- Select the actual enumerated link containing a proved source spine pair. -/
@[expose] def spineLinkIndex {G : Garden 1} {X : RegChain}
    (_hX : X.DecodesTree G) (l : (Fin 1 × Path) × (Fin 1 × Path))
    (hl : l ∈ spineLinks X (0, [])) : Fin (X.treeLinks (G.sig 0)).length :=
  Classical.choose (List.get_of_mem (show l ∈ X.treeLinks (G.sig 0) from
    spineLinks_sub X (G.sig 0) (0, []) l hl))

theorem get_spineLinkIndex {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (l : (Fin 1 × Path) × (Fin 1 × Path))
    (hl : l ∈ spineLinks X (0, [])) :
    (X.treeLinks (G.sig 0)).get (spineLinkIndex hX l hl) = l :=
  Classical.choose_spec (List.get_of_mem (show l ∈ X.treeLinks (G.sig 0) from
    spineLinks_sub X (G.sig 0) (0, []) l hl))

/-- The first top-level spine link contains the actual root. -/
@[expose] def firstSpineLink {w : ℕ} (m : MiniTreeCode) (inner : RegChain)
    (a : Fin w × Path) : (Fin w × Path) × (Fin w × Path) :=
  (a, addrExt a ([m.c] ++ inner.lonePath))

theorem firstSpineLink_mem {w : ℕ} (m : MiniTreeCode) (Qr Qg : RegCpl)
    (inner rest : RegChain) (a : Fin w × Path) :
    firstSpineLink m inner a ∈ spineLinks (.pair m Qr Qg inner rest) a :=
  List.mem_cons_self

/-- The selected index reads the exact two source addresses. -/
theorem treeLinkBranch_spineLinkIndex {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (l : (Fin 1 × Path) × (Fin 1 × Path))
    (hl : l ∈ spineLinks X (0, [])) (b : Fin 2) :
    (treeLinkBranch hX (spineLinkIndex hX l hl) b).val = if b = 0 then l.1 else l.2 := by
  fin_cases b
  · change ((X.treeLinks (G.sig 0)).get (spineLinkIndex hX l hl)).1 = l.1
    exact congrArg Prod.fst (get_spineLinkIndex hX l hl)
  · change ((X.treeLinks (G.sig 0)).get (spineLinkIndex hX l hl)).2 = l.2
    exact congrArg Prod.snd (get_spineLinkIndex hX l hl)

/-- Any successive source spine pair has a parentward-to-childward strict path order. -/
theorem lastSpine_after_firstPartner {w : ℕ} (m : MiniTreeCode) (inner rest : RegChain)
    (a : Fin w × Path) {l : (Fin w × Path) × (Fin w × Path)}
    (h : lastSpineLink rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) = some l) :
    Under (addrExt a ([m.c] ++ inner.lonePath)) l.1 ∧
      (addrExt a ([m.c] ++ inner.lonePath)).2.length < l.1.2.length := by
  have hu := (spineLink_under rest _ (lastSpineLink_mem rest _ h)).1
  constructor
  · apply under_trans _ hu
    simpa only [addrExt_append, List.append_assoc] using
      under_ext (addrExt a ([m.c] ++ inner.lonePath)) [m.lone]
  · have hh := under_length hu
    dsimp only [addrExt] at hh ⊢
    simp only [List.length_append, List.length_singleton] at hh ⊢
    omega

end WaveTurbulence.IncohInst
