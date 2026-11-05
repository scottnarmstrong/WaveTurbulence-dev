/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceChainAddress

/-! # The original sign-selected child placements in a consecutive mini-tree pair -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree

/-- The literal positive/negative roots of the red child couple. -/
def miniRedRoots {w : ℕ} (m : MiniTreeCode) (ζ : ℤˣ) (a : Fin w × Path) :
    (Fin w × Path) × (Fin w × Path) :=
  if slotSign ζ m.red.1 = 1 then
    (addrExt a [m.red.1],addrExt a [m.c,m.red.2])
  else (addrExt a [m.c,m.red.2],addrExt a [m.red.1])

/-- The literal positive/negative roots of the green child couple. -/
def miniGreenRoots {w : ℕ} (m : MiniTreeCode) (ζ : ℤˣ) (a : Fin w × Path) :
    (Fin w × Path) × (Fin w × Path) :=
  if slotSign ζ m.green.1 = 1 then
    (addrExt a [m.green.1],addrExt a [m.c,m.green.2])
  else (addrExt a [m.c,m.green.2],addrExt a [m.green.1])

theorem miniRedRoots_indep {w : ℕ} (m : MiniTreeCode) (ζ : ℤˣ) (a : Fin w × Path) :
    Indep (miniRedRoots m ζ a).1 (miniRedRoots m ζ a).2 := by
  unfold miniRedRoots
  split_ifs
  · simpa only [List.append_nil,List.cons_append,List.nil_append] using indep_red m [] a
  · simpa only [List.append_nil,List.cons_append,List.nil_append] using (indep_red m [] a).symm

theorem miniGreenRoots_indep {w : ℕ} (m : MiniTreeCode) (ζ : ℤˣ) (a : Fin w × Path) :
    Indep (miniGreenRoots m ζ a).1 (miniGreenRoots m ζ a).2 := by
  unfold miniGreenRoots
  split_ifs
  · simpa only [List.append_nil,List.cons_append,List.nil_append] using indep_green m [] a
  · simpa only [List.append_nil,List.cons_append,List.nil_append] using (indep_green m [] a).symm

/-- The original links retain exactly the selected red/green placements. -/
theorem chain_linksAt_pair_nil_roots {w : ℕ} (m : MiniTreeCode) (Qr Qg : RegCpl)
    (rest : RegChain) (ζ : ℤˣ) (a : Fin w × Path) :
    (RegChain.pair m Qr Qg .nil rest).linksAt ζ a =
    (a,addrExt a [m.c]) ::
      (Qr.linksAt (miniRedRoots m ζ a).1 (miniRedRoots m ζ a).2 ++
       Qg.linksAt (miniGreenRoots m ζ a).1 (miniGreenRoots m ζ a).2 ++
       rest.linksAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a [m.c,m.lone])) := by
  simp only [RegChain.linksAt,RegChain.lonePath,List.append_nil,List.cons_append,
    List.nil_append,miniRedRoots,miniGreenRoots]
  split_ifs <;> rfl

/-- The literal paired leaf factors use these same original placements. -/
theorem chainLeafProduct_pair_nil_roots {d w : ℕ} (F : Mom d → ℂ)
    (θ : Fin w × Path → Mom d × Mom d) (m : MiniTreeCode) (Qr Qg : RegCpl)
    (rest : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (r : Mom d)
    (cont : Fin w × Path → Mom d) :
    chainLeafProduct F θ (.pair m Qr Qg .nil rest) ζ a r cont =
    cplLeafProduct F θ Qr (miniRedRoots m ζ a).1 (miniRedRoots m ζ a).2 (childVals r (θ a) m.red.1) *
    cplLeafProduct F θ Qg (miniGreenRoots m ζ a).1 (miniGreenRoots m ζ a).2 (childVals r (θ a) m.green.1) *
    chainLeafProduct F θ rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a [m.c,m.lone]) r cont := by
  rw [chainLeafProduct_pair_nil]
  simp only [RegChain.lonePath,List.append_nil,List.cons_append,List.nil_append,
    miniRedRoots,miniGreenRoots]
  split_ifs <;> rfl

end WaveTurbulence.RegAsymp
