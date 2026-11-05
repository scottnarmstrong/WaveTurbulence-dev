/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.ExceptionalCounts
public import WaveTurbulence.Foundations.Molecule.LFTwist.TruncationScale

/-! # Full per-tree counts and truncation for a literal unit LF construction -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed

private theorem sum_two_exception {α β : Type*} [Fintype α] [Fintype β]
    (f f' : α → ℕ) (g g' : β → ℕ) (a : α) (b : β)
    (hf : ∀ x, x ≠ a → f x = f' x) (hg : ∀ y, y ≠ b → g y = g' y)
    (he : f a + g b = f' a + g' b) : (∑ x, f x) + ∑ y, g y = (∑ x, f' x) + ∑ y, g' y := by
  classical
  have hfe : ∑ x ∈ Finset.univ.erase a, f x = ∑ x ∈ Finset.univ.erase a, f' x := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hf x (Finset.mem_erase.mp hx).1
  have hge : ∑ y ∈ Finset.univ.erase b, g y = ∑ y ∈ Finset.univ.erase b, g' y := by
    apply Finset.sum_congr rfl
    intro y hy
    exact hg y (Finset.mem_erase.mp hy).1
  have h1 := Finset.sum_erase_add Finset.univ f (Finset.mem_univ a)
  have h2 := Finset.sum_erase_add Finset.univ f' (Finset.mem_univ a)
  have h3 := Finset.sum_erase_add Finset.univ g (Finset.mem_univ b)
  have h4 := Finset.sum_erase_add Finset.univ g' (Finset.mem_univ b)
  omega

namespace LFConstruction
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
    (h : LFConstruction s ε)

/-- TARGET lftwistprop: each original tree retains its complete layer-p count.
Only unchanged ordinary native layerings and the combined exceptional count
are used; global count preservation is not a construction premise. -/
theorem topOrder (j : Fin w) : h.output.topOrder p j = LG.topOrder p j := by
  rw [raw_topOrder_split h.output h.data (s.chosen_plain ε) h.decodes p j,
    raw_topOrder_split LG s.data s.plain s.decodes p j,h.coreTopCount_eq j]
  have hC := (s.pairs ε).sum_comp (fun q => rawCoupleTopCount h.output h.data (s.chosen_plain ε) p q j)
  have hT := (s.branches ε).sum_comp (fun b => rawTreeTopCount h.output h.data (s.chosen_plain ε) p b j)
  rw [← hC,← hT]
  have he := sum_two_exception
    (fun q => rawCoupleTopCount LG s.data s.plain p q j)
    (fun q => rawCoupleTopCount h.output h.data (s.chosen_plain ε) p (s.pairs ε q) j)
    (fun b => rawTreeTopCount LG s.data s.plain p b j)
    (fun b => rawTreeTopCount h.output h.data (s.chosen_plain ε) p (s.branches ε b) j)
    s.exceptional s.placement.lower
    (fun q hq => h.ordinary_coupleTopCount_eq q hq j)
    (fun b hb => h.ordinary_treeTopCount_eq b hb j)
    (by have hh := h.exceptional_topCounts_eq j; omega)
  omega

/-- The source total-order bound makes attached-component truncation redundant;
full truncation is therefore preserved by the literal unit LF construction. -/
theorem isTrunc (Ntop Natt : ℕ) (hn : LG.garden.order ≤ Natt) :
    h.output.IsTrunc p Ntop Natt ↔ LG.IsTrunc p Ntop Natt := by
  rw [trunc_iff_topOrder _ _ _ _ (h.order.trans_le hn),trunc_iff_topOrder _ _ _ _ hn]
  simp only [h.topOrder]

end LFConstruction
end WaveTurbulence.LFTwist
