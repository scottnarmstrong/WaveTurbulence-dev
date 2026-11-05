/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.SourceMiniShapes

/-! # The exact four side leaves of a source B mini context -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem addrExt_path_injective {w : ℕ} (a : Address w) : Function.Injective (addrExt a) := by
  intro p q he
  have hp := congrArg (fun z : Address w => z.2) he
  change a.2 ++ p = a.2 ++ q at hp
  exact List.append_cancel_left hp

/-- The two pinned mini pairs have exactly their four literal endpoints at every root sign. -/
theorem miniChain_pair_endpoints {w : ℕ} (m : MiniTreeCode) (ζ : ℤˣ) (a : Address w) :
    pairEndpoints ((miniChain m).pairsAt ζ a) =
      {addrExt a [m.red.1],addrExt a [m.c,m.red.2],addrExt a [m.green.1],addrExt a [m.c,m.green.2]} := by
  ext z
  by_cases hr : slotSign ζ m.red.1 = 1 <;> by_cases hg : slotSign ζ m.green.1 = 1 <;>
    simp [miniChain,RegChain.pairsAt,RegChain.lonePath,RegCpl.pairsAt,hr,hg,
      pairEndpoints,or_assoc,or_left_comm,or_comm]

/-- A mini-context leaf outside its lone subtree is one of the actual four side slots. -/
theorem miniContext_side_leaf (m : MiniTreeCode) (S : TTree) (p : Path)
    (hp : p ∈ (miniTreeContext m S).leaves) (hn : ¬ [m.c,m.lone] <+: p) :
    p = [m.red.1] ∨ p = [m.c,m.red.2] ∨ p = [m.green.1] ∨ p = [m.c,m.green.2] := by
  let a : Address 1 := (0,[])
  have he := chain_leafAddresses (miniChain m) (1 : ℤˣ) S a
  rw [miniChain_plug,miniChain_lonePath,miniChain_pair_endpoints] at he
  have hm : addrExt a p ∈ leafAddresses (miniTreeContext m S) a := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  rw [he] at hm
  rcases Finset.mem_union.mp hm with hs | hh
  · simp only [Finset.mem_insert,Finset.mem_singleton] at hs
    rcases hs with h | h | h | h
    · exact Or.inl (addrExt_path_injective a h)
    · exact Or.inr (Or.inl (addrExt_path_injective a h))
    · exact Or.inr (Or.inr (Or.inl (addrExt_path_injective a h)))
    · exact Or.inr (Or.inr (Or.inr (addrExt_path_injective a h)))
  · obtain ⟨r,hr,hx⟩ := Finset.mem_image.mp hh
    have hx' : addrExt a ([m.c,m.lone]++r) = addrExt a p := (addrExt_append a [m.c,m.lone] r).symm.trans hx
    have hpath := addrExt_path_injective a hx'
    exact (hn (hpath ▸ List.prefix_append [m.c,m.lone] r)).elim

/-- No side slot lies in the mini's lone-subtree region. -/
theorem mini_side_not_below (m : MiniTreeCode) :
    ¬ [m.c,m.lone] <+: [m.red.1] ∧ ¬ [m.c,m.lone] <+: [m.c,m.red.2] ∧
    ¬ [m.c,m.lone] <+: [m.green.1] ∧ ¬ [m.c,m.lone] <+: [m.c,m.green.2] := by
  obtain ⟨c,b⟩ := m
  fin_cases c <;> fin_cases b <;> decide

/-- Containment of two framed addresses is exactly containment of their relative paths. -/
theorem below_frames_iff {w : ℕ} (a : Address w) (p q : Path) :
    Below (addrExt a p) (addrExt a q) ↔ p <+: q := by
  change (a.1 = a.1 ∧ a.2 ++ p <+: a.2 ++ q) ↔ p <+: q
  simp only [true_and,List.prefix_append_right_inj]

end WaveTurbulence.Reg.Skeleton
