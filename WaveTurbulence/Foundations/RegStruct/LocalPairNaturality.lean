/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.PairNaturality

/-! # Local address transport for internal mini-tree insertion

A relocation need only respect path extension below the represented roots.
No global compatibility is required across an ancestor of the insertion node.
-/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Compatibility of an address map with every path below one specified root. -/
def RespectsAt {w v : ℕ} (f : (Fin w × Path) → (Fin v × Path)) (a : Fin w × Path) : Prop :=
  ∀ p, f (addrExt a p) = addrExt (f a) p

/-- Compatibility below a root passes to every descendant root. -/
theorem RespectsAt.child {w v : ℕ} {f : (Fin w × Path) → (Fin v × Path)} {a : Fin w × Path}
    (h : RespectsAt f a) (p : Path) : RespectsAt f (addrExt a p) := by
  intro q
  rw [addrExt_append,h,h,addrExt_append]

mutual
/-- Couple pair decoding commutes with address transport local to its two roots. -/
theorem couple_pairsAt_map_local {w v : ℕ} (Q : RegCpl)
    (f : (Fin w × Path) → (Fin v × Path)) (a b : Fin w × Path)
    (ha : RespectsAt f a) (hb : RespectsAt f b) :
    Q.pairsAt (f a) (f b) = (Q.pairsAt a b).map (fun p => (f p.1,f p.2)) := by
  have hA : ∀ p, f (addrExt a p) = addrExt (f a) p := ha
  have hB : ∀ p, f (addrExt b p) = addrExt (f b) p := hb
  cases Q with
  | triv => rfl
  | type1 c r g d =>
    have hr := couple_pairsAt_map_local r f _ _ (ha.child [0]) (hb.child [c.partner 0])
    have hg := couple_pairsAt_map_local g f _ _ (hb.child [1]) (ha.child [1])
    have hd := couple_pairsAt_map_local d f _ _ (ha.child [2]) (hb.child [c.partner 2])
    simp only [RegCpl.pairsAt,List.map_append,← hA,← hB,hr,hg,hd]
  | type2 p m q =>
    have hp := chain_pairsAt_map_local p f a ha 1
    have hm := chain_pairsAt_map_local m f b hb (-1)
    have hq := couple_pairsAt_map_local q f _ _ (ha.child p.lonePath) (hb.child m.lonePath)
    simp only [RegCpl.pairsAt,List.map_append,← hA,← hB,hp,hm,hq]
termination_by structural Q

/-- Chain pair decoding needs address compatibility only below its original root. -/
theorem chain_pairsAt_map_local {w v : ℕ} (X : RegChain)
    (f : (Fin w × Path) → (Fin v × Path)) (a : Fin w × Path)
    (ha : RespectsAt f a) (ζ : ℤˣ) :
    X.pairsAt ζ (f a) = (X.pairsAt ζ a).map (fun p => (f p.1,f p.2)) := by
  have hA : ∀ p, f (addrExt a p) = addrExt (f a) p := ha
  cases X with
  | nil => rfl
  | pair m r g i s =>
    have hR : ∀ p q, r.pairsAt (f (addrExt a p)) (f (addrExt a q)) =
        (r.pairsAt (addrExt a p) (addrExt a q)).map (fun p => (f p.1,f p.2)) :=
      fun p q => couple_pairsAt_map_local r f _ _ (ha.child p) (ha.child q)
    have hG : ∀ p q, g.pairsAt (f (addrExt a p)) (f (addrExt a q)) =
        (g.pairsAt (addrExt a p) (addrExt a q)).map (fun p => (f p.1,f p.2)) :=
      fun p q => couple_pairsAt_map_local g f _ _ (ha.child p) (ha.child q)
    have hI := chain_pairsAt_map_local i f _ (ha.child [m.c]) (slotSign ζ m.c)
    have hS := chain_pairsAt_map_local s f _
      (ha.child ([m.c] ++ i.lonePath ++ [m.lone])) (slotSign (slotSign ζ m.c) m.lone)
    by_cases hr : slotSign ζ m.red.1 = 1 <;>
      by_cases hg : slotSign ζ m.green.1 = 1 <;>
      simp only [RegChain.pairsAt,hr,hg,ite_true,ite_false,List.map_append,← hA,hR,hG,hI,hS]
termination_by structural X
end

end WaveTurbulence.Reg
