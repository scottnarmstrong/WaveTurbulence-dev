/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.GardenPairingTransport

/-! # Sign transport in the switched lower crown

TARGET twistexplain (b): all branching nodes except the lower root retain
their signs; the retained leaf and its paired outside leaf both flip.
-/

public section
namespace WaveTurbulence.Twist
open TTree Finset

/-- Signs factor over concatenated actual addresses. -/
theorem pathSign_append (ζ : ℤˣ) (p q : Path) :
    pathSign ζ (p ++ q) = pathSign (pathSign ζ p) q := by
  simp [pathSign,List.count_append,pow_add,mul_assoc]

/-- A retained child subtree equal to a leaf has no deeper leaf addresses. -/
theorem retained_leaf_tail {t : TTree} {keep : Fin 3}
    (hk : Comb.subtree t [keep] = some .leaf) {p : Path} (hp : keep::p ∈ t.leaves) : p = [] := by
  have hm : p ∈ TTree.leaf.leaves := (Comb.subtree_leaves_iff hk p).mpr hp
  exact mem_singleton.mp hm

/-- Only the retained leaf changes sign among transported leaves of the lower crown. -/
theorem switched_leaf_sign {t : TTree} {keep : Fin 3} (hkeep : keep ≠ 1)
    (hroot : [] ∉ t.leaves) (hk : Comb.subtree t [keep] = some .leaf)
    (ζ : ℤˣ) {p : Path} (hp : p ∈ t.leaves) :
    pathSign (-ζ) (switchPath keep p) =
      if p = [keep] then -pathSign ζ p else pathSign ζ p := by
  cases p with
  | nil => exact (hroot hp).elim
  | cons i p =>
    have hs := switchPath_sign keep i hkeep ζ p
    by_cases hi : i = keep
    · subst i
      have he := retained_leaf_tail hk hp
      subst p
      simpa only [ite_true] using hs
    · have he : i::p ≠ [keep] := fun he => hi (List.cons.inj he).1
      simpa only [hi,he,ite_false] using hs

/-- Only the lower root changes sign among transported branching nodes of the lower crown. -/
theorem switched_branch_sign {t : TTree} {keep : Fin 3} (hkeep : keep ≠ 1)
    (hk : Comb.subtree t [keep] = some .leaf) (ζ : ℤˣ) {p : Path} (hp : p ∈ t.branching) :
    pathSign (-ζ) (switchPath keep p) =
      if p = [] then -pathSign ζ p else pathSign ζ p := by
  cases p with
  | nil => simp [switchPath,pathSign]
  | cons i p =>
    have hi : i ≠ keep := by
      intro he
      subst i
      have hm : p ∈ TTree.leaf.branching := (Comb.subtree_branching_iff hk p).mpr hp
      exact notMem_empty p hm
    simpa only [hi,ite_false,List.cons_ne_nil] using switchPath_sign keep i hkeep ζ p

end WaveTurbulence.Twist
