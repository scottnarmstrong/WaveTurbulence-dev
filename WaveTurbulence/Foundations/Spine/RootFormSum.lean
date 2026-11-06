/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.DecoratedWeightExpansion
public import WaveTurbulence.Foundations.Spine.InputLeafCount
/-! AMEND6' (design P*, identity (M)): the signed root momentum is the signed sum over the POSITIVE input
leaves of their (shared) leaf momenta, each counted `[a in T_{j0}] - [partner(a) in T_{j0}]` times: pairs inside
one tree cancel (TARGET L2293, research-twistprof Q1 (c)). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

theorem root_sum_inputs {w d : ℕ} (G : Garden w) (hp : G.IsPlain) (k : GNode G.tree → Mom d)
    (hk : IsDecoration G k) (j0 : Fin w) :
    ((nodeSign G.sig (GNode.root G.tree j0).1 : ℤˣ) : ℤ) • k (GNode.root G.tree j0) =
      ∑ a ∈ inputLeaves G, ((if a.1.1 = j0 then (1 : ℤ) else 0) -
        (if (G.pair a).1.1 = j0 then (1 : ℤ) else 0)) • k a.toNode := by
  classical
  rw [sum_rule G.sig k hk.1 (GNode.root G.tree j0)]
  have hbelow : (GNode.root G.tree j0).leavesBelow =
      (univ : Finset (GLeaf G.tree)).filter fun ℓ => ℓ.1.1 = j0 := by
    ext ℓ
    constructor
    · intro h
      exact mem_filter.mpr ⟨mem_univ _, ((mem_filter.mp h).2).1.symm⟩
    · intro h
      have h' : ℓ.1.1 = j0 := (mem_filter.mp h).2
      exact mem_filter.mpr ⟨mem_univ _, h'.symm, List.nil_prefix⟩
  rw [hbelow, sum_filter]
  have hflip (l : GLeaf G.tree) : G.sign (G.pair l).toNode = -G.sign l.toNode :=
    G.pair_sign l (fun he => ((G.pair_eq_iff l).mp he) (hp l))
  set F : GLeaf G.tree → Mom d := fun ℓ =>
    if ℓ.1.1 = j0 then ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • k ℓ.toNode else 0 with hF
  have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (GLeaf G.tree))
    (fun l => G.sign l.toNode = 1) F
  have hinput : inputLeaves G = (univ : Finset (GLeaf G.tree)).filter fun l => G.sign l.toNode = 1 := by
    ext l
    simp only [inputLeaves, mem_filter, mem_univ, true_and, hp l, and_true]
  have hneg : ∑ l ∈ (univ : Finset (GLeaf G.tree)).filter (fun l => ¬ G.sign l.toNode = 1), F l =
      ∑ a ∈ inputLeaves G, F (G.pair a) := by
    rw [hinput]
    symm
    refine Finset.sum_nbij' (fun l => G.pair l) (fun l => G.pair l) ?_ ?_ ?_ ?_ ?_
    · intro l hl
      have hl' : G.sign l.toNode = 1 := (mem_filter.mp hl).2
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [hflip, hl']; decide
    · intro l hl
      have hl' : ¬ G.sign l.toNode = 1 := (mem_filter.mp hl).2
      have hl'' : G.sign l.toNode = -1 := (Int.units_eq_one_or _).resolve_left hl'
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      rw [hflip, hl'', neg_neg]
    · intro l _; exact G.pair_pair l
    · intro l _; exact G.pair_pair l
    · intro l _; rfl
  rw [← hsplit, hneg, hinput]
  rw [← Finset.sum_add_distrib]
  refine sum_congr rfl fun a ha => ?_
  have ha1 : G.sign a.toNode = 1 := (mem_filter.mp ha).2
  have hk2 := hk.2 a
  have hs1 : ((nodeSign G.sig a.1 : ℤˣ) : ℤ) = 1 := by
    have : nodeSign G.sig a.1 = 1 := ha1
    rw [this]; rfl
  have hs2 : ((nodeSign G.sig (G.pair a).1 : ℤˣ) : ℤ) = -1 := by
    have : nodeSign G.sig (G.pair a).1 = -1 := by
      have h := hflip a
      change nodeSign G.sig (G.pair a).1 = -nodeSign G.sig a.1 at h
      rw [h, show nodeSign G.sig a.1 = 1 from ha1]
    rw [this]; rfl
  simp only [hF, hs1, hs2, ← hk2]
  by_cases h1 : a.1.1 = j0 <;> by_cases h2 : (G.pair a).1.1 = j0 <;> simp [h1, h2, sub_smul]

end WaveTurbulence.LGSpine
