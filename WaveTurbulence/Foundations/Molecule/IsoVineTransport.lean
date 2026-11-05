/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.IsoBlockTransport

/-! # Exact expanded-template vines under actual directed-garden isomorphisms

No template or connectedness clause is weakened. Bond multiplicities are
transported as multisets through the actual dart equivalence.
-/

public section
namespace WaveTurbulence.Twist
open TTree Finset
variable {w : ℕ} (G H : Garden w) (f : GardenDirectedIso G H)

/-- Actual bond endpoints commute with the branching-node bijection. -/
theorem iso_ends (x : GardenDart G) : H.molecule.ends (f.darts x) = Sym2.map f.branches (G.molecule.ends x) := by
  change s(H.molecule.atom (f.darts x),H.molecule.atom (H.molecule.mate (f.darts x))) =
    s(f.branches (G.molecule.atom x),f.branches (G.molecule.atom (G.molecule.mate x)))
  rw [f.atom_comm,f.mate_comm,f.atom_comm]

/-- The exact internal undirected bond multiset is transported, including all parallel bonds. -/
theorem iso_groupBonds (S : Finset (GBranch G.tree)) :
    H.molecule.groupBonds (isoAtoms G H f S) = (G.molecule.groupBonds S).map (Sym2.map f.branches) := by
  have hset : (univ.filter fun x => H.molecule.out x = true ∧ H.molecule.InGroup (isoAtoms G H f S) x) =
      (univ.filter fun x => G.molecule.out x = true ∧ G.molecule.InGroup S x).image f.darts := by
    ext y
    obtain ⟨x,rfl⟩ := f.darts.surjective y
    constructor
    · intro h
      obtain ⟨_hu,ho,hg⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨x,mem_filter.mpr ⟨mem_univ _,f.out_comm x ▸ ho,
        (inGroup_isoAtoms G H f S x).mp hg⟩,rfl⟩
    · intro h
      obtain ⟨z,hz,he⟩ := mem_image.mp h
      have hzx := f.darts.injective he
      subst z
      obtain ⟨_hu,ho,hg⟩ := mem_filter.mp hz
      exact mem_filter.mpr ⟨mem_univ _,(f.out_comm x).symm ▸ ho,(inGroup_isoAtoms G H f S x).mpr hg⟩
  unfold Molecule.groupBonds
  rw [hset,image_val_of_injOn f.darts.injective.injOn,Multiset.map_map,Multiset.map_map]
  apply Multiset.map_congr rfl
  intro x _hx
  exact iso_ends G H f x

/-- The literal current B2 vine predicate, with its full expanded-template multiset, is preserved. -/
theorem iso_isVine {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hV : G.molecule.IsVine X S a b) :
    H.molecule.IsVine X (isoAtoms G H f S) (f.branches a) (f.branches b) := by
  obtain ⟨hB,k,hk,g,hg,himage,hj,hbonds⟩ := hV
  refine ⟨iso_isBlock G H f hB,k,hk,g ∘ f.branches.symm,?_,?_,?_,?_⟩
  · intro u hu v hv he
    obtain ⟨u,rfl⟩ := f.branches.surjective u
    obtain ⟨v,rfl⟩ := f.branches.surjective v
    have he' : g u = g v := by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using he
    exact congrArg f.branches (hg ((mem_isoAtoms G H f S u).mp hu) ((mem_isoAtoms G H f S v).mp hv) he')
  · change (S.image f.branches).image (g ∘ f.branches.symm) = _
    rw [Finset.image_image]
    simpa only [Function.comp_def,Equiv.symm_apply_apply] using himage
  · simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hj
  · rw [iso_groupBonds,Multiset.map_map]
    have he : (Sym2.map (g ∘ f.branches.symm)) ∘ Sym2.map f.branches = Sym2.map g := by
      funext p
      refine Sym2.inductionOn p ?_
      intro u v
      simp [Function.comp_def]
    rw [he]
    exact hbonds

end WaveTurbulence.Twist
