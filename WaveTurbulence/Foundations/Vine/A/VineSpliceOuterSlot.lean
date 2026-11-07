/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSplicePortTrace
public import WaveTurbulence.Foundations.Vine.A.VineSpliceLeafRange
public import WaveTurbulence.Foundations.FinalCount.RedSpliceStage
/-! Each surviving crown has an original external outer incidence. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole
variable {w : ℕ} {G : Garden w}

/-- Two units in a disjoint list with a common atom are identical. -/
theorem splice_units_eq_of_overlap (l : List (CLBlock G))
    (hd : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    {u v : CLBlock G} (hu : u ∈ l) (hv : v ∈ l) {x : GBranch G.tree}
    (hxu : x ∈ u.atoms) (hxv : x ∈ v.atoms) : u = v := by
  let : Std.Symm (fun u v : CLBlock G => Disjoint u.atoms v.atoms) := ⟨fun _ _ h => h.symm⟩
  by_contra hne
  exact Finset.disjoint_left.mp (hd.forall hu hv hne) hxu hxv

/-- Every nonempty merge label is the upper joint of a containing unit. -/
theorem spliceFold_cls_some (l : List (CLBlock G))
    (hd : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (v a : GBranch G.tree) (h : (spliceFold G l).cls v = some a) :
    ∃ u ∈ l, v ∈ u.atoms ∧ u.upper = a := by
  classical
  by_cases hm : ∃ u ∈ l, v ∈ u.atoms
  · obtain ⟨u, hu, hv⟩ := hm
    exact ⟨u, hu, hv, Option.some.inj ((spliceFold_cls_mem l hd hu hv).symm.trans h)⟩
  · have hn : ∀ u ∈ l, v ∉ u.atoms := fun u hu hv => hm ⟨u, hu, hv⟩
    rw [spliceFold_cls_notMem l hd hn] at h
    cases h

/-- Deletion is precisely internal incidence in one of the actual disjoint units. -/
theorem spliceFold_deleted_iff (l : List (CLBlock G))
    (hd : l.Pairwise (fun u v => Disjoint u.atoms v.atoms)) (x : GardenDart G) :
    (∃ a, (spliceFold G l).cls (G.molecule.atom x) = some a ∧
      (spliceFold G l).cls (G.molecule.atom (G.molecule.mate x)) = some a) ↔
    ∃ u ∈ l, G.molecule.InGroup u.atoms x := by
  constructor
  · rintro ⟨a, h1, h2⟩
    obtain ⟨u, hu, hx, hea⟩ := spliceFold_cls_some l hd _ _ h1
    obtain ⟨v, hv, hy, heb⟩ := spliceFold_cls_some l hd _ _ h2
    have he : u = v := splice_units_eq_of_overlap l hd hu hv u.isBlock.2.1
      ((hea.trans heb.symm) ▸ v.isBlock.2.1)
    exact ⟨u, hu, hx, he.symm ▸ hy⟩
  · rintro ⟨u, hu, hx, hy⟩
    exact ⟨u.upper, spliceFold_cls_mem l hd hu hx, spliceFold_cls_mem l hd hu hy⟩

/-- Every retained old branch has an outer port external to every spliced unit. -/
theorem spliceFold_outer_slot (l : List (CLBlock G))
    (hd : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    (b : GBranch (spliceFold G l).G.tree) :
    ∃ i : Fin 3, i ≠ 1 ∧ ∀ u ∈ l,
      i.succ ∉ internalPositions G u.atoms ((spliceFold G l).M.ob b) := by
  classical
  let v := (spliceFold G l).M.ob b
  by_cases hm : ∃ u ∈ l, v ∈ u.atoms
  · obtain ⟨u, hu, hv⟩ := hm
    have he : u.upper = v := by
      have hr := ((spliceFold G l).M.ob_range v).mp ⟨b, rfl⟩
      rw [spliceFold_cls_mem l hd hu hv] at hr
      exact Option.some.inj (hr.resolve_left (by intro h; cases h))
    let D := clSpliceSlotsOfBlock u.isBlock u.cl
    refine ⟨D.excluded, D.excluded_ne_middle, ?_⟩
    intro t ht hi
    obtain ⟨x, hx, hxg, hxi⟩ := (mem_internalPositions G).mp hi
    have hvt : v ∈ t.atoms := by change G.molecule.atom x = v at hx; exact hx ▸ hxg.1
    have htu : t = u := splice_units_eq_of_overlap l hd ht hu hvt hv
    subst t
    apply D.excluded_missing
    change D.excluded.succ ∈ internalPositions G u.atoms v at hi
    rwa [← he] at hi
  · refine ⟨0, by decide, ?_⟩
    intro u hu hi
    obtain ⟨x, hx, hxg, _⟩ := (mem_internalPositions G).mp hi
    exact hm ⟨u, hu, by change G.molecule.atom x = v at hx; exact hx ▸ hxg.1⟩

end WaveTurbulence.VineA
