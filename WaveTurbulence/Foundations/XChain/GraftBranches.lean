/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.GraftLeaves
/-! Branching nodes split into top branching nodes and lower branching nodes after grafting. -/
public section
namespace WaveTurbulence.Induct
open Finset TTree

theorem mem_branching_graftTree (T : TTree) (f : TTree.Path → TTree) (q : TTree.Path) :
    q ∈ (graftTree T f).branching ↔ q ∈ T.branching ∨
      ∃ a ∈ T.leaves, ∃ b ∈ (f a).branching, a ++ b = q := by
  induction T generalizing f q with
  | leaf => simp [graftTree, TTree.branching, TTree.leaves]
  | node l m r hl hm hr =>
    constructor
    · intro h
      simp only [graftTree, TTree.branching, Finset.mem_insert, Finset.mem_union] at h
      rcases h with rfl | (h | h) | h
      · exact Or.inl (by simp [TTree.branching])
      · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp h
        rcases (hl (fun a => f (0 :: a)) _).mp hu with hb | ⟨a, ha, b, hb, rfl⟩
        · exact Or.inl (by simp [TTree.branching, TTree.cons_mem_pre, hb])
        · exact Or.inr ⟨0 :: a, by simp [TTree.leaves, TTree.cons_mem_pre, ha], b, hb, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp h
        rcases (hm (fun a => f (1 :: a)) _).mp hu with hb | ⟨a, ha, b, hb, rfl⟩
        · exact Or.inl (by simp [TTree.branching, TTree.cons_mem_pre, hb])
        · exact Or.inr ⟨1 :: a, by simp [TTree.leaves, TTree.cons_mem_pre, ha], b, hb, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp h
        rcases (hr (fun a => f (2 :: a)) _).mp hu with hb | ⟨a, ha, b, hb, rfl⟩
        · exact Or.inl (by simp [TTree.branching, TTree.cons_mem_pre, hb])
        · exact Or.inr ⟨2 :: a, by simp [TTree.leaves, TTree.cons_mem_pre, ha], b, hb, rfl⟩
    · intro h
      rcases h with hb | ⟨a, ha, b, hb, rfl⟩
      · simp only [TTree.branching, Finset.mem_insert, Finset.mem_union] at hb
        rcases hb with rfl | (hb | hb) | hb
        · simp [graftTree, TTree.branching]
        · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp hb
          have h := (hl (fun a => f (0 :: a)) _).mpr (Or.inl hu)
          simp [graftTree, TTree.branching, TTree.cons_mem_pre, h]
        · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp hb
          have h := (hm (fun a => f (1 :: a)) _).mpr (Or.inl hu)
          simp [graftTree, TTree.branching, TTree.cons_mem_pre, h]
        · obtain ⟨u, hu, rfl⟩ := TTree.mem_pre.mp hb
          have h := (hr (fun a => f (2 :: a)) _).mpr (Or.inl hu)
          simp [graftTree, TTree.branching, TTree.cons_mem_pre, h]
      · simp only [TTree.leaves, Finset.mem_union] at ha
        rcases ha with (ha | ha) | ha
        · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
          have h := (hl (fun a => f (0 :: a)) _).mpr (Or.inr ⟨a, hleaf, b, hb, rfl⟩)
          simpa [graftTree, TTree.branching, TTree.cons_mem_pre] using h
        · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
          have h := (hm (fun a => f (1 :: a)) _).mpr (Or.inr ⟨a, hleaf, b, hb, rfl⟩)
          simpa [graftTree, TTree.branching, TTree.cons_mem_pre] using h
        · obtain ⟨a, hleaf, rfl⟩ := TTree.mem_pre.mp ha
          have h := (hr (fun a => f (2 :: a)) _).mpr (Or.inr ⟨a, hleaf, b, hb, rfl⟩)
          simpa [graftTree, TTree.branching, TTree.cons_mem_pre] using h

end WaveTurbulence.Induct
