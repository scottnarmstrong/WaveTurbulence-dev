/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRow

/-! # P4-W2 (session 13, step 2g): the product of the exceptional weights over the exceptional rows

`vpSet recs`, `vbSet recs`: the rows whose pair (resp. branch) is exceptional.  `prod_vpSet_xqOf`: for a record list with distinct pairs inside the regional pairs,
the product of the exceptional weights `xqOf` over the pair rows `vpSet` is the product of the records' factors; likewise for the branches (`vbSet` has exactly one row
per record branch).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem prod_pexOf_xqOf (recs : List (ExcRec G d)) (hnd : (recs.map ExcRec.p0).Nodup) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ)
    (ξ : GNode G.tree → (Fin d → ℤ)) :
    ∏ p ∈ pexOf recs, xqOf recs p t u ξ = (recs.map fun r => r.X ξ u).prod := by
  classical
  induction recs with
  | nil => simp [pexOf_nil]
  | cons r rs ih =>
    have hnd2 : (∀ x ∈ rs, ¬ x.p0 = r.p0) ∧ (rs.map ExcRec.p0).Nodup := by simpa using hnd
    have hnd' : (rs.map ExcRec.p0).Nodup := hnd2.2
    have hr : ∀ r' ∈ rs, r'.p0 ≠ r.p0 := hnd2.1
    have hnot : r.p0 ∉ pexOf rs := by
      rw [mem_pexOf]
      rintro ⟨r', hr', h⟩
      exact hr r' hr' h
    rw [pexOf_cons, Finset.prod_insert hnot, xqOf_cons_self r rs hr, List.map_cons, List.prod_cons, ← ih hnd']
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    refine xqOf_cons_ne r rs ?_ t u ξ
    rintro rfl
    exact hnot hp

variable (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (hG : G.IsPlain)

/-- The rows whose pair is exceptional. -/
noncomputable def vpSet (recs : List (ExcRec G d)) : Finset (assemblyShape hM9 B).VIdx := by
  classical
  exact Finset.univ.filter fun v => (assemblyPairOf hM9 B hG v).1 ∈ pexOf recs

/-- The rows whose branch is exceptional. -/
noncomputable def vbSet (recs : List (ExcRec G d)) : Finset (assemblyShape hM9 B).VIdx := by
  classical
  exact Finset.univ.filter fun v => (assemblyBranchOf hM9 B v).1 ∈ bexOf recs

theorem mem_vpSet (recs : List (ExcRec G d)) (v : (assemblyShape hM9 B).VIdx) :
    v ∈ vpSet hM9 B hG recs ↔ (assemblyPairOf hM9 B hG v).1 ∈ pexOf recs := by
  classical
  unfold vpSet
  simp

theorem mem_vbSet (recs : List (ExcRec G d)) (v : (assemblyShape hM9 B).VIdx) :
    v ∈ vbSet hM9 B recs ↔ (assemblyBranchOf hM9 B v).1 ∈ bexOf recs := by
  classical
  unfold vbSet
  simp

theorem prod_vpSet_xqOf (recs : List (ExcRec G d)) (hnd : (recs.map ExcRec.p0).Nodup)
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ)
    (ξ : GNode G.tree → (Fin d → ℤ)) :
    ∏ v ∈ vpSet hM9 B hG recs, xqOf recs (assemblyPairOf hM9 B hG v).1 t u ξ = (recs.map fun r => r.X ξ u).prod := by
  classical
  rw [← prod_pexOf_xqOf recs hnd t u ξ]
  refine (Finset.prod_nbij (fun v => (assemblyPairOf hM9 B hG v).1) (fun v hv => (mem_vpSet hM9 B hG recs v).mp hv)
    (fun v1 _ v2 _ h => ?_) (fun p hp => ?_) (fun v hv => rfl))
  · have h' : assemblyPairOf hM9 B hG v1 = assemblyPairOf hM9 B hG v2 := Subtype.ext h
    have := congrArg (assemblyPairBij hG B hM9) h'
    rwa [assemblyPairBij_assemblyPairOf, assemblyPairBij_assemblyPairOf] at this
  · obtain ⟨r, hr, rfl⟩ := mem_pexOf.mp hp
    refine ⟨assemblyPairBij hG B hM9 ⟨r.p0, hreg r hr⟩, (mem_vpSet hM9 B hG recs _).mpr ?_, ?_⟩
    · rw [assemblyPairOf_bij]; exact hp
    · exact congrArg Subtype.val (assemblyPairOf_bij hM9 B hG ⟨r.p0, hreg r hr⟩)

theorem pairOf_injective (v1 v2 : (assemblyShape hM9 B).VIdx)
    (h : (assemblyPairOf hM9 B hG v1).1 = (assemblyPairOf hM9 B hG v2).1) : v1 = v2 := by
  have := congrArg (assemblyPairBij hG B hM9) (Subtype.ext h : assemblyPairOf hM9 B hG v1 = assemblyPairOf hM9 B hG v2)
  rwa [assemblyPairBij_assemblyPairOf, assemblyPairBij_assemblyPairOf] at this

theorem branchOf_injective (v1 v2 : (assemblyShape hM9 B).VIdx)
    (h : (assemblyBranchOf hM9 B v1).1 = (assemblyBranchOf hM9 B v2).1) : v1 = v2 := by
  have := congrArg (assemblyBranchBij hM9 B) (Subtype.ext h : assemblyBranchOf hM9 B v1 = assemblyBranchOf hM9 B v2)
  rwa [assemblyBranchBij_assemblyBranchOf, assemblyBranchBij_assemblyBranchOf] at this

/-- **The product identity `hX` from the per-record identities.** -/
theorem hX_of_records (recs : List (ExcRec G d)) (hnp : (recs.map ExcRec.p0).Nodup) (hnb : (recs.map ExcRec.bj).Nodup)
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ)
    (ξ : GNode G.tree → (Fin d → ℤ)) (vpf vbf : ExcRec G d → (assemblyShape hM9 B).VIdx)
    (hvp : ∀ r ∈ recs, (assemblyPairOf hM9 B hG (vpf r)).1 = r.p0)
    (hvb : ∀ r ∈ recs, (assemblyBranchOf hM9 B (vbf r)).1 = r.bj)
    (Wp Wb : (assemblyShape hM9 B).VIdx → ℂ) (facr : ExcRec G d → ℂ) (C : ℂ)
    (hrec : ∀ r ∈ recs, r.X ξ u = facr r * (Wp (vpf r) * Wb (vbf r))) (hfac : (recs.map facr).prod = C) :
    ∏ v ∈ vpSet hM9 B hG recs, xqOf recs (assemblyPairOf hM9 B hG v).1 t u ξ =
      C * (∏ v ∈ vpSet hM9 B hG recs, Wp v) * ∏ v ∈ vbSet hM9 B recs, Wb v := by
  classical
  rw [prod_vpSet_xqOf hM9 B hG recs hnp hreg t u ξ]
  have hl1 : (recs.map vpf).Nodup := by
    refine List.Nodup.of_map (fun v => (assemblyPairOf hM9 B hG v).1) ?_
    have : (recs.map vpf).map (fun v => (assemblyPairOf hM9 B hG v).1) = recs.map ExcRec.p0 := by
      rw [List.map_map]
      exact List.map_congr_left fun r hr => hvp r hr
    rw [this]; exact hnp
  have hl2 : (recs.map vbf).Nodup := by
    refine List.Nodup.of_map (fun v => (assemblyBranchOf hM9 B v).1) ?_
    have : (recs.map vbf).map (fun v => (assemblyBranchOf hM9 B v).1) = recs.map ExcRec.bj := by
      rw [List.map_map]
      exact List.map_congr_left fun r hr => hvb r hr
    rw [this]; exact hnb
  have e1 : vpSet hM9 B hG recs = (recs.map vpf).toFinset := by
    ext v
    rw [mem_vpSet, mem_pexOf, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨r, hr, h⟩
      exact ⟨r, hr, pairOf_injective hM9 B hG _ _ ((hvp r hr).trans h)⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hr, (hvp r hr).symm⟩
  have e2 : vbSet hM9 B recs = (recs.map vbf).toFinset := by
    ext v
    rw [mem_vbSet, mem_bexOf, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨r, hr, h⟩
      exact ⟨r, hr, branchOf_injective hM9 B _ _ ((hvb r hr).trans h)⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hr, (hvb r hr).symm⟩
  rw [e1, e2, List.prod_toFinset _ hl1, List.prod_toFinset _ hl2]
  have : (recs.map fun r => r.X ξ u) = recs.map fun r => facr r * (Wp (vpf r) * Wb (vbf r)) :=
    List.map_congr_left hrec
  have key : ∀ l : List (ExcRec G d), (l.map fun r => facr r * (Wp (vpf r) * Wb (vbf r))).prod =
      (l.map facr).prod * (l.map fun r => Wp (vpf r)).prod * (l.map fun r => Wb (vbf r)).prod := by
    intro l
    induction l with
    | nil => simp
    | cons r rs ih => simp only [List.map_cons, List.prod_cons, ih]; ring
  rw [this, key, hfac, List.map_map, List.map_map]
  rfl

end WaveTurbulence.VineEstS5C.P4.W2
