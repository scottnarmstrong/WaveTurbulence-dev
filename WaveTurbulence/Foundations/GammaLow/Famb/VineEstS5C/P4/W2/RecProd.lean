/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecRow
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecProd
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS5C.P4.W2.RecRow
-- L5b port of `WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecProd` (sha256 162c215e24796d24…): its chain-dependent declarations only, over 𝒱_γ;
-- see GammaLow/Famb/PROGRESS.md (Design) and COPIED-SHA256SUMS.

/-! # P4-W2 (session 13, step 2g): the product of the exceptional weights over the exceptional rows

`vpSet recs`, `vbSet recs`: the rows whose pair (resp. branch) is exceptional.  `prod_vpSet_xqOf`: for a record list with distinct pairs inside the regional pairs,
the product of the exceptional weights `xqOf` over the pair rows `vpSet` is the product of the records' factors; likewise for the branches (`vbSet` has exactly one row
per record branch).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W2 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS5C.P4 WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
variable {γF : ℝ}
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A WaveTurbulence.GammaLow.Famb.VineEstS2
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4 WaveTurbulence.GammaLow.Famb.VineEstS5C WaveTurbulence.GammaLow.Famb.VineEstS3 WaveTurbulence.GammaLow.Famb.VineEstS4

variable {w d : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

variable (hM9 : NormalChartSupply γF) (B : CLChainAssemblyΓ γF G R n) (hG : G.IsPlain)

/-- The rows whose pair is exceptional. -/
noncomputable def vpSetΓ (recs : List (ExcRec G d)) : Finset (assemblyShapeΓ hM9 B).VIdx := by
  classical
  exact Finset.univ.filter fun v => (assemblyPairOfΓ hM9 B hG v).1 ∈ pexOf recs

/-- The rows whose branch is exceptional. -/
noncomputable def vbSetΓ (recs : List (ExcRec G d)) : Finset (assemblyShapeΓ hM9 B).VIdx := by
  classical
  exact Finset.univ.filter fun v => (assemblyBranchOfΓ hM9 B v).1 ∈ bexOf recs

theorem mem_vpSetΓ (recs : List (ExcRec G d)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    v ∈ vpSetΓ hM9 B hG recs ↔ (assemblyPairOfΓ hM9 B hG v).1 ∈ pexOf recs := by
  classical
  unfold vpSetΓ
  simp

theorem mem_vbSetΓ (recs : List (ExcRec G d)) (v : (assemblyShapeΓ hM9 B).VIdx) :
    v ∈ vbSetΓ hM9 B recs ↔ (assemblyBranchOfΓ hM9 B v).1 ∈ bexOf recs := by
  classical
  unfold vbSetΓ
  simp

theorem prod_vpSet_xqOfΓ (recs : List (ExcRec G d)) (hnd : (recs.map ExcRec.p0).Nodup)
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ)
    (ξ : GNode G.tree → (Fin d → ℤ)) :
    ∏ v ∈ vpSetΓ hM9 B hG recs, xqOf recs (assemblyPairOfΓ hM9 B hG v).1 t u ξ = (recs.map fun r => r.X ξ u).prod := by
  classical
  rw [← prod_pexOf_xqOf recs hnd t u ξ]
  refine (Finset.prod_nbij (fun v => (assemblyPairOfΓ hM9 B hG v).1) (fun v hv => (mem_vpSetΓ hM9 B hG recs v).mp hv)
    (fun v1 _ v2 _ h => ?_) (fun p hp => ?_) (fun v hv => rfl))
  · have h' : assemblyPairOfΓ hM9 B hG v1 = assemblyPairOfΓ hM9 B hG v2 := Subtype.ext h
    have := congrArg (assemblyPairBijΓ hG B hM9) h'
    rwa [assemblyPairBij_assemblyPairOfΓ, assemblyPairBij_assemblyPairOfΓ] at this
  · obtain ⟨r, hr, rfl⟩ := mem_pexOf.mp hp
    refine ⟨assemblyPairBijΓ hG B hM9 ⟨r.p0, hreg r hr⟩, (mem_vpSetΓ hM9 B hG recs _).mpr ?_, ?_⟩
    · rw [assemblyPairOf_bijΓ]; exact hp
    · exact congrArg Subtype.val (assemblyPairOf_bijΓ hM9 B hG ⟨r.p0, hreg r hr⟩)

theorem pairOf_injectiveΓ (v1 v2 : (assemblyShapeΓ hM9 B).VIdx)
    (h : (assemblyPairOfΓ hM9 B hG v1).1 = (assemblyPairOfΓ hM9 B hG v2).1) : v1 = v2 := by
  have := congrArg (assemblyPairBijΓ hG B hM9) (Subtype.ext h : assemblyPairOfΓ hM9 B hG v1 = assemblyPairOfΓ hM9 B hG v2)
  rwa [assemblyPairBij_assemblyPairOfΓ, assemblyPairBij_assemblyPairOfΓ] at this

theorem branchOf_injectiveΓ (v1 v2 : (assemblyShapeΓ hM9 B).VIdx)
    (h : (assemblyBranchOfΓ hM9 B v1).1 = (assemblyBranchOfΓ hM9 B v2).1) : v1 = v2 := by
  have := congrArg (assemblyBranchBijΓ hM9 B) (Subtype.ext h : assemblyBranchOfΓ hM9 B v1 = assemblyBranchOfΓ hM9 B v2)
  rwa [assemblyBranchBij_assemblyBranchOfΓ, assemblyBranchBij_assemblyBranchOfΓ] at this

/-- **The product identity `hX` from the per-record identities.** -/
theorem hX_of_recordsΓ (recs : List (ExcRec G d)) (hnp : (recs.map ExcRec.p0).Nodup) (hnb : (recs.map ExcRec.bj).Nodup)
    (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (t : Fin 3 → ℝ) (u : GBranch G.tree → ℝ)
    (ξ : GNode G.tree → (Fin d → ℤ)) (vpf vbf : ExcRec G d → (assemblyShapeΓ hM9 B).VIdx)
    (hvp : ∀ r ∈ recs, (assemblyPairOfΓ hM9 B hG (vpf r)).1 = r.p0)
    (hvb : ∀ r ∈ recs, (assemblyBranchOfΓ hM9 B (vbf r)).1 = r.bj)
    (Wp Wb : (assemblyShapeΓ hM9 B).VIdx → ℂ) (facr : ExcRec G d → ℂ) (C : ℂ)
    (hrec : ∀ r ∈ recs, r.X ξ u = facr r * (Wp (vpf r) * Wb (vbf r))) (hfac : (recs.map facr).prod = C) :
    ∏ v ∈ vpSetΓ hM9 B hG recs, xqOf recs (assemblyPairOfΓ hM9 B hG v).1 t u ξ =
      C * (∏ v ∈ vpSetΓ hM9 B hG recs, Wp v) * ∏ v ∈ vbSetΓ hM9 B recs, Wb v := by
  classical
  rw [prod_vpSet_xqOfΓ hM9 B hG recs hnp hreg t u ξ]
  have hl1 : (recs.map vpf).Nodup := by
    refine List.Nodup.of_map (fun v => (assemblyPairOfΓ hM9 B hG v).1) ?_
    have : (recs.map vpf).map (fun v => (assemblyPairOfΓ hM9 B hG v).1) = recs.map ExcRec.p0 := by
      rw [List.map_map]
      exact List.map_congr_left fun r hr => hvp r hr
    rw [this]; exact hnp
  have hl2 : (recs.map vbf).Nodup := by
    refine List.Nodup.of_map (fun v => (assemblyBranchOfΓ hM9 B v).1) ?_
    have : (recs.map vbf).map (fun v => (assemblyBranchOfΓ hM9 B v).1) = recs.map ExcRec.bj := by
      rw [List.map_map]
      exact List.map_congr_left fun r hr => hvb r hr
    rw [this]; exact hnb
  have e1 : vpSetΓ hM9 B hG recs = (recs.map vpf).toFinset := by
    ext v
    rw [mem_vpSetΓ, mem_pexOf, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨r, hr, h⟩
      exact ⟨r, hr, pairOf_injectiveΓ hM9 B hG _ _ ((hvp r hr).trans h)⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hr, (hvp r hr).symm⟩
  have e2 : vbSetΓ hM9 B recs = (recs.map vbf).toFinset := by
    ext v
    rw [mem_vbSetΓ, mem_bexOf, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨r, hr, h⟩
      exact ⟨r, hr, branchOf_injectiveΓ hM9 B _ _ ((hvb r hr).trans h)⟩
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

end WaveTurbulence.GammaLow.Famb.VineEstS5C.P4.W2
