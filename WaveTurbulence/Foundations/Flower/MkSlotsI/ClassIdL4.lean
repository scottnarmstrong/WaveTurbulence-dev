/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassIdL3
public import WaveTurbulence.Foundations.Flower.MkSlots.IntAdm
public import WaveTurbulence.Foundations.Flower.MkSlots.Geo

/-! # B3s-HELPER7 ClassId (lower bounds, part 4): no lower bound on the unit interiors of a member

**`member_lbS_inter`** (`hlbU` of VBC/PVBR): for a member `y` of the run class, no non-upper atom `x` of a unit of `y`
carries a lower bound `lbS`. A pinned leaf child of `x` is retained (`leafPin_ret`), hence a crown node of the unit:
`x` is the unit lower (`ext_child`). Its lower bound is the representative's (`member_lbS_lower`); there, the pinned
couple root below the lower `b` of unit `j` makes the core of `b` protected (`parent_mem_protI`), and `b` is a
non-upper atom of the vine `c ∈ 𝒱₀ \ Mk` of the last piece of the aligned assembly of unit `j` (`exists_piece_lower`,
`alignedPiece_mem_vinesV0`, `ne_upper_of_piece`). So `c` is marked, against `hMk` (the marked vines of `𝒱₀` lie in the
marked set `mk a.prime`; the hypothesis from which `hrepUP` itself is derived, β's `hU_rep_pat_recon`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsI

/-- **The lower joint of a chain assembly is a non-upper atom of one of its pieces** (the last appended one). -/
theorem exists_piece_lower {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : VineEstS2.CLChainAssembly G R n) :
    ∃ i : Fin n, b ∈ (VineEstS2.assemblyPieceAt B i).atoms ∧ b ≠ (VineEstS2.assemblyPieceAt B i).upper := by
  cases B with
  | single hV R => exact ⟨0, hV.1.2.2.1, fun h => hV.1.2.2.2.1 h.symm⟩
  | append B hT hi hU R => exact ⟨0, hT.1.2.2.1, fun h => hT.1.2.2.2.1 h.symm⟩

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J p)
  (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hGeoA hrepUP in
/-- **No lower bound at the unit lowers of the representative** (`hMk`: the marked vines of `𝒱₀` are marked). -/
theorem rep_lbS_lower (kSel : Fin (2 * R) → Option ℕ)
    (hMk : ∀ c ∈ markI J pat t s kSel a.prime, c ∈ vinesV0 a.prime.skeleton a.totalSigma → c ∈ mk a.prime)
    (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) :
    MkSlotsB.lbS a.prime.data a.prime.prime.1
        (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
          t s) s (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower = none := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  set b := (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).lower with hb
  have hfa : MkSlots.fixCore a.prime.data a.prime.prime.1
      (fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat
        t s) b = none :=
    hrepUP j _ (lower_mem _)
  rw [lbS_eq_leaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J hcapA pat t s]
  refine ite_eq_right fun h => ?_
  obtain ⟨u, hu, hch, hne⟩ := (pinChild_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    J hcapA pat t s id (fun b' hb' => absurd rfl (hb' b')) b hfa).mpr h.2
  obtain ⟨u', hu', hch', -⟩ := (pinChild_decoded a.prime.data a.prime.prime.1 (sourceLayer a)
    (sourceLayer_isLayering a) J pat t s a.layered (sourceLayer_reconstructs a) a.prime.decodes id b).mpr
    ⟨u, hu, hch, hne⟩
  have hprot : (a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes b).toNode ∈
      protI a.layered J pat t s kSel := MkSlotsB.parent_mem_protI kSel hch' hu'
  obtain ⟨k, hk1, hk2⟩ := exists_piece_lower
    (alignedAssemblyMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j)
  obtain ⟨c, hc, hca⟩ := alignedPiece_mem_vinesV0 a.totalSigma (mk a.prime) j k
  have hne' := ne_upper_of_piece _ k c hca hk1 hk2
  rw [RedSplice.mem_vinesV0] at hc
  obtain ⟨hc0, hcMk⟩ := hc
  have hbc : b ∈ c.atoms := by rw [hca]; exact hk1
  have hm : c ∈ markI J pat t s kSel a.prime :=
    ⟨RedSplice.vinesV0_subset _ _ hc0, b, hbc, hne',
      (a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes b).toNode, hprot,
      ProtGeo.mem_nearRegion_own (ProtGeo.skelAddr_mem_ownRegion _ _ b)⟩
  exact hcMk (hMk c hm hc0)

include hy hG hGeoA hGeoY hrepUP in
/-- **No lower bound on the unit interiors of a member** (`hlbU` of VBC/PVBR). -/
theorem member_lbS_inter (kSel : Fin (2 * R) → Option ℕ)
    (hMk : ∀ c ∈ markI J pat t s kSel a.prime, c ∈ vinesV0 a.prime.skeleton a.totalSigma → c ∈ mk a.prime) :
    ∀ j, ∀ x ∈ VineB.inter (fun j => unitClBlock (y.2 j)) j,
      MkSlotsB.lbS y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s
        x = none := by
  intro j x hx
  obtain ⟨hxa, hxu⟩ := VineB.mem_inter.mp hx
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  have hfx : MkSlots.fixCore y.1.data y.1.plain
      (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) x =
        none :=
    MkSlotsB.member_fix_unit_pat a mk y hy hG J hcapA hcapY pat t s hrepUP j x hxa
  by_contra hsome
  have h := hsome
  rw [lbS_eq_leaf y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY pat t s] at h
  have hL : LeafPinBelow y.1.data y.1.plain
      (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) x := by
    by_contra hn
    exact h (ite_eq_right fun hc => hn hc.2)
  obtain ⟨σ, i, hσ, hp⟩ := hL
  have hret := leafPin_ret y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J hcapY pat t s
    (fun j => unitClBlock (y.2 j)) x hfx σ i hσ hp
  have hnr : x.child i ∉ clRealizationNodes y.1.skeleton (unitClBlock (y.2 j)).atoms := by
    rw [← hσ]
    rcases hret j with h1 | h1
    · exact h1
    · exact (SpliceShape.leaf_ne_branch h1).elim
  rcases ext_child (unitClBlock (y.2 j)) hxa i hnr with ⟨hxu', -⟩ | ⟨hxl, -⟩
  · exact hxu hxu'
  · subst hxl
    apply hsome
    rw [member_lbS_lower a mk y hy hG J hGeoA hGeoY pat t s hrepUP j]
    exact rep_lbS_lower a mk J hGeoA pat t s hrepUP kSel hMk j

end Class

end WaveTurbulence.Flower.MkSlotsI
