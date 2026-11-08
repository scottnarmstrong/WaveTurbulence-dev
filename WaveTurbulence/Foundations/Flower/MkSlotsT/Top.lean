/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelClass
public import WaveTurbulence.Foundations.Flower.MkUnitsL.Defs

/-! # B3s-HELPER5 (γ) T2: the unit top filters of a class (`MkUnitsL.UnitTopFilters`)

B3-2's `UnitTopFilters L p a Mk SU base roots E` asks for a top weight `E` that is a function of the layered garden
and equals, on the reconstruction of every member `y` of the run class, the product over the units of the top
filters at radii `SU j` read at the member's unit top `(y.2 j).blk.a` on the collapsed decoration.

* `stemPick LG J t dd`: the capped-stem branch of tree `t` at depth `dd` (unique with one capped flower per tree,
  δ's `MkSlotsS.stem_eq_of_length`); `stemPick_eq`;
* `topE`: the product, over the units `j`, of the filters `radProd (SU j)` at `stemPick LG J (tj j) (dj j)`;
* **`unitTopFilters_stem`**: with `SU := SUStem` (tree-indexed radii, e.g. σ's) and `(tj j, dj j)` the tree and depth
  of the representative's core of the upper joint of unit `j`, `UnitTopFilters` holds at the marked set `mk a.prime`
  (B4's `classMk mkF a` at the integration's marking): the member's unit top is a stem node exactly when the
  representative's is (`stemB_member_iff`), in the same tree and at the same depth (δ's
  `MkSlotsS.stemCore_length_member`), so it is the picked node, and its filter is the member's top filter
  (`radProd_core_eq_nodeWeight`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate (CleanPt)

namespace WaveTurbulence.Flower.MkSlotsT

/-- The capped-stem branch of tree `t` at depth `dd`, if any. -/
def stemPick {w : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (t : Fin w) (dd : ℕ) :
    Option (GBranch LG.garden.tree) :=
  if h : ∃ b, b ∈ stemSetCap LG J t ∧ b.1.2.length = dd then some h.choose else none

theorem stemPick_eq {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)} (hone : MkSlotsS.OneFlower LG J)
    {t : Fin w} {b : GBranch LG.garden.tree} (hb : b ∈ stemSetCap LG J t) :
    stemPick LG J t b.1.2.length = some b := by
  have h : ∃ b', b' ∈ stemSetCap LG J t ∧ b'.1.2.length = b.1.2.length := ⟨b, hb, rfl⟩
  unfold stemPick
  rw [dif_pos h]
  exact congrArg some (MkSlotsS.stem_eq_of_length hone h.choose_spec.1 hb h.choose_spec.2)

/-- **The top weight**: the filters `radProd (SU j)` at the stem node of tree `tj j` at depth `dj j`. -/
def topE {w d n : ℕ} (L : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (J : Finset (Fin w)) (tj : Fin n → Fin w)
    (dj : Fin n → ℕ) (SU : Fin n → List ℝ) (LG : LayeredGarden w) (κ : GenDecoration LG.garden d roots 0) : ℂ :=
  ∏ j, (stemPick LG J (tj j) (dj j)).elim 1
    fun b => (radProd (SU j) (omegaNode LG.garden (cosetDecoration LG.garden L base κ.1) b) : ℂ)

section Class
variable {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R)) (J : Finset (Fin (2 * R)))

/-- The tree of the representative's core of the upper joint of unit `j`. -/
def topTree (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) : Fin (2 * R) :=
  (a.prime.data.corePosition (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper).1

/-- Its depth. -/
def topDepth (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length) : ℕ :=
  (a.prime.data.corePosition
    (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper).2.length

/-- The representative's unit radius lists for tree-indexed radii. -/
abbrev SURep (radT : Fin (2 * R) → List ℝ) :
    Fin (unitBlocks a.prime.skeleton a.totalSigma (mk a.prime)).length → List ℝ :=
  SUStem a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (fun b => radT b.1.1)
    (blk := unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime))

/-- **T2: `UnitTopFilters` for the stem filters** (tree-indexed radii, e.g. σ's `radSigma`). -/
theorem unitTopFilters_stem {d : ℕ} (hc : CleanPt J a)
    (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
    (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
    (hrepU : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
      ¬ IsCapFlowerParent (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.coreBranch a.prime.prime.1 b))
    (hcapY : ∀ y ∈ sourceClass a p (objKind (2 * R)) mk, ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
    (honeY : ∀ y ∈ sourceClass a p (objKind (2 * R)) mk,
      MkSlotsS.OneFlower (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J)
    (radT : Fin (2 * R) → List ℝ) (hradT : ∀ j, ∀ x ∈ radT j, 1 ≤ x) (L : ℝ) (base : Mom d)
    (roots : Fin (2 * R) → (Fin d → ℤ)) :
    MkUnitsL.UnitTopFilters L p a (mk a.prime) (SURep a mk J radT) base roots
      (topE L base J (topTree a mk) (topDepth a mk) (SURep a mk J radT)) := by
  refine ⟨fun j => SUStem_pos a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
    (fun b => radT b.1.1) (fun b => hradT b.1.1) j, fun y hy κ => ?_⟩
  have hy' : y ∈ sourceClass a p (objKind (2 * R)) mk := hy
  unfold topE
  refine Finset.prod_congr rfl fun j _ => ?_
  set Φ₁ := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  set hd₁ := unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)
  set c := Φ₁.hinge hd₁ j
  have hu₁ : (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).upper = Φ₁.br c :=
    (Φ₁.br_hinge hd₁ j).symm
  have hh : (memShape a mk y hy').hinge (source_disjMk a mk y hy') j = c :=
    hinge_eq_of_hmom Φ₁ (memShape a mk y hy') hd₁ (source_disjMk a mk y hy')
      (fun j i => congrFun (congrFun (memShape_hmom a mk y hy') j) i) j
  have hu₂ : (y.2 j).blk.a = (memShape a mk y hy').br c := by
    show (unitClBlock (y.2 j)).upper = _
    rw [← hh, (memShape a mk y hy').br_hinge]
  rw [hu₂]
  by_cases hst : StemB a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
    (coreLG a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (Φ₁.br c))
  · -- the member's unit top is the picked stem node
    have hsY := (stemB_member_iff a mk y hy' J hcapA (hcapY y hy') hG hrepU c).mpr hst
    obtain ⟨t, ht⟩ := hsY
    have htY : (coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
        ((memShape a mk y hy').br c)).1.1 = topTree a mk j := by
      unfold topTree
      rw [hu₁]
      exact (MkSlots.IntRest.coreBranch_fst y.1.data y.1.plain _).trans
        ((shape_br_fst (memShape a mk y hy') c).trans
          ((shape_br_fst Φ₁ c).symm.trans (MkSlots.IntRest.coreBranch_fst a.prime.data a.prime.prime.1 _).symm))
    have htt : t = topTree a mk j := by
      rw [← htY]; exact ((Finset.mem_filter.mp ht).2.1).symm
    subst htt
    have hstA : OnStemAddr (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a)
        (sourceLayer_isLayering a)) J (a.prime.data.corePosition (Φ₁.br c)) :=
      ((stemB_core_iff a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (Φ₁.br c)).mp
        hst).1
    have hdep := MkSlotsS.stemCore_length_member a mk y hy' J hcapA (hcapY y hy') hG hc c hstA
    have hdj : topDepth a mk j = (coreLG y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)
        ((memShape a mk y hy').br c)).1.2.length := by
      unfold topDepth
      rw [hu₁]
      exact hdep
    rw [hdj, stemPick_eq (honeY y hy') ht]
    exact radProd_core_eq_nodeWeight y.1.data y.1.plain κ L base _ _
  · -- no filter: both sides are `1`
    have hSU : SURep a mk J radT j = [] := by
      show SUStem a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (fun b => radT b.1.1)
        (blk := unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)) j = []
      unfold SUStem
      rw [hu₁, if_neg hst]
    rw [hSU]
    have h1 : VineSpaceK.nodeWeight (V5W2L.topFilterWeightL ([] : List ℝ)) L base
        ((memShape a mk y hy').br c) (collapseGenDecoration y.1.data y.1.plain κ).1 = 1 := by
      simp [VineSpaceK.nodeWeight, V5W2L.topFilterWeightL]
    rw [h1]
    rcases stemPick _ J (topTree a mk j) (topDepth a mk j) with _ | b
    · rfl
    · simp [radProd]

end Class

end WaveTurbulence.Flower.MkSlotsT
