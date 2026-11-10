/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoLb
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoU
public import WaveTurbulence.Foundations.Flower.ProtGeo.Couple
public import WaveTurbulence.Foundations.RegStruct.OperationBRoots

/-! # B3s-HELPER3 B4 (R187): a native couple root is never a capped flower parent

A root of the native couple of a skeleton pair is a capped flower parent only if a depth-one leaf of its tree is paired
with a leaf of a cap tree (`cfp_nativeRoot_iff`). The cap side is then a single leaf, so the couple code is
`type2 X nil triv` (or its mirror, D2b's `code_of_trees2_leaf`/`code_of_trees1_leaf`) whose only cross pair is the
lone leaf at `X.lonePath`, of even length (`chain_lonePath_length`): a depth-one cross pair is impossible
(`nativeRoot_not_cfp`).

Hence **the pinned native tops with a free clock are exactly the `dParent`-pinned roots of the paired trees `T1` of
cap couples** (`pinnedTop_freeClock_dParent`), the lower bounds sit only on `dParent` trees (`lbS_dParent`,
`lbAt_dParent`), and atoms of trees whose pattern is not `dParent` (e.g. selected trees, `pat = plain`) carry none
(`lbAt_eq_none`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntGeo
open WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

/-- The endpoints of the pairs of a chain rooted at `(j, [])` lie in tree `j`. -/
theorem chain_pairsAt_fst (X : RegChain) (ζ : ℤˣ) (j : Fin 2) :
    ∀ z ∈ X.pairsAt ζ ((j, []) : Fin 2 × Path), z.1.1 = j ∧ z.2.1 = j := by
  intro z hz
  let f : Fin 2 × Path → Fin 2 × Path := fun y => (j, y.2)
  have hf : RespectsAt f (j, []) := fun p => by simp [f, addrExt]
  have hm := chain_pairsAt_map_local X f (j, []) hf ζ
  have hfa : f (j, []) = (j, []) := rfl
  rw [hfa] at hm
  rw [hm] at hz
  obtain ⟨y, -, rfl⟩ := List.mem_map.mp hz
  exact ⟨rfl, rfl⟩

theorem lonePath_ne_singleton (X : RegChain) (k : Fin 3) : X.lonePath ≠ [k] := by
  intro h
  have hl := chain_lonePath_length X
  rw [h] at hl
  simp at hl
  omega

/-- The cross pairs of `type2 X nil triv`: a depth-one leaf of tree `0` is never paired with tree `1`. -/
theorem type2_left_no_short (X : RegChain) (k : Fin 3) (r : Path)
    (h : (((0 : Fin 2), [k]), ((1 : Fin 2), r)) ∈
      symmPairs ((RegCpl.type2 X .nil .triv).pairsAt ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)))) :
    False := by
  rw [mem_symmPairs_iff, type2_left_pairsAt] at h
  rcases h with h | h <;> rcases List.mem_append.mp h with h | h
  · exact absurd (chain_pairsAt_fst X 1 0 _ h).2 (by simp)
  · simp only [RegCpl.pairsAt, List.mem_singleton, Prod.mk.injEq, addrExt] at h
    exact lonePath_ne_singleton X k (by simpa using h.1.2.symm)
  · exact absurd (chain_pairsAt_fst X 1 0 _ h).1 (by simp)
  · simp only [RegCpl.pairsAt, List.mem_singleton, Prod.swap_prod_mk, Prod.mk.injEq, addrExt] at h
    exact absurd h.1.1 (by decide)

/-- The mirror: a depth-one leaf of tree `1` of `type2 nil X triv` is never paired with tree `0`. -/
theorem type2_right_no_short (X : RegChain) (k : Fin 3) (r : Path)
    (h : (((1 : Fin 2), [k]), ((0 : Fin 2), r)) ∈
      symmPairs ((RegCpl.type2 .nil X .triv).pairsAt ((0 : Fin 2), ([] : Path)) ((1 : Fin 2), ([] : Path)))) :
    False := by
  rw [mem_symmPairs_iff, type2_right_pairsAt] at h
  rcases h with h | h <;> rcases List.mem_append.mp h with h | h
  · exact absurd (chain_pairsAt_fst X (-1) 1 _ h).2 (by simp)
  · simp only [RegCpl.pairsAt, List.mem_singleton, Prod.mk.injEq, addrExt] at h
    exact absurd h.1.1 (by decide)
  · exact absurd (chain_pairsAt_fst X (-1) 1 _ h).1 (by simp)
  · simp only [RegCpl.pairsAt, List.mem_singleton, Prod.swap_prod_mk, Prod.mk.injEq, addrExt] at h
    exact lonePath_ne_singleton X k (by simpa using h.2.2.symm)

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)

include hcap in
/-- **A root of a native couple is never a capped flower parent.** -/
theorem nativeRoot_not_cfp (q : SourcePair S) (j : Fin 2) (T : GBranch (D.forest hS))
    (hT : T.toNode = (nativeCoupleForest D hS q).root j) :
    ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J T := by
  intro hc
  obtain ⟨hni, ℓ', hside, hlen, hpJ⟩ := (cfp_nativeRoot_iff D hS layer hLayer J q j T hT).mp hc
  obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hlen
  obtain ⟨j₂, hj₂⟩ : ∃ j₂, ((decodedCouple (D.couple q)).pair ℓ').1.1 = j₂ := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, ((decodedCouple (D.couple q)).pair ℓ').1.2 = r := ⟨_, rfl⟩
  rw [hj₂] at hpJ
  have hne : j₂ ≠ j := fun h => hni (h ▸ hpJ)
  -- the cap side of the couple is a single leaf
  have hleaf : coupleForest (D.couple q) j₂ = TTree.leaf := by
    have hsub := (nativeCoupleForest D hS q).subtree_eq j₂
    have hl : (D.forest hS) ((nativeCoupleForest D hS q).root j₂).1.1 = TTree.leaf := hcap _ hpJ
    rw [hl] at hsub
    cases hp : ((nativeCoupleForest D hS q).root j₂).1.2 with
    | nil =>
      rw [hp] at hsub
      exact (Option.some.inj hsub).symm
    | cons x xs =>
      rw [hp] at hsub
      exact absurd hsub (by simp [Comb.subtree])
  -- the other side is not
  have hnleaf : coupleForest (D.couple q) j ≠ TTree.leaf := by
    intro h0
    have hm := ℓ'.2
    have e : ℓ'.1 = (j, [k]) := Prod.ext hside hk
    rw [e] at hm
    change [k] ∈ (coupleForest (D.couple q) j).leaves at hm
    rw [h0] at hm
    simp [TTree.leaves] at hm
  -- the pair
  have hmem : (ℓ'.1, ((decodedCouple (D.couple q)).pair ℓ').1) ∈ symmPairs (D.couple q).raw.2 :=
    gardenOfPairs_pair_mem _ _ _ _ _ _ _ ℓ'
  have e1 : ℓ'.1 = (j, [k]) := Prod.ext hside hk
  have e2 : ((decodedCouple (D.couple q)).pair ℓ').1 = (j₂, r) := Prod.ext hj₂ hr
  rw [e1, e2] at hmem
  have hwf := D.couple_wf q
  change ((j, [k]), (j₂, r)) ∈ symmPairs ((D.couple q).pairsAt ((0 : Fin 2), []) ((1 : Fin 2), [])) at hmem
  fin_cases j <;> fin_cases j₂
  · exact hne rfl
  · obtain ⟨X, hQ, -⟩ := ProtGeo.code_of_trees2_leaf hwf hleaf hnleaf
    rw [hQ] at hmem
    exact type2_left_no_short X k r hmem
  · obtain ⟨X, hQ, -⟩ := ProtGeo.code_of_trees1_leaf hwf hleaf hnleaf
    rw [hQ] at hmem
    exact type2_right_no_short X k r hmem
  · exact hne rfl

/-- The garden branch of a native couple top is the root of the native couple. -/
theorem nativeBr_couple_top (p : SourcePair S) (q : NativeClockBranch D (.inl p)) (hq : NativeTop D (.inl p) q) :
    (nativeBr D hS (.inl p) q).toNode = (nativeCoupleForest D hS p).root q.1.1 := by
  obtain ⟨⟨j, r⟩, hm⟩ := q
  have hr : r = [] := hq
  subst hr
  apply Subtype.ext
  show (((nativeCoupleForest D hS p).root j).1.1, ((nativeCoupleForest D hS p).root j).1.2 ++ []) = _
  rw [List.append_nil]

variable (pat : Fin w → FixPat) (t s : ℝ)

include hcap in
/-- **The pinned native tops with a free clock are exactly the `dParent`-pinned roots of the paired trees `T1` of cap
couples** (pinned at `s`). -/
theorem pinnedTop_freeClock_dParent (sl : ReplacementSlot S) (q : NativeClockBranch D sl) (hq : NativeTop D sl q)
    {v : ℝ} (hv : MkSlots.fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) sl q = some v)
    (c : GBranch S.tree) (i : Fin 3) (hc : nativeClockNode D hS sl q = c.child i)
    (hfree : MkSlots.fixCore D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) c = none) :
    ∃ p : SourcePair S, sl = .inl p ∧ IsCapPair S hS J p ∧ v = s ∧
      ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (nativeBr D hS sl q) ∧
      pat (nativeBr D hS sl q).1.1 = FixPat.dParent ∧
      ∃ C : GBranch (D.forest hS), IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C ∧
        C.IsChildOf (nativeBr D hS sl q) := by
  obtain ⟨p, rfl, hp, hvs, hcs⟩ :=
    pinnedTop_freeClock_cases D hS layer hLayer J hcap pat t s sl q hq hv c i hc hfree
  have hn := nativeRoot_not_cfp D hS layer hLayer J hcap p q.1.1 _ (nativeBr_couple_top D hS p q hq)
  rcases hcs with h | ⟨hpat, hC⟩
  · exact absurd h hn
  · exact ⟨p, rfl, hp, hvs, hn, hpat, hC⟩

variable (s : ℝ)

include hcap in
/-- **Lower bounds sit only on `dParent` trees.** -/
theorem lbS_dParent (c : GBranch S.tree)
    (h : (lbS D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) s c).isSome) :
    pat c.1.1 = FixPat.dParent := by
  unfold lbS at h
  split_ifs at h with hc
  · obtain ⟨hfree, sl, q, i, hq, hpin, hcl⟩ := hc
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hpin
    obtain ⟨-, -, -, -, -, hpat, -⟩ :=
      pinnedTop_freeClock_dParent D hS layer hLayer J hcap pat t s sl q hq hv c i hcl hfree
    obtain ⟨h1, -⟩ := nativeTop_isChildOf D hS sl q hq c i hcl
    rw [h1] at hpat
    rwa [show (D.coreBranch hS c).1.1 = c.1.1 from inflatedPosition_index S D.tree c.toNode] at hpat
  · exact absurd h (by simp)

/-! ## The piece: lower bounds only on `dParent` trees -/

section Piece
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign

variable {w : ℕ} (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (a : PrescribedPrimeGarden w)
  (Mk : Set (Stage1.CLVine a.prime.skeleton))

end Piece

end WaveTurbulence.Flower.MkSlotsB
