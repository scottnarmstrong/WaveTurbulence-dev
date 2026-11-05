/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerKind

/-!
# X2E-3, step 9: the gate's conditions on a flower graft

For flower graft data `D`: the layer-`p` cut of the flower graft is the top forest (`layerCutForest_flowerGraft`).
For `x : FlowerAt` at flower trees `tops` of flower sign `ζ`:
- `topOrder_toData`, `topCountBelow_toData`: the gate's counts are the counts of the trees `tops j`;
- `flowerKindOK_iff`: the gate's kind condition is `tops j ∈ kindTrees` (non-trivial `tops`);
- `patValid_iff`: the gate's pattern condition is `treePatValid` (patterns `plain`, `dRoot`);
- `attach_iff`: the gate's attached-order condition is the order bound on the lower components.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI
open scoped Classical

/-! ## Counts on a layered garden -/

theorem topCountBelow_eq_cntBelow {w : ℕ} (LG : LayeredGarden w) (p : ℕ) (hbound : ∀ a, LG.layer a ≤ p)
    (a : GNode LG.garden.tree) : LG.topCountBelow p a = cntBelow (layerCutForest LG p a.1.1) a.1.2 := by
  unfold LayeredGarden.topCountBelow cntBelow
  symm
  refine card_bij (fun q hq => (⟨(a.1.1, q), cutTree_branching_subset _ _ (mem_filter.mp hq).1⟩ :
    GBranch LG.garden.tree)) ?_ ?_ ?_
  · intro q hq
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_univ _, ⟨rfl, hq2⟩, (layerCut_branch_mem_iff LG p hbound ⟨(a.1.1, q), _⟩).mp hq1⟩
  · intro q _ q' _ h
    exact congrArg (fun z : GBranch LG.garden.tree => z.1.2) h
  · intro b hb
    obtain ⟨-, ⟨hj, hpfx⟩, hl⟩ := mem_filter.mp hb
    have hmem : b.1.2 ∈ (layerCutForest LG p a.1.1).branching := by
      rw [show a.1.1 = b.1.1 from hj]
      exact (layerCut_branch_mem_iff LG p hbound b).mpr hl
    exact ⟨b.1.2, mem_filter.mpr ⟨hmem, hpfx⟩, Subtype.ext (Prod.ext hj rfl)⟩

/-! ## Flower graft data -/

namespace FlowerGraftData

variable {Pm p : ℕ} {ζ : ℤˣ} (D : FlowerGraftData Pm p ζ)

theorem layerCutForest_flowerGraft : layerCutForest D.flowerGraft p = D.base.top := by
  have h : layerCutForest D.flowerGraft p = layerCutForest D.pairedGraft p := rfl
  rw [h, D.pairedGraft_eq, D.base.layerCutForest_graft]

theorem layer_le (a : GNode D.flowerGraft.garden.tree) : D.flowerGraft.layer a ≤ p :=
  Canon.layer_le_of_isCanonH D.flowerGraft_isCanonH a

end FlowerGraftData

/-! ## Flower data at given flower trees -/

section Gate

variable {Pm p : ℕ} {ζ : ℤˣ} {tops : Fin (2 * Pm) → FTree} (x : FlowerAt Pm p tops)
  (hsign : ∀ j, (tops j).sign = ζ)

theorem layerCut_toData : layerCutForest (x.toData hsign).flowerGraft p = ftop tops :=
  (x.toData hsign).layerCutForest_flowerGraft

theorem topOrder_toData (j : Fin (2 * Pm)) : (x.toData hsign).flowerGraft.topOrder p j = (tops j).order := by
  rw [← layerCutForest_order _ p (x.toData hsign).layer_le j, layerCut_toData, order_toTree]

theorem topCountBelow_toData (a : GNode (x.toData hsign).flowerGraft.garden.tree) :
    (x.toData hsign).flowerGraft.topCountBelow p a = cntBelow (tops a.1.1).toTree a.1.2 := by
  rw [topCountBelow_eq_cntBelow _ p (x.toData hsign).layer_le, layerCut_toData]

theorem mem_branching_of_top {j : Fin (2 * Pm)} {q : TTree.Path} (hq : q ∈ (tops j).toTree.branching) :
    q ∈ ((x.toData hsign).flowerGraft.garden.tree j).branching := by
  have hq' : q ∈ (layerCutForest (x.toData hsign).flowerGraft p j).branching := by
    rw [layerCut_toData]
    exact hq
  exact cutTree_branching_subset _ _ hq'

variable {x hsign} in
theorem nil_mem_branching {F : FTree} (hF : F ≠ FTree.flower) : ([] : TTree.Path) ∈ F.toTree.branching := by
  have hT := (ne_flower_iff F).mp hF
  cases h : F.toTree with
  | leaf => exact absurd h hT
  | node l m r => simp [TTree.branching]

variable (hF : ∀ j, tops j ≠ FTree.flower)

theorem isFlowerParent_toData_iff (b : GBranch (x.toData hsign).flowerGraft.garden.tree) :
    (x.toData hsign).flowerGraft.garden.IsFlowerParent b ↔ b.1.2 = ((tops b.1.1).flowerParent (hF b.1.1)).1.2 :=
  ((x.toData hsign).isFlowerParent_iff b).trans (exists_flower_step_iff hF b.1.1 b.1.2)

/-- The flower parent of tree `j`, as a branch of the flower graft. -/
def fpBranch (j : Fin (2 * Pm)) : GBranch (x.toData hsign).flowerGraft.garden.tree :=
  ⟨(j, ((tops j).flowerParent (hF j)).1.2), mem_branching_of_top x hsign ((tops j).flowerParent (hF j)).2⟩

include hF in
/-- **The kinds.** -/
theorem flowerKindOK_iff (N : ℕ) (kind : FlowerKind) :
    (x.toData hsign).flowerGraft.FlowerKindOK p N kind ↔ ∀ j, tops j ∈ kindTrees N kind := by
  cases kind with
  | X =>
    refine forall_congr' fun j => ?_
    change _ ↔ tops j ∈ Xset N
    rw [topOrder_toData, mem_Xset_iff (hF j)]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [order_eq_toTree]
    exact one_le_order_toTree (hF j)
  | Y =>
    refine forall_congr' fun j => ?_
    change _ ↔ tops j ∈ (Yind N).image rootOf
    rw [topOrder_toData, mem_Ytrees_iff (hF j)]
    refine and_congr_right fun _ => ⟨fun h k => ?_, fun h b hb k => ?_⟩
    · have hk := h ⟨(j, []), mem_branching_of_top x hsign (nil_mem_branching (hF j))⟩ rfl k
      rwa [topCountBelow_toData] at hk
    · rw [topCountBelow_toData]
      have e1 : (b.child k).1.1 = j := congrArg Prod.fst hb
      have e2 : (b.child k).1.2 = [k] := by
        change b.1.2 ++ [k] = [k]
        rw [congrArg Prod.snd hb]
        rfl
      rw [e1, e2]
      exact h k
  | W =>
    refine forall_congr' fun j => ?_
    change _ ↔ tops j ∈ (Wind N).image bottomOf
    rw [topOrder_toData, mem_Wtrees_iff (hF j)]
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h b hbj hfp => ?_⟩
    · obtain ⟨hsib, hlast⟩ := h (fpBranch x hsign hF j) rfl
        ((isFlowerParent_toData_iff x hsign hF _).mpr rfl)
      refine ⟨fun k hk => ?_, ?_⟩
      · have hnf : ¬ (x.toData hsign).flowerGraft.IsFlowerNode ((fpBranch x hsign hF j).child k) := by
          rw [(x.toData hsign).isFlowerNode_iff]
          exact hk
        have h' := hsib k hnf
        rwa [topCountBelow_toData] at h'
      · rwa [topCountBelow_toData] at hlast
    · have hb : b.1.2 = ((tops j).flowerParent (hF j)).1.2 := by
        have h' := (isFlowerParent_toData_iff x hsign hF b).mp hfp
        rwa [hbj] at h'
      obtain ⟨hsib, hlast⟩ := h
      refine ⟨fun k hnf => ?_, ?_⟩
      · rw [topCountBelow_toData]
        have e1 : (b.child k).1.1 = j := hbj
        have e2 : (b.child k).1.2 = ((tops j).flowerParent (hF j)).1.2 ++ [k] := by
          change b.1.2 ++ [k] = _
          rw [hb]
        rw [e1, e2]
        refine hsib k fun he => hnf ?_
        rw [(x.toData hsign).isFlowerNode_iff]
        change (b.child k).1.2 = (tops (b.child k).1.1).flowerPath
        rw [e1, e2]
        exact he
      · rw [topCountBelow_toData]
        have e1 : b.toNode.1.1 = j := hbj
        have e2 : b.toNode.1.2 = ((tops j).flowerParent (hF j)).1.2 := hb
        rw [e1, e2]
        exact hlast

include hF in
/-- **The patterns.** -/
theorem patValid_iff (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot) :
    (∀ j, (x.toData hsign).flowerGraft.PatValid p j pat) ↔ ∀ j, treePatValid (tops j) (hF j) pat := by
  rcases hpat with rfl | rfl
  · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  · refine forall_congr' fun j => ⟨?_, fun h0 => ?_⟩
    · rintro ⟨b, hb, hnf⟩ h0
      apply hnf
      rw [isFlowerParent_toData_iff x hsign hF b]
      have e1 : b.1.1 = j := congrArg Prod.fst hb
      have e2 : b.1.2 = [] := congrArg Prod.snd hb
      rw [e2, e1]
      exact h0.symm
    · refine ⟨⟨(j, []), mem_branching_of_top x hsign (nil_mem_branching (hF j))⟩, rfl, fun hfp => h0 ?_⟩
      exact ((isFlowerParent_toData_iff x hsign hF _).mp hfp).symm

/-- **The attached orders.** -/
theorem attach_iff (Natt : ℕ) :
    (∀ u ∈ (x.toData hsign).flowerGraft.attachNodes p, (x.toData hsign).flowerGraft.attachedOrder p u ≤ Natt) ↔
      ∀ B, (x.low B).garden.order ≤ Natt := by
  have h := (x.toData hsign).flowerGraft_isTrunc_iff (∑ j, (tops j).order) Natt
  have htop : ∀ j, (x.toData hsign).flowerGraft.topOrder p j ≤ ∑ j, (tops j).order := fun j => by
    rw [topOrder_toData]
    exact single_le_sum (f := fun j => (tops j).order) (fun _ _ => Nat.zero_le _) (mem_univ j)
  have htop' : ∀ j, ((x.toData hsign).base.top j).order ≤ ∑ j, (tops j).order := fun j => by
    change (tops j).toTree.order ≤ _
    rw [order_toTree]
    exact single_le_sum (f := fun j => (tops j).order) (fun _ _ => Nat.zero_le _) (mem_univ j)
  exact ⟨fun ha => (h.mp ⟨htop, ha⟩).2, fun hb => (h.mpr ⟨htop', hb⟩).2⟩

end Gate

end WaveTurbulence.X2E
