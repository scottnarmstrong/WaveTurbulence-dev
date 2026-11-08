/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassId2
public import WaveTurbulence.Foundations.Flower.MkSlotsI.Box
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoT1
public import WaveTurbulence.Foundations.Flower.MkSlotsI.Count
public import WaveTurbulence.Foundations.Flower.MkSlots.IntWeight

/-! # B3s-HELPER7 ClassId (part 3): the slot boxes and the consumed momenta of a member

For a member `y` of the run class (shapes `Φy = memShape a mk y hy`, `Φa = stShape …`):
* `clk_corr`: the clock sources of the outer slots correspond (root clocks equal; branch clocks with equal pins:
  β's `member_fixCap_pat`, `member_fix_unit_pat`, the representative's `hrepUP`; route cases as B3's
  `memShape_clkLayer`); `genSlotBox_member`: the member's general slot box is the representative's `genBoxAt`;
* **`member_topCut`**: the member's slot times on its pinned relaxed core domain with lower bounds satisfy the
  representative's `TopCut` (SlotObl revision 5), given the class-commonness of the lower bounds at the clock branches
  (`hlbclk`);
* **`member_hbox`**: the `hbox` of VBC4 for the box `genBoxAt … ∩ TopCut`;
* `ConsG`, `ConsCG`, `member_hcons`, **`member_hexp₀`**, **`member_hexpC`**: the consumed momenta (lattice points at
  base `0`, the cap momentum on cap pairs, the root label on root chain slots) and the superpositions of VBC4 from
  `SlotDataOK` and RSlot's `member_genSlot`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset TTree MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (anchProfiles chainW fixCore recLG IsCapPair capTreeOf)

namespace WaveTurbulence.Flower.MkSlotsI

/-- On a cap pair the slot momentum of every decoration is the cap root label. -/
theorem genDec_capPair {w d : ℕ} (S : Garden w) (hS : S.IsPlain) (J : Finset (Fin w))
    (hcap : ∀ j ∈ J, S.tree j = TTree.leaf) {roots : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration S d roots nfl) (q : SourcePair S) (hq : IsCapPair S hS J q) :
    κ.1 (q.firstLeaf hS).toNode = roots (capTreeOf S hS J q) := by
  unfold capTreeOf
  split_ifs with h1
  · exact MkSlots.IntWeight.genDec_cap S J hcap κ _ h1
  · have h2 : (q.secondLeaf hS).1.1 ∈ J := hq.resolve_left h1
    have e := κ.2.1.2 (q.secondLeaf hS)
    rw [pair_second hS q] at e
    exact e.symm.trans (MkSlots.IntWeight.genDec_cap S J hcap κ _ h2)

theorem clkOfNode_coupleLeafNode {w : ℕ} {S : Garden w} (hS : S.IsPlain) (p : SourcePair S) (j : Fin 2) :
    clkOfNode S (MkSlotsB.coupleLeafNode hS p j) = argSrc hS (.inl p) j := by
  fin_cases j <;> rfl

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain) (J : Finset (Fin (2 * R)))
  (hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf)
  (hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hy hG hcapA hcapY hrepUP in
/-- **The clock sources of the outer slots correspond**: root clocks are equal, branch clocks carry equal pins. -/
theorem clk_corr (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2) :
    (∃ r, argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s') i = .inl r ∧
        argSrc a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s') i
          = .inl r) ∨
      ∃ by' ba, argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s') i = .inr by' ∧
        argSrc a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s') i
          = .inr ba ∧
        fixCore y.1.data y.1.plain
            (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
            by' =
          fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) ba := by
  have hroute := congrFun (congrFun (memShape_route a mk y hy hG) s') i
  rcases hr' : (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route
      a.prime.prime.1 hG s' i with y' | j
  · rw [hr'] at hroute
    rw [(memShape a mk y hy).route_inl _ hG hroute,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_inl _ hG hr']
    rcases y' with r | c
    · exact Or.inl ⟨r, rfl, rfl⟩
    · refine Or.inr ⟨(memShape a mk y hy).br c,
        (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).br c, rfl, rfl, ?_⟩
      exact (MkSlotsB.member_fixCap_pat a mk y hy hG J hcapA hcapY pat t s hrepUP c).trans
        (MkSlotsB.fixCap_decoded_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
          (sourceLayer_reconstructs a) a.prime.decodes J pat t s _)
  · rw [hr'] at hroute
    rw [(memShape a mk y hy).route_inr _ hG hroute,
      (stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).route_inr _ hG hr']
    refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
    show fixCap _ J pat t s _ = fixCap _ J pat t s _
    rw [MkSlotsB.member_fix_unit_pat a mk y hy hG J hcapA hcapY pat t s hrepUP j _ (lower_mem _),
      hrepUP j _ (lower_mem _)]

include hy hG hcapA hcapY hrepUP in
/-- The clock pins of the outer slots are common to the run class. -/
theorem clkPin_member (tt : Fin (2 * R) → ℝ)
    (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2) :
    clkPin tt (fixCore y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s))
        (argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s') i) =
      clkPin tt (fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s))
        (argSrc a.prime.prime.1
          ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s')
          i) := by
  rcases clk_corr a mk y hy hG J hcapA hcapY pat t s hrepUP s' i with ⟨r, h1, h2⟩ | ⟨by', ba, h1, h2, h3⟩
  · rw [h1, h2]; rfl
  · rw [h1, h2]; exact h3

include hy hG hcapA hcapY hrepUP in
/-- **The member's general slot box is the representative's** `genBoxAt`. -/
theorem genSlotBox_member (tt : Fin (2 * R) → ℝ)
    (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    genSlotBox p (fun b => stateLayer y.1 (y.1.data.coreBranch y.1.plain b).toNode) y.1.plain tt
        (fixCore y.1.data y.1.plain
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s))
        ((memShape a mk y hy).iota y.1.plain hG s') =
      genSlotBox p (fun b => sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 b).toNode) a.prime.prime.1 tt
        (fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s))
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s') := by
  ext ts
  unfold genSlotBox
  simp only [Set.mem_ofPred_eq, clkPin_member a mk y hy hG J hcapA hcapY pat t s hrepUP tt s',
    memShape_slotBox a mk y hy hG s']

/-- The pin values of the pattern pins: `s`, or `t` at a root. -/
theorem fixCap_le_t {w : ℕ} {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    (hst : s ≤ t) {b : GBranch LG.garden.tree} {v : ℝ} (h : fixCap LG J pat t s b = some v) : s ≤ v ∧ v ≤ t := by
  rcases MkSlotsB.fixCap_value h with rfl | ⟨rfl, -, -⟩
  · exact ⟨le_rfl, hst⟩
  · exact ⟨hst, le_rfl⟩

include hy hG hcapA hcapY hrepUP in
/-- **The member's slot times satisfy the representative's `TopCut`** on the pinned relaxed core domain with the
lower bounds `lbS`, given the class-commonness of the lower bounds at the clock branches of the outer slots. -/
theorem member_topCut (hst : s < t)
    (hlbclk : ∀ (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) (i : Fin 2)
      (by' : GBranch y.1.skeleton.tree) (ba : GBranch a.prime.skeleton.tree),
      argSrc y.1.plain ((memShape a mk y hy).iota y.1.plain hG s') i = .inr by' →
      argSrc a.prime.prime.1
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s') i
        = .inr ba →
      MkSlotsB.lbS y.1.data y.1.plain
          (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s
          by' =
        MkSlotsB.lbS a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) s ba)
    (τ : GBranch y.1.skeleton.tree → ℝ)
    (hpin : MkSlotsB.PinnedAt (fixCore y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)) τ)
    (hlb : τ ∈ MkSlotsB.lbDomR (MkSlotsB.lbS y.1.data y.1.plain
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s) s))
    (s' : ReplacementSlot (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G) :
    TopCut a J pat t s
      ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG s')
      (slotTs y.1.plain (fun _ => t) τ ((memShape a mk y hy).iota y.1.plain hG s')) := by
  set Φy := memShape a mk y hy with hΦy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) with hΦa
  set LGy := layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) with hLGy
  -- the value of a pinned native top attached at a child of a branch is `s`
  have hval_s : ∀ (sl : ReplacementSlot a.prime.skeleton) (b : NativeClockBranch a.prime.data sl) (v : ℝ),
      MkSlotsB.NativeTop a.prime.data sl b →
      MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) sl b = some v →
      ∀ (ba : GBranch a.prime.skeleton.tree) (k : Fin 3),
        MkSlotsB.nativeClockNode a.prime.data a.prime.prime.1 sl b = ba.child k → v = s := by
    intro sl b v hb hv ba k hk
    have hTc := MkSlotsB.nativeTop_isChildOf a.prime.data a.prime.prime.1 sl b hb ba k hk
    have hTnr : (MkSlotsB.nativeBr a.prime.data a.prime.prime.1 sl b).1.2 ≠ [] := by
      obtain ⟨-, k', hk'⟩ := hTc; rw [hk']; simp
    rcases MkSlotsB.fixCap_value (show fixCap (recLG a) J pat t s (MkSlotsB.nativeBr a.prime.data a.prime.prime.1 sl b)
        = some v from hv) with h | ⟨-, h0, -⟩
    · exact h
    · exact absurd h0 hTnr
  -- a clock of the member is at least `s` whenever the representative carries a pinned native top below it
  have key : ∀ (i : Fin 2) (sl : ReplacementSlot a.prime.skeleton) (b : NativeClockBranch a.prime.data sl) (v : ℝ),
      argSrc a.prime.prime.1 (Φa.iota a.prime.prime.1 hG s') i = clkOfNode _
        (MkSlotsB.nativeClockNode a.prime.data a.prime.prime.1 sl b) →
      MkSlotsB.NativeTop a.prime.data sl b →
      MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) sl b = some v →
      (∀ ba, argSrc a.prime.prime.1 (Φa.iota a.prime.prime.1 hG s') i = .inr ba →
        fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) ba = none →
        ∃ x, MkSlotsB.lbS a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) s ba = some x ∧ v ≤ x) →
      v ≤ slotTs y.1.plain (fun _ => t) τ (Φy.iota y.1.plain hG s') i := by
    intro i sl b v hsrc hb hv hfree
    show v ≤ clockOf _ (fun _ => t) τ (argSrc y.1.plain (Φy.iota y.1.plain hG s') i)
    rcases clk_corr a mk y hy hG J hcapA hcapY pat t s hrepUP s' i with ⟨r, h1, h2⟩ | ⟨by', ba, h1, h2, h3⟩
    · rw [h1]
      exact (fixCap_le_t hst.le hv).2
    · rw [h1]
      show v ≤ τ by'
      rw [h2] at hsrc
      obtain ⟨k, hk⟩ := exists_child_of_clkOfNode hsrc.symm
      have hvs := hval_s sl b v hb hv ba k hk.symm
      rcases hfa : fixCore a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) ba with _ | u
      · obtain ⟨x, hx, hvx⟩ := hfree ba h2 hfa
        have hy' := hlbclk s' i by' ba h1 h2
        rw [hx] at hy'
        exact hvx.trans (hlb by' x hy').le
      · rw [← h3] at hfa
        rw [hpin.pin by' u hfa, hvs]
        exact (fixCap_le_t hst.le hfa).1
  cases s' with
  | inl q =>
    intro b v hb hv
    refine key b.1.1 (.inl (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))) b v ?_ hb hv ?_
    · exact (clkOfNode_coupleLeafNode a.prime.prime.1 _ b.1.1).symm
    · intro ba h2 hfa
      have hsrc := (clkOfNode_coupleLeafNode a.prime.prime.1 _ b.1.1).trans h2
      obtain ⟨k, hk⟩ := exists_child_of_clkOfNode hsrc
      exact MkSlotsB.lbComplete_lbS a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J pat t s
        (.inl (pairOfLeaf a.prime.skeleton a.prime.prime.1 (Φa.leaf (q.firstLeaf hG)))) b v ba k hb hv hk.symm hfa
  | inr c =>
    intro b v hb hv
    refine key 0 (.inr (Φa.br c)) b v rfl hb hv ?_
    intro ba h2 hfa
    exfalso
    obtain ⟨k, hk⟩ := exists_child_of_clkOfNode h2
    obtain ⟨q', hq', -⟩ := MkSlotsB.pinnedTop_freeClock_cases a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) J hcapA pat t s (.inr (Φa.br c)) b hb hv ba k hk.symm hfa
    exact Sum.inr_ne_inl hq'

end Class

end WaveTurbulence.Flower.MkSlotsI
