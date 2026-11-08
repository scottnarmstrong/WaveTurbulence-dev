/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.ClassForm
public import WaveTurbulence.Foundations.Flower.MkSlotsI.Count
public import WaveTurbulence.Foundations.Flower.MkSlotsB.EngDR
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeo
public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelClk

/-! # B3s-HELPER7 AsmG (1): the hinge data of the general piece on the relaxed pinned domain

The engine's hinge hypothesis `hhinge` is δ's unpinned-form `MkSlotsS.HHkPropD` on
`Dom = domOf π tt ∩ MkSlotsB.pinSet π.fix` for the general piece `π = pieceGenAt … a Mk dag` at `Mk = classMk mkF a`.
It follows from main's `HHkProp` of the normalized piece `a.normalizedPiece P.d Mk` by β's shift method
`MkSlotsB.hHkPropD_of_hHkProp`, whose three pin hypotheses are:

* `hpv` (pins in their layer windows, below the root time `t`): β's `MkSlotsB.fixOf_val`;
* `hpm` (a pinned child carries a pin `≤` its pinned parent's): β's `MkSlotsB.fixOf_mono_child`;
* `hclk0` (the unit clocks at branches are free), **`fixOf_unitClock`**: the hinge clock by β's
  `MkSlotsB.fixOf_hinge`; the two lower crown clocks `u21, u22` by the new **`fixCap_lowerChild_unit`**: a pinned
  vertex at a lower crown child `u.lower.child i` of a unit `u` is protected and lies in the near region of `u.lower`,
  so the vine of `𝒱₀♮` through `u.lower` inside `u` (`RedSplice.unitBlocks_soundMk`) is marked through its NON-upper
  atom `u.lower` (**`clVine_upper_ne_lower`**: no vine inside a (CL) block has the block's lower joint as its upper
  joint — the joint slots `{1,2}`/`{2,3}` of a vine's upper joint are not inside the slots `{0,1}`/`{0,3}` of the
  block's lower joint), contradicting `markI ⊆ mkF`.

Main export: **`hHkPropD_pieceGenAt`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineEstS3
  WaveTurbulence.VineEstS3.FS WaveTurbulence.RepAnalytic WaveTurbulence.VineAlign
open WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.RedSplice (stSt unitBlocks)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ}

/-- **No vine inside a (CL) block has the block's lower joint as its upper joint.** The upper joint of a vine has
no internal parent, so its internal slots are `{1,2}` or `{2,3}`; the lower joint of a (CL) block has its parent
inside, so its slots are `{0,1}` or `{0,3}`; slot `2` of the vine's upper joint would be a slot of the block's lower
joint (the vine lies inside the block). -/
theorem clVine_upper_ne_lower {G : Garden w} (u : RedSplice.CLBlock G) (c : Stage1.CLVine G)
    (hsub : c.atoms ⊆ u.atoms) : c.upper ≠ u.lower := by
  intro heq
  obtain ⟨X, hV⟩ := c.isVine
  have hB := hV.1
  have hc := Mole.joint_no_parent_slots G hB.2.1 hB.2.2.2.2.1 hB.2.2.2.2.2.1 c.notParentUpper
  have hu := Mole.joint_with_parent_slots G u.isBlock.2.2.1 u.isBlock.2.2.2.2.2.2.1 u.isBlock.2.2.2.2.2.2.2.1
    u.cl.2
  have h2 : (2 : Fin 4) ∈ Mole.internalPositions G c.atoms c.upper := by
    rcases hc with h | h <;> rw [h] <;> decide
  have h2' : (2 : Fin 4) ∈ Mole.internalPositions G u.atoms u.lower := by
    obtain ⟨x, hx, hg, hp⟩ := (Mole.mem_internalPositions G).mp h2
    exact (Mole.mem_internalPositions G).mpr ⟨x, heq ▸ hx, ⟨hsub hg.1, hsub hg.2⟩, hp⟩
  rcases hu with h | h <;> rw [h] at h2' <;> revert h2' <;> decide

/-- **No lower crown child of a unit of the piece carries a pin.** `a` is a prescribed point, `mkF` a fine marking
containing `markI`; `u` is a unit of `unitBlocks` at `classMk mkF a` and `y` the skeleton branch at a child
`u.lower.child i` of its lower joint. -/
theorem fixCap_lowerChild_unit {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) {u : RedSplice.CLBlock a.prime.skeleton}
    (hu : u ∈ unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a)) {y : GBranch a.prime.skeleton.tree}
    (i : Fin 3) (hy : y.toNode = u.lower.child i) :
    fixCap a.layered J pat t s (a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes y) = none := by
  obtain ⟨c, hc, hlc, hcu⟩ := RedSplice.unitBlocks_soundMk hu u.lower u.isBlock.2.2.1
  rw [RedSplice.mem_vinesV0] at hc
  obtain ⟨hc0, hcMk⟩ := hc
  by_contra hpin
  have hpin' := Option.ne_none_iff_isSome.1 hpin
  have hm : c ∈ markI J pat t s kSel a.prime := by
    refine ⟨RedSplice.vinesV0_subset _ _ hc0, u.lower, hlc, fun h => clVine_upper_ne_lower u c hcu h.symm, _,
      MkSlots.mem_protI_of_fixCap hpin', ?_⟩
    apply ProtGeo.mem_nearRegion_child i
    rw [← hy]
    exact ProtGeo.skelAddr_mem_ownRegion _ _ y
  exact hcMk ⟨hsub a.prime hm, hc0⟩

/-- **The unit clocks of the piece at branches are free** (`hclk0` of β's `MkSlotsB.hHkPropD_of_hHkProp`): the hinge
clock (`MkSlotsB.fixOf_hinge`) and the lower crown clocks `u21, u22` (`fixCap_lowerChild_unit`) of every unit carry
no pin, for every pattern. -/
theorem fixOf_unitClock {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (hsub : ∀ {LG : LayeredGarden w} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden w) (j : Fin (unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a)).length)
    (i : Fin 3) (c : GBranch (MkSlots.stA mkF a).G.tree)
    (h : (VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)).hclk
      (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)) j i =
        Sum.inr c) :
    MkSlots.fixOf J pat t s mkF a c = none := by
  set Φ := VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)
  set hd := VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a)
  have hmem : VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a) j ∈
      unitBlocks a.prime.skeleton a.totalSigma (classMk mkF a) := List.get_mem _ _
  fin_cases i
  · change Sum.inr (Φ.hinge hd j) = Sum.inr c at h
    have hc : c = Φ.hinge hd j := (Sum.inr_injective h).symm
    have hh : c ∈ (MkSlots.stA mkF a).hinges := by
      rw [← VineB.stShape_hingesMk (Mole.garden_isMolecule a.prime.skeleton), hc]
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    exact MkSlotsB.fixOf_hinge J pat t s mkF a kSel hsub c hh
  · change VineB.nodeClk _ (Φ.hmom hd j 2) = Sum.inr c at h
    have hn := MkSlotsS.nodeClk_eq_inr h
    have h2 := Φ.node_hmom hd j 2
    rw [hn] at h2
    have h2' : Φ.node c.toNode =
        (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a) j).lower.child
          (VineB.regionOf (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
            (classMk mkF a) j)).positive := h2
    exact fixCap_lowerChild_unit pat t s kSel mkF hsub a hmem _ ((Φ.br_node c).trans h2')
  · change VineB.nodeClk _ (Φ.hmom hd j 3) = Sum.inr c at h
    have hn := MkSlotsS.nodeClk_eq_inr h
    have h2 := Φ.node_hmom hd j 3
    rw [hn] at h2
    have h2' : Φ.node c.toNode =
        (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (classMk mkF a) j).lower.child
          (VineB.regionOf (VineB.unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma
            (classMk mkF a) j)).negative := h2
    exact fixCap_lowerChild_unit pat t s kSel mkF hsub a hmem _ ((Φ.br_node c).trans h2')

/-- **The hinge data of the general piece on the engine's domain** (`hhinge` of the engine with
`Dom := domOf π tt ∩ MkSlotsB.pinSet π.fix`, `π = pieceGenAt … a Mk dag`, `Mk = classMk mkF a`): main's unpinned
`HHkProp` of the normalized piece gives δ's `MkSlotsS.HHkPropD` on `Dom`, by β's shift method
`MkSlotsB.hHkPropD_of_hHkProp` (pins `fixOf_val`, `fixOf_mono_child`; free unit clocks `fixOf_unitClock`). -/
theorem hHkPropD_pieceGenAt (P : WTParams) {R : ℕ} {p : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
    (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (a : PrescribedPrimeGarden (2 * R)) (hG : CapGeo a.layered J p) (hpat : CapPatValid a.layered J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf a.layered.garden.tree, IsCapFlower a.layered J ℓ ∧ ℓ.1.1 = j)
    (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (Mk : Set (Stage1.CLVine a.prime.skeleton)) (hMk : Mk = classMk mkF a)
    (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (selSk : GenDecoration (stSt a.prime.skeleton a.totalSigma Mk).G P.d roots 0 → Prop)
    (Hk : Fin (unitBlocks a.prime.skeleton a.totalSigma Mk).length → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ)
    (H : HingeFam (Fin (unitBlocks a.prime.skeleton a.totalSigma Mk).length) P.d)
    (hHk : HHkProp (a.normalizedPiece P.d Mk) (fun _ => t) 0 roots selSk
      ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).hclk
        (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk))
      ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).hmom
        (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)) Hk H) :
    MkSlotsS.HHkPropD (pieceGenAt P J pat t s kSel σ Rs a Mk dag).toStage1PieceD (fun _ => t) 0 roots selSk
      (domOf (pieceGenAt P J pat t s kSel σ Rs a Mk dag) (fun _ => t) ∩
        MkSlotsB.pinSet (pieceGenAt P J pat t s kSel σ Rs a Mk dag).fix)
      ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).hclk
        (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk))
      ((VineB.stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk).hmom
        (VineB.unitBlkMk_disj (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma Mk)) Hk H := by
  subst hMk
  intro κ hsel τ hτ j c hc
  refine MkSlotsB.hHkPropD_of_hHkProp (pieceGenAt P J pat t s kSel σ Rs a (classMk mkF a) dag) (fun _ => t) 0 roots
    selSk _ _ Hk H ?_ ?_ ?_ hHk κ hsel τ hτ.1.1 hτ.2 j c hc
  · intro b v hb
    exact MkSlotsB.fixOf_val J pat t s mkF a hG hpat hroot hs ht b v hb
  · intro b b' v v' hb hb' hcc
    exact MkSlotsB.fixOf_mono_child J pat t s mkF a hs.2.le hcc hb hb'
  · intro j' i c' h
    exact fixOf_unitClock pat t s kSel mkF hsub a j' i c' h

end WaveTurbulence.Flower.MkSlotsI
