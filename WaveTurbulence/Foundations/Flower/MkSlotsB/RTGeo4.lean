/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.RTGeo3
public import WaveTurbulence.Foundations.Flower.MkSlotsO.Split

/-! # B3s-HELPER3 B5(ii) geometry (R188), part 4: the root-trace slots from HELPER8's predicates

* **`rtChain_of_pred`**: a chain slot with a pinned native branch and no native node on a capped stem is a
  root-trace chain slot (`RTChain`): the pin is the `dChild i` pin of the chain TOP `r`, child `i` of a CORE capped
  flower parent `F = core β` (a capped flower parent, a `dRoot` root or a `dParent` pin would be on a capped stem; a
  pinned non-top chain branch would have a capped flower parent as native parent);
* **`rtCouple_of_pred`**: a non-cap leaf-pair slot with a pinned native branch is a root-trace couple slot
  (`RTCouple`, `Rt = rtRoots`: the pinned roots, possibly both);
* **`not_selNat_cpl`**: a non-cap leaf-pair slot carries no selected native vertex (selected vertices are on the
  capped stems, the native couple of a non-cap pair is off them). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence WaveTurbulence.LGSpine TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-- A native branch of a chain slot is never a core branch. -/
theorem chainBr_ne_core {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (γ' : GBranch S.tree)
    (y : GBranch (decodedTree (D.tree γ') (nodeSign S.sig γ'.1)).tree) (β' : GBranch S.tree) :
    (D.coreBranch hS β').toNode ≠ (nativeBr D hS (.inr γ') y).toNode := by
  intro he
  have h1 := slotOf_nativeBr D hS (.inr γ') y
  rw [← he, slotOf_core] at h1
  obtain rfl := Sum.inr_injective h1
  have h2 := congrArg (fun z : GNode (D.forest hS) => z.1.2) he
  change (inflatedPosition S D.tree β'.toNode).2 ++ (D.tree β').lonePath =
    (inflatedPosition S D.tree β'.toNode).2 ++ y.1.2 at h2
  have h3 := List.append_cancel_left h2
  let ℓ : GLeaf (decodedTree (D.tree β') (nodeSign S.sig β'.1)).tree :=
    ⟨(y.1.1, (D.tree β').lonePath), by
      have hm := PL234.lonePath_mem_leaves (D.tree β') (nodeSign S.sig β'.1)
      have hy : y.1.1 = 0 := Subsingleton.elim _ _
      show (D.tree β').lonePath ∈ ((decodedTree (D.tree β') (nodeSign S.sig β'.1)).tree y.1.1).leaves
      rw [hy]; exact hm⟩
  exact VineB.SpliceShape.leaf_ne_branch (v := y) (ℓ := ℓ) (Subtype.ext (Prod.ext rfl h3))

/-- **(1) A chain slot with a pinned native branch and no native stem node is a root-trace chain slot.** -/
theorem rtChain_of_pred {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ)
    (hcan : IsCanonGC (p + 1) a.layered) (hJ : J.card = R) (hG : CapGeo a.layered J p)
    (hpat : CapPatValid a.layered J pat p) (hirr : a.layered.garden.Irreducible)
    (sl : ReplacementSlot a.prime.skeleton) (hsl : ∃ β, sl = .inr β)
    (hpin : MkSlotsO.HasPinNative a J pat t s kSel σ sl) (hst : ¬ MkSlotsO.HasStemNative a J pat t s kSel σ sl) :
    ∃ γ', sl = .inr γ' ∧ RTChain a J pat t s p γ' := by
  have hR := rtRec_of (p := p) a J pat hcan hJ hG hpat hirr
  obtain ⟨γ', rfl⟩ := hsl
  obtain ⟨qb, hqb⟩ := hpin
  have hqb' : (fixCap (recLG a) J pat t s (nativeBr a.prime.data a.prime.prime.1 (.inr γ') qb)).isSome := hqb
  -- no native chain branch is on a capped stem
  have hstem : ∀ y : GBranch (decodedTree (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).tree,
      ¬ OnCapStem (recLG a) J (nativeBr a.prime.data a.prime.prime.1 (.inr γ') y).toNode := by
    intro y hy
    refine hst ⟨GBranch.toNode (tree := (decodedTree (a.prime.data.tree γ')
      (nodeSign a.prime.skeleton.sig γ'.1)).tree) y, fun β' he => ?_, _, hy, rfl⟩
    exact chainBr_ne_core a.prime.data a.prime.prime.1 γ' y β' (he.symm.trans (Subtype.ext rfl))
  -- the chain is nontrivial
  have h0 : (a.prime.data.tree γ').lonePath ≠ [] := by
    intro h0
    have hq2 := qb.2
    rw [show ((decodedTree (a.prime.data.tree γ') (nodeSign a.prime.skeleton.sig γ'.1)).tree qb.1.1) =
      (a.prime.data.tree γ').plug (nodeSign a.prime.skeleton.sig γ'.1) TTree.leaf from rfl,
      (lonePath_nil_iff _ _).mp h0] at hq2
    simp [TTree.branching] at hq2
  set b := nativeBr a.prime.data a.prime.prime.1 (.inr γ') qb with hbdef
  have hbaddr : b.1 = addrExt (inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode) qb.1.2 := rfl
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hqb'
  rcases fixCap_cases hv with ⟨hc, -⟩ | ⟨-, -, hb0, -⟩ | ⟨-, -, ⟨C, hC, hCb⟩, -⟩ | ⟨i, -, hpi, ⟨c, hc, h1, h2⟩, -⟩
  · exfalso
    obtain ⟨ℓ, hℓ, hd⟩ := cfp_isDesc_flower hc
    exact hstem qb ⟨ℓ, hℓ, hd⟩
  · exfalso
    obtain ⟨ℓ, hℓ, hℓj⟩ := hR.root _ (branch_not_cap hR.geo b)
    refine hstem qb ⟨ℓ, hℓ, hℓj.symm, ?_⟩
    show b.1.2 <+: ℓ.1.2
    rw [hb0]; exact List.nil_prefix
  · exfalso
    obtain ⟨ℓ, hℓ, hd⟩ := cfp_isDesc_flower hC
    obtain ⟨g1, k, g2⟩ := hCb
    have hbC : b.toNode.IsDesc C.toNode := ⟨g1.symm, ⟨[k], g2.symm⟩⟩
    exact hstem qb ⟨ℓ, hℓ, isDesc_trans hbC hd⟩
  · -- `dChild i`: the pinned branch is the chain top, child `i` of a core capped flower parent
    have hcaddr : c.1 = (b.1.1, b.1.2.dropLast) := by
      rw [h2, List.dropLast_concat, h1]
    have hq0 : qb.1.2 = [] := by
      by_contra hne
      let y := GNode.parent (tree := (decodedTree (a.prime.data.tree γ')
        (nodeSign a.prime.skeleton.sig γ'.1)).tree) qb.toNode hne
      have hyc : nativeBr a.prime.data a.prime.prime.1 (.inr γ') y = c := by
        apply Subtype.ext
        rw [hcaddr]
        show addrExt (inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode) qb.1.2.dropLast = _
        rw [hbaddr]
        simp only [addrExt]
        rw [List.dropLast_append_of_ne_nil hne]
      obtain ⟨ℓ, hℓ, hd⟩ := cfp_isDesc_flower hc
      exact hstem y (hyc ▸ ⟨ℓ, hℓ, hd⟩)
    have hr1 : b.1 = inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode := by
      rw [hbaddr, hq0]; simp [addrExt]
    have hγnr : γ'.1.2 ≠ [] := by
      intro hr
      have hb2 : b.1.2 = [] := by
        rw [hr1]
        have : inflatedPosition a.prime.skeleton a.prime.data.tree γ'.toNode = γ'.toNode.1 := by
          rw [inflatedPosition]; simp only [show γ'.toNode.1.2 = [] from hr, ↓reduceDIte]
        rw [this]; exact hr
      rw [h2] at hb2; simp at hb2
    let β := γ'.toNode.parent hγnr
    let k := γ'.1.2.getLast hγnr
    have hγ : γ'.toNode = β.child k := (Skeleton.child_parent γ'.toNode hγnr).symm
    have hbat : b.toNode = (a.prime.data.coreBranch a.prime.prime.1 β).child k := by
      have ha := IntGeo.attachedNode_nonroot a.prime.data a.prime.prime.1 γ'.toNode hγnr
      exact (Subtype.ext hr1).trans ha
    have hv' := congrArg Subtype.val hbat
    have e1 : b.1.1 = (a.prime.data.coreBranch a.prime.prime.1 β).1.1 := by
      have h := congrArg Prod.fst hv'; exact h
    have e2 : b.1.2 = (a.prime.data.coreBranch a.prime.prime.1 β).1.2 ++ [k] := by
      have h := congrArg Prod.snd hv'; exact h
    have hcβ : c = a.prime.data.coreBranch a.prime.prime.1 β := by
      apply Subtype.ext
      rw [hcaddr, e2, List.dropLast_concat, e1]
    have hik : i = k := by
      have := h2.symm.trans e2
      rw [hcβ] at this
      exact (List.singleton_inj.mp (List.append_inj' this rfl).2)
    subst hik
    have hF : IsCapFlowerParent (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β) := hcβ ▸ hc
    have hpatβ : pat β.1.1 = FixPat.dChild k := by
      rw [← hpi, e1]
      exact (congrArg pat (inflatedPosition_index a.prime.skeleton a.prime.data.tree β.toNode)).symm
    have hnc : ∀ β' : GBranch a.prime.skeleton.tree,
        (a.prime.data.coreBranch a.prime.prime.1 β').toNode ≠ b.toNode :=
      chainBr_ne_core a.prime.data a.prime.prime.1 γ' qb
    refine ⟨γ', rfl, ?_⟩
    exact
      { two_le := rtc_two_le a γ' h0
        wf := rtc_wf a γ'
        pins := rtc_pins a J pat t s hR β γ' k b hF hpatβ hbat hr1
        layer_le := rtc_layer_le a J pat hR γ'
        layer_root := rtc_layer_root a J pat hR β γ' k b hF hpatβ hbat hr1
        layer_lone := rtc_layer_lone a γ'
        amb := rtc_amb a J pat hR γ'
        genΘs_one := rtc_genΘs_one a J pat hR β γ' k b hF hbat hr1
        selNative_empty := rtc_selNative_empty a J pat hR β γ' k b hF hbat hr1
        chainW_eq := rtc_chainW_eq a J pat hR γ'
        clk0 := rtc_clk0 a J pat t s β γ' k hF hγ
        clkLayer0 := rtc_clkLayer0 a J pat hR β γ' k hF hγ
        free := rtc_free a J pat t s hR β γ' k b hF hbat hnc hr1
        nonroot := rtc_nonroot a β γ' k hγ
        notSelAdj := rtc_notSelAdj a J pat β γ' k hpatβ hγ
        prot := rtc_prot a J pat t s hR β γ' k b hF hpatβ hbat hnc hr1
        leafwise := rtc_leafwise a J pat hR β γ' k b hF hbat hr1
        front_card := rtc_front_card a γ' }

/-- **(2) A non-cap leaf-pair slot with a pinned native branch is a root-trace couple slot** (the pinned roots
`Rt = rtRoots`). -/
theorem rtCouple_of_pred {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ)
    (hcan : IsCanonGC (p + 1) a.layered) (hJ : J.card = R) (hG : CapGeo a.layered J p)
    (hpat : CapPatValid a.layered J pat p) (hirr : a.layered.garden.Irreducible)
    (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t)
    (sl : ReplacementSlot a.prime.skeleton) (hcpl : MkSlotsO.IsCplSlot a J pat t s kSel σ sl)
    (hpin : MkSlotsO.HasPinNative a J pat t s kSel σ sl) :
    ∃ (q' : SourcePair a.prime.skeleton) (Rt : Fin 2 → Prop), sl = .inl q' ∧ RTCouple a J pat t s p q' Rt := by
  have hR := rtRec_of (p := p) a J pat hcan hJ hG hpat hirr
  obtain ⟨q', rfl, hnc⟩ := hcpl
  obtain ⟨qb, hqb⟩ := hpin
  have hqb' : (fixCap (recLG a) J pat t s (cbr a q' qb)).isSome := hqb
  obtain ⟨h0, -⟩ := rcp_pinned_root a J pat t s hR q' hnc qb hqb'
  have hj : rtRoots a J pat t s q' qb.1.1 := by
    refine ⟨by rw [← h0]; exact qb.2, ?_⟩
    have heq : (⟨(qb.1.1, []), by rw [← h0]; exact qb.2⟩ : GBranch (decodedCouple (a.prime.data.couple q')).tree) =
        qb := Subtype.ext (Prod.ext rfl h0.symm)
    show (fixCap (recLG a) J pat t s (cbr a q' _)).isSome
    rw [heq]; exact hqb'
  refine ⟨q', rtRoots a J pat t s q', rfl, ?_⟩
  exact
    { rt := ⟨qb.1.1, hj⟩
      notCap := hnc
      wf := rcp_wf a q'
      pins := rcp_pins a J pat t s hR q' hnc
      layer_le := rcp_layer_le a J pat hR q'
      root_pinned := rcp_root_pinned a J pat t s hR q'
      root_le := rcp_root_le a J pat hR q'
      amb := rcp_amb a J pat hR q'
      genΘs_one := rcp_genΘs_one a J q' hnc
      selNative_empty := rcp_selNative_empty a J q' hnc
      chainW_eq := rcp_chainW_eq a J pat hR q' hnc
      notSelAdj := rcp_notSelAdj a J pat t s hR q' hnc
      prot := rcp_prot a J pat t s q' qb.1.1 hj
      leafwise := rcp_leafwise a J pat hR q' hnc
      front_card := rcp_front_card a q'
      box := rcp_box a J pat t s hR q' hnc ht hs }

/-- **(3) A non-cap leaf-pair slot carries no selected native vertex.** -/
theorem not_selNat_cpl {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ)
    (sl : ReplacementSlot a.prime.skeleton) (hcpl : MkSlotsO.IsCplSlot a J pat t s kSel σ sl) :
    ¬ MkSlotsO.HasSelNat a J pat t s kSel σ sl := by
  obtain ⟨q', rfl, hnc⟩ := hcpl
  rintro ⟨y, -, v, hv, hve⟩
  have hst := (selSetCap_onStem hv).2
  have he : v.toNode = (nativeCoupleForest a.prime.data a.prime.prime.1 q').nodeEmbedding y := Subtype.ext hve
  rw [he] at hst
  exact (rcp_noFlower a J q' hnc y.1.1).not_onCapStem (root_isDesc_node _ _ q' y) hst

end WaveTurbulence.Flower.MkSlotsB
