/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoEdge
public import WaveTurbulence.Foundations.Spine.PL234Draft.GlueTree

/-! # B3s-HELPER3 B4 (pattern R-core 2): the pattern pins at a core branch, read on the skeleton

On the reconstruction `LG = layeredReconstruction D hS layer hLayer` (cap trees single leaves), the pattern pins at a
core branch `D.coreBranch hS b` are decided by four predicates (`fixCap_congr`):
* capped flower parent (B3s's R-core);
* root (`core_root_iff`: `b` a skeleton root with trivial chain);
* has a capped-flower-parent child (`dParent`; `hasCfpChild_core_iff`: the top attached at a skeleton child `b.child i`
  is a capped flower parent — for a branch child iff its chain is trivial and its core is one
  (`cfp_attached_branch_iff`; the top of a non-trivial chain never is, `chainTop_not_cfp`), for a leaf child iff the
  native couple satisfies `RootCfpG` (`cfp_nativeRoot_iff`));
* is child `i` of a capped flower parent (`dChild i`; `childOfCfp_core_iff`: trivial chain, last step `i`, the core of
  the skeleton parent a capped flower parent — the terminal node of a non-trivial chain never is,
  `terminal_not_cfp`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntGeo
open WaveTurbulence.Flower.MkSlots.IntRest

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-! ## `fixCap` is decided by four predicates -/

/-- **Congruence of the pattern pins**: same tree, same four predicates ⇒ same pin. -/
theorem fixCap_congr {LG₁ LG₂ : LayeredGarden w} (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (B₁ : GBranch LG₁.garden.tree) (B₂ : GBranch LG₂.garden.tree) (htree : B₁.1.1 = B₂.1.1)
    (hcfp : IsCapFlowerParent LG₁ J B₁ ↔ IsCapFlowerParent LG₂ J B₂)
    (hroot : B₁.1.2 = [] ↔ B₂.1.2 = [])
    (hpar : (∃ c, IsCapFlowerParent LG₁ J c ∧ c.IsChildOf B₁) ↔ ∃ c, IsCapFlowerParent LG₂ J c ∧ c.IsChildOf B₂)
    (hch : ∀ i : Fin 3, (∃ c, IsCapFlowerParent LG₁ J c ∧ B₁.1.1 = c.1.1 ∧ B₁.1.2 = c.1.2 ++ [i]) ↔
      ∃ c, IsCapFlowerParent LG₂ J c ∧ B₂.1.1 = c.1.1 ∧ B₂.1.2 = c.1.2 ++ [i]) :
    fixCap LG₁ J pat t s B₁ = fixCap LG₂ J pat t s B₂ := by
  obtain ⟨x, hx1⟩ : ∃ x, pat B₁.1.1 = x := ⟨_, rfl⟩
  have hx2 : pat B₂.1.1 = x := htree ▸ hx1
  unfold fixCap
  by_cases h : IsCapFlowerParent LG₁ J B₁
  · simp only [h, hcfp.mp h, ↓reduceIte]
  · simp only [h, (not_congr hcfp).mp h, ↓reduceIte, hx1, hx2]
    cases x with
    | plain => rfl
    | dRoot =>
      by_cases hr : B₁.1.2 = []
      · simp only [hr, hroot.mp hr, ↓reduceIte]
      · simp only [hr, (not_congr hroot).mp hr, ↓reduceIte]
    | dParent =>
      by_cases hr : ∃ c, IsCapFlowerParent LG₁ J c ∧ c.IsChildOf B₁
      · simp only [hr, hpar.mp hr, ↓reduceIte]
      · simp only [hr, (not_congr hpar).mp hr, ↓reduceIte]
    | dChild i =>
      by_cases hr : ∃ c, IsCapFlowerParent LG₁ J c ∧ B₁.1.1 = c.1.1 ∧ B₁.1.2 = c.1.2 ++ [i]
      · simp only [hr, (hch i).mp hr, ↓reduceIte]
      · simp only [hr, (not_congr (hch i)).mp hr, ↓reduceIte]

/-- A pinned branch that is not pinned by a pattern clause is unpinned: the converse reading of `fixCap`. -/
theorem fixCap_none_of {LG : LayeredGarden w} (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (B : GBranch LG.garden.tree) (hcfp : ¬ IsCapFlowerParent LG J B)
    (hroot : pat B.1.1 = FixPat.dRoot → B.1.2 ≠ [])
    (hpar : pat B.1.1 = FixPat.dParent → ¬ ∃ c, IsCapFlowerParent LG J c ∧ c.IsChildOf B)
    (hch : ∀ i : Fin 3, pat B.1.1 = FixPat.dChild i →
      ¬ ∃ c, IsCapFlowerParent LG J c ∧ B.1.1 = c.1.1 ∧ B.1.2 = c.1.2 ++ [i]) :
    fixCap LG J pat t s B = none := by
  cases h : fixCap LG J pat t s B with
  | none => rfl
  | some v =>
    exfalso
    rcases fixCap_cases h with ⟨hc, -⟩ | ⟨-, hp, h0, -⟩ | ⟨-, hp, hc, -⟩ | ⟨i, -, hp, hc, -⟩
    · exact hcfp hc
    · exact hroot hp h0
    · exact hpar hp hc
    · exact hch i hp hc

/-- The four predicates of a pinned-free branch from `fixCap … = none`. -/
theorem preds_of_fixCap_none {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {B : GBranch LG.garden.tree} (h : fixCap LG J pat t s B = none) :
    ¬ IsCapFlowerParent LG J B ∧ (pat B.1.1 = FixPat.dRoot → B.1.2 ≠ []) ∧
      (pat B.1.1 = FixPat.dParent → ¬ ∃ c, IsCapFlowerParent LG J c ∧ c.IsChildOf B) ∧
      (∀ i : Fin 3, pat B.1.1 = FixPat.dChild i →
        ¬ ∃ c, IsCapFlowerParent LG J c ∧ B.1.1 = c.1.1 ∧ B.1.2 = c.1.2 ++ [i]) := by
  unfold fixCap at h
  by_cases hc : IsCapFlowerParent LG J B
  · simp only [hc, ↓reduceIte] at h; exact absurd h (by simp)
  simp only [hc, ↓reduceIte] at h
  refine ⟨hc, fun hp h0 => ?_, fun hp hq => ?_, fun i hp hq => ?_⟩
  · rw [hp] at h; simp only [h0, ↓reduceIte] at h; exact absurd h (by simp)
  · rw [hp] at h; simp only [hq, ↓reduceIte] at h; exact absurd h (by simp)
  · rw [hp] at h; simp only [hq, ↓reduceIte] at h; exact absurd h (by simp)

/-! ## Reconstruction geometry -/

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (hcap : ∀ j ∈ J, (D.garden hS).tree j = TTree.leaf)

/-- The core node of a skeleton branch is the lone leaf of its native chain. -/
theorem slotOf_core (b : GBranch S.tree) : slotOf D hS (D.coreBranch hS b).toNode = .inr b := by
  let a : NativeNode D (.inr b) := ⟨((0 : Fin 1), (D.tree b).lonePath),
    Links.lonePath_mem_plug (D.tree b) (nodeSign S.sig b.1) TTree.leaf⟩
  have he : nativeNodeAt D hS (.inr b) a = (D.coreBranch hS b).toNode := Subtype.ext rfl
  rw [← he]
  exact slotOf_nativeNodeAt D hS _ a

include hcap in
/-- **The top of a non-trivial chain is never a capped flower parent.** -/
theorem chainTop_not_cfp (b' : GBranch S.tree) (h0 : (D.tree b').lonePath ≠ []) (C : GBranch (D.forest hS))
    (hC : C.1 = inflatedPosition S D.tree b'.toNode) :
    ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C := by
  intro hc
  have h1 := slotOf_chainTop D hS b' C hC
  rcases capParent_core_or_native D hS layer hLayer J hcap C hc with ⟨b'', rfl⟩ | ⟨q, c, -, rfl⟩
  · rw [slotOf_core] at h1
    obtain rfl := Sum.inr_injective h1
    have h2 : (D.coreBranch hS b'').1.2 = (inflatedPosition S D.tree b''.toNode).2 ++ (D.tree b'').lonePath := rfl
    rw [hC] at h2
    have h3 := congrArg List.length h2
    simp only [List.length_append] at h3
    exact h0 (List.length_eq_zero_iff.mp (by omega))
  · rw [slotOf_subforestBranch] at h1
    exact Sum.inl_ne_inr h1

include hcap in
/-- **The terminal node of a non-trivial chain is never a capped flower parent.** -/
theorem terminal_not_cfp (π : GBranch S.tree) (h0 : (D.tree π).lonePath ≠ []) (B : GBranch (D.forest hS))
    (hB : B.1 = addrExt (inflatedPosition S D.tree π.toNode) (D.tree π).lonePath.dropLast) :
    ¬ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J B := by
  intro hc
  have h1 := slotOf_chainTerminal D hS π h0 B hB
  rcases capParent_core_or_native D hS layer hLayer J hcap B hc with ⟨b'', rfl⟩ | ⟨q, c, -, rfl⟩
  · rw [slotOf_core] at h1
    obtain rfl := Sum.inr_injective h1
    have h2 : (D.coreBranch hS b'').1.2 = (inflatedPosition S D.tree b''.toNode).2 ++ (D.tree b'').lonePath := rfl
    rw [hB] at h2
    simp only [addrExt] at h2
    have h3 := congrArg List.length h2
    simp only [List.length_append, List.length_dropLast] at h3
    have h4 : (D.tree b'').lonePath.length ≠ 0 := fun h => h0 (List.length_eq_zero_iff.mp h)
    omega
  · rw [slotOf_subforestBranch] at h1
    exact Sum.inl_ne_inr h1

include hcap in
/-- **The top attached at a skeleton branch `b'` is a capped flower parent iff the chain of `b'` is trivial and its core
is one.** -/
theorem cfp_attached_branch_iff (b' : GBranch S.tree) :
    (∃ C : GBranch (D.forest hS), C.toNode = attachedNode D hS b'.toNode ∧
        IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C) ↔
      (D.tree b').lonePath = [] ∧ IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b') := by
  constructor
  · rintro ⟨C, hC, hc⟩
    rcases attachedTop_of_eq D hS _ C hC with ⟨b0, hb0, h0, rfl⟩ | ⟨b0, hb0, h0, hC1, -⟩ | ⟨σ, hσ, -, -⟩
    · obtain rfl := Mole.branch_toNode_injective hb0
      exact ⟨h0, hc⟩
    · obtain rfl := Mole.branch_toNode_injective hb0
      exact absurd hc (chainTop_not_cfp D hS layer hLayer J hcap b0 h0 C hC1)
    · exact (VineB.SpliceShape.leaf_ne_branch hσ).elim
  · rintro ⟨h0, hc⟩
    refine ⟨D.coreBranch hS b', Subtype.ext ?_, hc⟩
    show D.corePosition b' = inflatedPosition S D.tree b'.toNode
    unfold ReconstructionData.corePosition
    rw [h0]
    simp [addrExt]

/-! ## Native couple roots -/

/-- **The native-couple form of "the root on side `i` is a capped flower parent"**: side `i` is off the cap trees and
some depth-one leaf of side `i` is paired with a leaf on a side in a cap tree (`inJ j`: the tree of side `j`). -/
def RootCfpG (G2 : Garden 2) (i : Fin 2) (inJ : Fin 2 → Prop) : Prop :=
  ¬ inJ i ∧ ∃ ℓ' : GLeaf G2.tree, ℓ'.1.1 = i ∧ ℓ'.1.2.length = 1 ∧ inJ (G2.pair ℓ').1.1

/-- **A root of a native couple is a capped flower parent iff the couple satisfies `RootCfpG`.** -/
theorem cfp_nativeRoot_iff (q : SourcePair S) (i : Fin 2) (T : GBranch (D.forest hS))
    (hT : T.toNode = (nativeCoupleForest D hS q).root i) :
    IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J T ↔
      RootCfpG (decodedCouple (D.couple q)) i (fun j => ((nativeCoupleForest D hS q).root j).1.1 ∈ J) := by
  rw [← nativeCoupleGarden_eq D hS q]
  have hT1 : T.1 = ((nativeCoupleForest D hS q).root i).1 := congrArg Subtype.val hT
  have hpairE := Comb.RootedSubforest.inducedGarden_pair (G := D.garden hS) (nativeCoupleForest D hS q)
    (nativeCoupleForest_closed D hS q)
  constructor
  · rintro ⟨ℓ, ⟨hℓJ, hpJ⟩, hpar1, k, hpar2⟩
    have hmem : ℓ ∈ Comb.RootedSubforest.leafSet (G := D.garden hS) (nativeCoupleForest D hS q) := by
      refine (Comb.RootedSubforest.mem_leafSet_iff (G := D.garden hS) _ ℓ).mpr ⟨i, ?_, ?_⟩
      · exact (congrArg Prod.fst hT1).symm.trans hpar1.symm
      · show ((nativeCoupleForest D hS q).root i).1.2 <+: ℓ.1.2
        rw [hpar2, ← congrArg Prod.snd hT1]
        exact List.prefix_append _ _
    obtain ⟨ℓ', -, he⟩ := Finset.mem_image.mp hmem
    have hv := congrArg Subtype.val he
    have hv1 : ((nativeCoupleForest D hS q).root ℓ'.1.1).1.1 = ℓ.1.1 := by have h := congrArg Prod.fst hv; exact h
    have hv2 : ((nativeCoupleForest D hS q).root ℓ'.1.1).1.2 ++ ℓ'.1.2 = ℓ.1.2 := by
      have h := congrArg Prod.snd hv; exact h
    have hTp : ℓ.1.2 = ((nativeCoupleForest D hS q).root i).1.2 ++ [k] := by
      rw [hpar2, ← congrArg Prod.snd hT1]
    have hside : ℓ'.1.1 = i := by
      by_contra hne
      have hinc := (nativeCoupleForest D hS q).incomparable _ _ hne
      have htr : ((nativeCoupleForest D hS q).root ℓ'.1.1).1.1 = ((nativeCoupleForest D hS q).root i).1.1 := by
        rw [hv1, hpar1]; exact (congrArg Prod.fst hT1)
      have p1 : ((nativeCoupleForest D hS q).root ℓ'.1.1).1.2 <+: ℓ.1.2 := ⟨ℓ'.1.2, hv2⟩
      have p2 : ((nativeCoupleForest D hS q).root i).1.2 <+: ℓ.1.2 := ⟨[k], hTp.symm⟩
      rcases List.prefix_or_prefix_of_prefix p1 p2 with h | h
      · exact hinc.1 ⟨htr, h⟩
      · exact hinc.2 ⟨htr.symm, h⟩
    refine ⟨?_, ℓ', hside, ?_, ?_⟩
    · show ((nativeCoupleForest D hS q).root i).1.1 ∉ J
      rw [← congrArg Prod.fst hT1, ← hpar1]; exact hℓJ
    · rw [hside, hTp] at hv2
      rw [List.append_cancel_left hv2]; rfl
    · have hp := hpairE ℓ'
      rw [he] at hp
      have h2 := congrArg (fun m : GLeaf (D.forest hS) => m.1.1) hp
      show ((nativeCoupleForest D hS q).root _).1.1 ∈ J
      exact h2 ▸ hpJ
  · rintro ⟨hni, ℓ', hside, hlen, hpJ⟩
    obtain ⟨k, hk⟩ := List.length_eq_one_iff.mp hlen
    let ℓ := Comb.RootedSubforest.leafEmbedding (nativeCoupleForest D hS q) ℓ'
    have hℓ1 : ℓ.1.1 = ((nativeCoupleForest D hS q).root i).1.1 := by
      show ((nativeCoupleForest D hS q).root ℓ'.1.1).1.1 = _
      rw [hside]
    have hℓ2 : ℓ.1.2 = ((nativeCoupleForest D hS q).root i).1.2 ++ [k] := by
      show ((nativeCoupleForest D hS q).root ℓ'.1.1).1.2 ++ ℓ'.1.2 = _
      rw [hside, hk]
    refine ⟨ℓ, ⟨?_, ?_⟩, ?_, k, ?_⟩
    · rw [hℓ1]; exact hni
    · have hp := hpairE ℓ'
      have h2 := congrArg (fun m : GLeaf (D.forest hS) => m.1.1) hp
      exact (congrArg (· ∈ J) h2).mp hpJ
    · rw [hℓ1, ← congrArg Prod.fst hT1]
    · rw [hℓ2, ← congrArg Prod.snd hT1]

/-! ## The four predicates at a core branch -/

/-- **Root**: the core of `b` is a root iff `b` is a skeleton root with trivial chain. -/
theorem core_root_iff (b : GBranch S.tree) :
    (D.coreBranch hS b).1.2 = [] ↔ b.1.2 = [] ∧ (D.tree b).lonePath = [] := by
  have h2 : (D.coreBranch hS b).1.2 = (inflatedPosition S D.tree b.toNode).2 ++ (D.tree b).lonePath := rfl
  rw [h2, List.append_eq_nil_iff]
  constructor
  · rintro ⟨h1, h3⟩
    refine ⟨?_, h3⟩
    by_contra hb
    exact inflatedPosition_path_ne_nil D.tree b.toNode hb h1
  · rintro ⟨h1, h3⟩
    refine ⟨?_, h3⟩
    have : inflatedPosition S D.tree b.toNode = b.toNode.1 := by
      rw [inflatedPosition]
      simp only [show b.toNode.1.2 = [] from h1, ↓reduceDIte]
    rw [this]
    exact h1

/-- **`dParent`**: the core of `b` has a capped-flower-parent child iff the top attached at some skeleton child is
one. -/
theorem hasCfpChild_core_iff (b : GBranch S.tree) :
    (∃ C, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C ∧ C.IsChildOf (D.coreBranch hS b)) ↔
      ∃ (i : Fin 3) (C : GBranch (D.forest hS)), C.toNode = attachedNode D hS (b.child i) ∧
        IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C := by
  constructor
  · rintro ⟨C, hc, hC⟩
    obtain ⟨i, hi⟩ := child_of_core D hS hC
    exact ⟨i, C, hi, hc⟩
  · rintro ⟨i, C, hC, hc⟩
    refine ⟨C, hc, ?_⟩
    rw [attachedNode_child] at hC
    have hv := congrArg Subtype.val hC
    refine ⟨?_, i, ?_⟩
    · have h := congrArg Prod.fst hv; exact h
    · have h := congrArg Prod.snd hv; exact h

/-- The core of a non-root skeleton branch with trivial chain is a child of the core of its skeleton parent. -/
theorem core_addr_of_nil (b : GBranch S.tree) (h0 : (D.tree b).lonePath = []) (hb : b.1.2 ≠ []) :
    (D.coreBranch hS b).1 = ((D.coreBranch hS (b.toNode.parent hb)).1.1,
      (D.coreBranch hS (b.toNode.parent hb)).1.2 ++ [b.1.2.getLast hb]) := by
  show addrExt (inflatedPosition S D.tree b.toNode) (D.tree b).lonePath = _
  rw [h0]
  have hip : inflatedPosition S D.tree b.toNode =
      addrExt (inflatedPosition S D.tree (b.toNode.parent hb).toNode)
        ((D.tree (b.toNode.parent hb)).lonePath ++ [b.1.2.getLast hb]) := by
    rw [inflatedPosition]
    simp only [show b.toNode.1.2 ≠ [] from hb, ↓reduceDIte]
    rfl
  rw [hip]
  show ((inflatedPosition S D.tree (b.toNode.parent hb).toNode).1,
      ((inflatedPosition S D.tree (b.toNode.parent hb).toNode).2 ++
        ((D.tree (b.toNode.parent hb)).lonePath ++ [b.1.2.getLast hb])) ++ []) =
    ((inflatedPosition S D.tree (b.toNode.parent hb).toNode).1,
      ((inflatedPosition S D.tree (b.toNode.parent hb).toNode).2 ++ (D.tree (b.toNode.parent hb)).lonePath) ++
        [b.1.2.getLast hb])
  simp only [List.append_nil, List.append_assoc]

include hcap in
/-- **`dChild i`**: the core of `b` is child `i` of a capped flower parent iff the chain of `b` is trivial, `b` is not a
skeleton root, its last step is `i`, and the core of its skeleton parent is a capped flower parent. -/
theorem childOfCfp_core_iff (b : GBranch S.tree) (i : Fin 3) :
    (∃ C, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J C ∧ (D.coreBranch hS b).1.1 = C.1.1 ∧
        (D.coreBranch hS b).1.2 = C.1.2 ++ [i]) ↔
      (D.tree b).lonePath = [] ∧ ∃ hb : b.1.2 ≠ [], b.1.2.getLast hb = i ∧
        IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS (b.toNode.parent hb)) := by
  constructor
  · rintro ⟨C, hc, h1, h2⟩
    have hCaddr := parent_addr (show (D.coreBranch hS b).IsChildOf C from ⟨h1, i, h2⟩)
    by_cases h0 : (D.tree b).lonePath = []
    · have hb : b.1.2 ≠ [] := by
        intro hr
        have := (core_root_iff D hS b).mpr ⟨hr, h0⟩
        rw [this] at h2
        simp at h2
      have hcore := core_addr_of_nil D hS b h0 hb
      have hCe : C = D.coreBranch hS (b.toNode.parent hb) := by
        apply Subtype.ext
        rw [hCaddr, hcore, List.dropLast_concat]
      subst hCe
      refine ⟨h0, hb, ?_, hc⟩
      have h3 := congrArg Prod.snd hcore
      simp only at h3
      rw [h2] at h3
      exact (List.append_inj' h3 rfl).2 |> fun h => (List.singleton_inj.mp h).symm
    · exfalso
      refine terminal_not_cfp D hS layer hLayer J hcap b h0 C ?_ hc
      rw [hCaddr]
      show ((D.coreBranch hS b).1.1, (D.coreBranch hS b).1.2.dropLast) = _
      have e1 : (D.coreBranch hS b).1.1 = (inflatedPosition S D.tree b.toNode).1 := rfl
      have e2 : (D.coreBranch hS b).1.2 = (inflatedPosition S D.tree b.toNode).2 ++ (D.tree b).lonePath := rfl
      rw [e1, e2, List.dropLast_append_of_ne_nil h0]
      rfl
  · rintro ⟨h0, hb, hi, hc⟩
    refine ⟨_, hc, ?_, ?_⟩
    · have h := congrArg Prod.fst (core_addr_of_nil D hS b h0 hb); exact h
    · rw [← hi]
      have h := congrArg Prod.snd (core_addr_of_nil D hS b h0 hb); exact h

end WaveTurbulence.Flower.MkSlotsB
