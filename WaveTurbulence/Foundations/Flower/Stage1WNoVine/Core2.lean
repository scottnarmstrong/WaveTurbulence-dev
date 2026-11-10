/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.FwNode
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.SlotTree
public import WaveTurbulence.Foundations.Stage1.Represents.RepSlots2
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr7
public import WaveTurbulence.Foundations.Spine.IncoherentConstantMonotonicity
public import WaveTurbulence.Foundations.Spine.SourceProviders
public import WaveTurbulence.Foundations.Flower.IncTop.Gate

/-! # STAGE1W-O4: the weighted vine-free core and its prefix (row O4d, part 2)

* `slots_existW`: the per-slot superpositions of the weighted slot kernels of one profile (main's `slots_exist` with
  `couple_slot_targetW` / `tree_slot_targetW`), with masses carrying `cψ ^ slotNr`.
* `represents_noVine_coreW`: main's `represents_noVine_core` for the weighted value, at size `cψ^(3·order) s`.
* `NoVineRepresentsAtNW`, `noVineRepresentsAtNW_of_gate`: main's `NoVineRepresentsAtN` for the weighted value.
* `noVine_prefixNW`: its prefix, from main's two leafwise gates and the staged INC-TOP gate. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.Stage1WNoVine
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine
  WaveTurbulence.VineEstS3.FS MeasureTheory Set WaveTurbulence.RegRedLeaf WaveTurbulence.RegRed
  WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W WaveTurbulence.PL2330 WaveTurbulence.RedSplice
  WaveTurbulence.VineA
open scoped ENNReal

section Slots

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

theorem cplExp_le_slotNr (p : ℕ) (p' : SourcePair S) :
    cplExp (nativeCoupleLayered D hS layer hLayer p') (cplQ D hS layer hLayer p p' 0)
      (cplQ D hS layer hLayer p p' 1) ≤ slotNr D hS (.inl p') := by
  have h := card_embNodes_le (layeredReconstruction D hS layer hLayer) (nativeCoupleLayered D hS layer hLayer p')
    (fun a => (nativeCoupleForest D hS p').nodeEmbedding a) (fun j => ((nativeCoupleForest D hS p').root j).1)
    (fun a => rfl) p
  unfold cplExp cplNodes
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq rfl))
  congr 1
  refine Finset.filter_congr fun x _ => ?_
  have e : ![cplQ D hS layer hLayer p p' 0, cplQ D hS layer hLayer p p' 1] x.1.1 = cplQ D hS layer hLayer p p' x.1.1 :=
    congrFun (fin2_vec (cplQ D hS layer hLayer p p')).symm x.1.1
  rw [e]
  rfl

theorem treeExp_le_slotNr (p : ℕ) (b : GBranch S.tree) :
    treeExp (nativeChainLayered D hS layer hLayer b) (treeQ D hS layer hLayer p b) ≤ slotNr D hS (.inr b) := by
  have h := card_embNodes_le (layeredReconstruction D hS layer hLayer) (nativeChainLayered D hS layer hLayer b)
    (chainContextNode D hS b) (fun _ => inflatedPosition S D.tree b.toNode) (fun a => rfl) p
  unfold treeExp treeNodes
  refine le_trans (le_of_eq ?_) (h.trans (le_of_eq rfl))
  congr 1

end Slots

/-! ### The vine-free successor pieces -/

/-- The staged INC-TOP input is monotone in the large constants. -/
theorem topIncoherentDecayAtR_largeConstantMonotone : LargeConstantMonotone TopIncoherentDecayAtR := by
  intro P C₁ C₂ hC hC₂ hδ hL hCC hCC₂ hsource p hp n hn g cψ hc hg
  rw [N_largeConstants] at hn
  have hc0 : 0 ≤ P.C₁ := by linarith
  have hL0 : 0 ≤ P.L := by linarith
  have hreg := regBound_largeConstants_mono (C₂ := C₂) P hc0 hCC hδ.le hL0 n
  constructor
  · intro Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi H B hb
    refine ((hsource p hp n hn g cψ hc hg).1 Q hw hsize LG hQ hlayer q q' hq hq' hroot hroot' hi H B hb).trans ?_
    gcongr
    exact hreg _
  · intro X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi H B hb
    refine ((hsource p hp n hn g cψ hc hg).2 X hw hsize LG hX hlayer q q' hqq' hqp hroot hlone hi H B hb).trans ?_
    gcongr
    exact hreg _

end WaveTurbulence.Flower.Stage1WNoVine
