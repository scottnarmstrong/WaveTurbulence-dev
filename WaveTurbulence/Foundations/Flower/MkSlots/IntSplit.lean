/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.IntCapHyp

/-! # B3s MK-SLOTS (integration): the split of the capped node weight by native objects

On the reconstruction `LG = layeredReconstruction D hS layer hLayer` of a skeleton `S`, every node lies in exactly
one native object (`nativeNodeEquiv`; `slotOf`). The capped node weight `capNodeW` (frontier × dagger) is split as
`∏ capNodeW = (∏ chainW) · restW` (`prod_capNodeW_split`, pure algebra):

* `chainW`: the frontier weight everywhere, the dagger weight on the nodes of cap natives (`InCapNative`) and on the
  nodes that are not "case b" (`IsCaseB`: a core branch that is a capped flower parent, or one of its non-flower
  children); this is the node weight fed to the skeleton reduction;
* `restW`: the dagger weight on the case-b nodes outside cap natives (core flower parents and their siblings of the
  flower); it is a function of the skeleton decoration, and on the support of its indicators it is constant.

Geometric facts to be used with it (stated where proved): pins, anchored leaves and the dagger weight of non-core
capped flower parents lie in cap natives, so on every slot that is not a cap pair the pinned slot kernel with
`chainW` is B3's `slotFW`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlots

variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- The slot (native object) of a node of the reconstruction. -/
def slotOf (z : GNode (D.forest hS)) : ReplacementSlot S := ((nativeNodeEquiv D hS).symm z).1

/-- A node of the reconstruction lies in the native couple of a cap pair. -/
def InCapNative (J : Finset (Fin w)) (z : GNode (D.forest hS)) : Prop :=
  ∃ q : SourcePair S, slotOf D hS z = Sum.inl q ∧ IsCapPair S hS J q

theorem slotOf_nativeNodeAt (s : ReplacementSlot S) (a : NativeNode D s) :
    slotOf D hS (nativeNodeAt D hS s a) = s := by
  unfold slotOf
  have h : (nativeNodeEquiv D hS).symm (nativeNodeAt D hS s a) = ⟨s, a⟩ :=
    (nativeNodeEquiv D hS).symm_apply_eq.mpr rfl
  rw [h]

variable (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)

/-- "Case b" nodes: the core branch of a skeleton branch that is a capped flower parent, and its children other than
the capped flower. -/
def IsCaseB (J : Finset (Fin w)) (z : GNode (D.forest hS)) : Prop :=
  ∃ b : GBranch S.tree, IsCapFlowerParent (layeredReconstruction D hS layer hLayer) J (D.coreBranch hS b) ∧
    (z = (D.coreBranch hS b).toNode ∨ ∃ i : Fin 3, z = (D.coreBranch hS b).child i ∧
      ¬ ∃ ℓ : GLeaf (D.forest hS), IsCapFlower (layeredReconstruction D hS layer hLayer) J ℓ ∧ ℓ.toNode = z)

/-- **The node weight of the reduction**: frontier everywhere; dagger on cap natives and off the case-b nodes. -/
def chainW (L γ δ : ℝ) (p : ℕ) (s : ℝ) (J : Finset (Fin w)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (z : GNode (D.forest hS)) (x : Mom d) : ℂ :=
  fwNode (layeredReconstruction D hS layer hLayer) p (fun j => frontierG (Rf j)) z x *
    (if InCapNative D hS J z then dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J dag z x
      else if IsCaseB D hS layer hLayer J z then 1
      else dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J dag z x)

/-- **The remaining dagger weight**: the dagger weight on the case-b nodes outside cap natives. -/
def restW (L γ δ : ℝ) (s : ℝ) (J : Finset (Fin w)) (dag : Option (Fin w → Fin 3 → Mom d))
    (k : GNode (D.forest hS) → Mom d) : ℂ :=
  ∏ z, if ¬ InCapNative D hS J z ∧ IsCaseB D hS layer hLayer J z then
    dagNodeW L γ δ s (layeredReconstruction D hS layer hLayer) J dag z (k z) else 1

/-- **The split** `∏ capNodeW = (∏ chainW) · restW` (pointwise). -/
theorem prod_capNodeW_split (L γ δ : ℝ) (p : ℕ) (s : ℝ) (J : Finset (Fin w)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (k : GNode (D.forest hS) → Mom d) :
    ∏ z, capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag z (k z) =
      (∏ z, chainW D hS layer hLayer L γ δ p s J Rf dag z (k z)) * restW D hS layer hLayer L γ δ s J dag k := by
  unfold restW
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun z _ => ?_
  unfold capNodeW chainW
  by_cases h1 : InCapNative D hS J z
  · simp [h1]
  · by_cases h2 : IsCaseB D hS layer hLayer J z
    · simp [h1, h2]
    · simp [h1, h2]

end WaveTurbulence.Flower.MkSlots
