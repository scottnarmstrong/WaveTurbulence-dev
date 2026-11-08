/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.Split
public import WaveTurbulence.Foundations.Flower.MkSlotsO.UnCopy
public import WaveTurbulence.Foundations.Flower.MkSlotsB.ROne
public import WaveTurbulence.Foundations.Flower.MkSlots.PRedLeaves

/-! # B3s-HELPER8 / UNPIN (part 1): the general slot kernel of an unpinned slot is a leafwise kernel

On a slot none of whose native branches is pinned (`fixNative … ≡ none`), β's relaxed pinned weighted slot kernel
`MkSlotsB.slotFnGWFRL` with the per-slot factor `genΘs` is the weighted leafwise kernel `kernelNodeW` of the native
object (unpinned time domain `kDomain`, Lebesgue time measure), with the decoration weight `m · θ` where `m` is the
node product of the node weight and `θ` the node product of `unNode` at the native resonances.

* `kernelNodeWR_coset`: a decoration weight that factors through the coset decoration moves into the momentum weight;
* `kernelNodeWR_none_eq`: no pins, the domain `kDomain`, unit decoration weight: `kernelNodeW`;
* `fixNative_none_of_not_pin`: `¬ HasPinNative` means that no native branch is pinned;
* **`slotFnGWFRL_genΘs_inl`**, **`slotFnGWFRL_genΘs_inr`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.Flower.MkSlotsI
open WaveTurbulence.VineA

namespace WaveTurbulence.Flower.MkSlotsO

variable {w d : ℕ}

/-- A decoration weight that factors through the coset decoration moves into the momentum weight. -/
theorem kernelNodeWR_coset (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m θ : (GNode LG.garden.tree → Mom d) → ℂ) (Dom : Set (GBranch LG.garden.tree → ℝ)) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (fix : GBranch LG.garden.tree → Option ℝ) :
    MkSlotsB.kernelNodeWR L γ δ LG A m Dom k₀ nroot nfl (fun κ => θ (cosetDecoration LG.garden L k₀ κ.1)) fix =
      MkSlotsB.kernelNodeWR L γ δ LG A (fun k => m k * θ k) Dom k₀ nroot nfl (fun _ => 1) fix := by
  unfold MkSlotsB.kernelNodeWR
  congr 1
  refine tsum_congr fun κ => ?_
  ring

/-- Without pins, on the domain `kDomain`, with unit decoration weight, the relaxed kernel is `kernelNodeW`. -/
theorem kernelNodeWR_none_eq (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b) :
    MkSlotsB.kernelNodeWR L γ δ LG A m (kDomain LG up s) k₀ nroot nfl (fun _ => 1) (fun _ => none) =
      Stage1WNoVine.kernelNodeW L γ δ LG A m up s k₀ nroot nfl := by
  rw [MkSlotsB.kernelNodeWR_one_eq L γ δ LG A m (kDomain LG up s) up s k₀ nroot nfl (fun _ => none)
    (fun _ _ => Iff.rfl)]
  exact MkSlots.kernelNodeWF_none L γ δ LG A m up s k₀ hG nroot nfl

/-- **The unpinned relaxed kernel** with a decoration weight factoring through the coset decoration. -/
theorem kernelNodeWR_unpinned (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m θ : (GNode LG.garden.tree → Mom d) → ℂ) (up : GBranch LG.garden.tree → ℝ) (s : ℝ)
    (Fn : GBranch LG.garden.tree → Option ℝ) (upFree : GBranch LG.garden.tree → Prop) (sFree : Prop) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (hG : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hFn : ∀ b, Fn b = none) :
    MkSlotsB.kernelNodeWR L γ δ LG A m (MkSlotsB.kDomainR LG up s Fn upFree sFree) k₀ nroot nfl
        (fun κ => θ (cosetDecoration LG.garden L k₀ κ.1)) Fn =
      Stage1WNoVine.kernelNodeW L γ δ LG A (fun k => m k * θ k) up s k₀ nroot nfl := by
  have e : Fn = fun _ => none := funext hFn
  subst e
  rw [MkSlotsB.kDomainR_none, kernelNodeWR_coset]
  exact kernelNodeWR_none_eq L γ δ LG A _ up s k₀ nroot nfl hG

section Slot

variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)

/-- The couple slot kernel with the per-slot factor `genΘs`, unfolded. -/
theorem un_slotFn_inl (γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (fixG : GBranch (D.forest hS) → Option ℝ) (q : SourcePair S) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL D hS L γ δ H W (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer fixG (.inl q) ts k =
      MkSlotsB.kernelNodeWR L γ δ (nativeCoupleLayered D hS layer hLayer q)
        (fun a => H ((nativeCoupleForest D hS q).nodeEmbedding a).1)
        (fun k' => ∏ a, W ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a))
        (MkSlotsB.kDomainR (nativeCoupleLayered D hS layer hLayer q) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
          (MkSlots.fixNative D hS fixG (.inl q)) (fun _ => False) False)
        k (fun _ => 0) 0
        (fun κ => (fun k' => ∏ a, unNode D hS layer hLayer J L σ kSel Rs
          ((nativeCoupleForest D hS q).nodeEmbedding a) (MkSlotsS.omegaAt k' a))
          (cosetDecoration (nativeCoupleLayered D hS layer hLayer q).garden L k κ.1))
        (MkSlots.fixNative D hS fixG (.inl q)) := rfl

/-- The chain slot kernel with the per-slot factor `genΘs`, unfolded. -/
theorem un_slotFn_inr (γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (fixG : GBranch (D.forest hS) → Option ℝ) (b : GBranch S.tree) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL D hS L γ δ H W (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer fixG (.inr b) ts k =
      MkSlotsB.kernelNodeWR L γ δ (nativeChainLayered D hS layer hLayer b)
        (fun a => H (chainContextNode D hS b a).1)
        (fun k' => ∏ a, W (chainContextNode D hS b a) (k' a))
        (MkSlotsB.kDomainR (nativeChainLayered D hS layer hLayer b) (fun _ => ts 0) (ts 1)
          (MkSlots.fixNative D hS fixG (.inr b)) (fun _ => False) (MkSlots.fixCore D hS fixG b = none))
        k (fun _ => 0) 0
        (fun κ => (fun k' => ∏ a, unNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b a)
          (MkSlotsS.omegaAt k' a)) (cosetDecoration (nativeChainLayered D hS layer hLayer b).garden L k κ.1))
        (MkSlots.fixNative D hS fixG (.inr b)) := rfl

/-- **The unpinned couple slot kernel** is the weighted leafwise kernel of the native couple. -/
theorem slotFnGWFRL_genΘs_inl (γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (fixG : GBranch (D.forest hS) → Option ℝ) (q : SourcePair S)
    (hfix : ∀ qb, MkSlots.fixNative D hS fixG (.inl q) qb = none) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL D hS L γ δ H W (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer fixG (.inl q) ts k =
      Stage1WNoVine.kernelNodeW L γ δ (nativeCoupleLayered D hS layer hLayer q)
        (fun a => H ((nativeCoupleForest D hS q).nodeEmbedding a).1)
        (fun k' => (∏ a, W ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a)) *
          ∏ a, unNode D hS layer hLayer J L σ kSel Rs ((nativeCoupleForest D hS q).nodeEmbedding a)
            (MkSlotsS.omegaAt k' a))
        (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0 := by
  rw [un_slotFn_inl]
  exact kernelNodeWR_unpinned L γ δ (nativeCoupleLayered D hS layer hLayer q) _ _
    (fun k' => ∏ a, unNode D hS layer hLayer J L σ kSel Rs ((nativeCoupleForest D hS q).nodeEmbedding a)
      (MkSlotsS.omegaAt k' a)) _ 0 _ _ _ k _ _
    (noFlowerParent_of_noFlower _ (nativeCouple_noFlower D hS q)) hfix

/-- **The unpinned chain slot kernel** is the weighted leafwise kernel of the native chain. -/
theorem slotFnGWFRL_genΘs_inr (γ δ : ℝ) (H : LeafProfiles w d) (W : GNode (D.forest hS) → Mom d → ℂ)
    (fixG : GBranch (D.forest hS) → Option ℝ) (b : GBranch S.tree)
    (hfix : ∀ qb, MkSlots.fixNative D hS fixG (.inr b) qb = none) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL D hS L γ δ H W (genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer fixG (.inr b) ts k =
      Stage1WNoVine.kernelNodeW L γ δ (nativeChainLayered D hS layer hLayer b)
        (fun a => H (chainContextNode D hS b a).1)
        (fun k' => (∏ a, W (chainContextNode D hS b a) (k' a)) *
          ∏ a, unNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b a) (MkSlotsS.omegaAt k' a))
        (fun _ => ts 0) (ts 1) k (fun _ => 0) 0 := by
  rw [un_slotFn_inr]
  exact kernelNodeWR_unpinned L γ δ (nativeChainLayered D hS layer hLayer b) _ _
    (fun k' => ∏ a, unNode D hS layer hLayer J L σ kSel Rs (chainContextNode D hS b a) (MkSlotsS.omegaAt k' a))
    _ _ _ _ _ k _ _ (noFlowerParent_of_noFlower _ (decodedTree_noFlower _ _)) hfix

end Slot

/-- `¬ HasPinNative`: no native branch of the slot is pinned. -/
theorem fixNative_none_of_not_pin {R : ℕ} {a : PrescribedPrimeGarden (2 * R)} {J : Finset (Fin (2 * R))}
    {pat : Fin (2 * R) → FixPat} {t s : ℝ} {kSel σ : Fin (2 * R) → Option ℕ} {sl : ReplacementSlot a.prime.skeleton}
    (h : ¬ HasPinNative a J pat t s kSel σ sl) (qb : NativeClockBranch a.prime.data sl) :
    MkSlots.fixNative a.prime.data a.prime.prime.1 (fixCap (MkSlots.recLG a) J pat t s) sl qb = none := by
  by_contra hne
  exact h ⟨qb, Option.ne_none_iff_isSome.mp hne⟩

end WaveTurbulence.Flower.MkSlotsO
