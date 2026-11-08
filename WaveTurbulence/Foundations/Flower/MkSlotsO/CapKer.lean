/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.CapGate
public import WaveTurbulence.Foundations.Flower.MkSlotsO.Obl

/-! # B3s-HELPER8 / CAP: the general cap slot kernel is a filtered protected kernel of the paired tree

On a nontrivial cap slot (B3s's `MkSlots.CapSide K`), the general slot kernel `slotFnGWFRL … chainW … genΘs …`
(the body of `MkSlotsI.genSlotKer` on a cap pair) at the cap momentum is
`c₀ · capCfgKer … (starWeight · capInd · capθ1) cfg … (ts j0)` (`slotFn_cap_T1`), where:

* `chainW = capNodeW` on the native nodes of the cap couple (`MkSlots.IntGeo.inCapNative_nativeNodeAt`);
* the per-slot factor `genΘs (.inl q) k κ = capΘ (coset κ)` is folded into the multiplier (`kernelNodeWR_fold`);
* the relaxed slot kernel is the protected kernel of the paired tree (`capKer_T1`, β's `CapP.capSlot_kernel_pat` with a
  general multiplier, copied by source);
* `K.m1_eq` (B3s) turns the capped node weight into `c₀ · starWeight · capInd`;
* the transported factor `capθ1` is D3/D6's filter multiplier on the chain nodes of the paired tree (`capθ1_eq`): σ's
  dyadic filters (`capFT`, scale `capMσ`), the selection shells and σ's filter at the selected vertex (`capFuT`,
  `capMuT`), the selected filter `chiD(|Ω|/Rs)` (`capSelT`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open MeasureTheory Set
open WaveTurbulence TTree WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
  WaveTurbulence.Links WaveTurbulence.LGSpine WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo
  WaveTurbulence.Flower.ProtWhole WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB

namespace WaveTurbulence.Flower.MkSlotsO

/-- A decoration weight that is a function of the coset decoration can be moved into the multiplier. -/
theorem kernelNodeWR_fold {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (A : GNode LG.garden.tree → Mom d → ℝ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (Dom : Set (GBranch LG.garden.tree → ℝ)) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (Θ : (GNode LG.garden.tree → Mom d) → ℂ)
    (fix : GBranch LG.garden.tree → Option ℝ) :
    kernelNodeWR L γ δ LG A m Dom k₀ nroot nfl (fun κ => Θ (cosetDecoration LG.garden L k₀ κ.1)) fix =
      kernelNodeWR L γ δ LG A (fun k' => m k' * Θ k') Dom k₀ nroot nfl (fun _ => 1) fix := by
  unfold kernelNodeWR
  congr 1
  refine tsum_congr fun κ => ?_
  ring

/-- Over the nodes, a function that is `1` off the branching nodes is a product over the branches. -/
theorem prod_node_eq_prod_branch {w : ℕ} {T : Fin w → TTree} {M : Type*} [CommMonoid M] (f : GNode T → M)
    (hf : ∀ a : GNode T, a.1.2 ∉ (T a.1.1).branching → f a = 1) :
    ∏ a, f a = ∏ b : GBranch T, f b.toNode := by
  refine (Fintype.prod_of_injective (fun b : GBranch T => b.toNode) (fun b b' h => ?_) (fun b => f b.toNode) f
    (fun a ha => hf a fun hb => ha ⟨⟨a.1, hb⟩, Subtype.ext rfl⟩) (fun _ => rfl)).symm
  exact Subtype.ext (congrArg (fun z : GNode T => z.1) h)

namespace CapK

variable {w : ℕ} {S : Garden w} {D : ReconstructionData S} {hS : S.IsPlain} {J : Finset (Fin w)}
  {q : SourcePair S} (K : CapSide D hS J q)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer)
  {p : ℕ} (hGeo : CapGeo (layeredReconstruction D hS layer hLayer) J p)

/-! ### The relaxed slot kernel with a general multiplier -/

include hGeo in
/-- **The relaxed slot kernel of a nontrivial cap slot, any multiplier** (β's `CapP.capSlot_kernel_pat`, copied by
source with the multiplier `m` in place of `∏ W`): the protected kernel of the paired tree at the upper clock `ts j0`,
with the pins of `objCfg … pat`. -/
theorem capKer_T1 {d : ℕ} (L γ δ : ℝ) (pat : Fin w → FixPat) (t s : ℝ) (H : LeafProfiles w d)
    (m : (GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree → Mom d) → ℂ) (ts : Fin 2 → ℝ) (k : Mom d) :
    kernelNodeWR L γ δ (nativeCoupleLayered D hS layer hLayer q)
        (fun a => H ((nativeCoupleForest D hS q).nodeEmbedding a).1) m
        (kDomainR (nativeCoupleLayered D hS layer hLayer q) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
          (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q)) (fun _ => False)
          False)
        k (fun _ => 0) 0 (fun _ => 1)
        (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q)) =
      kernelProt L γ δ (K.Dq layer hLayer).T1 (CapG.capH1 K.j0 (CapSide.Hq (q := q) layer hLayer H))
        (fun K' => m (fun a => K' ((K.Dq layer hLayer).ρ a)) *
          CapG.capPairFactor (K.Dq layer hLayer) (CapSide.Hq (q := q) layer hLayer H) K')
        (fun _ => ts K.j0) 0 ((CapP.cfgPat K layer hLayer pat).fix K.X s t (ts K.j0)) k (fun _ => 0) 0 := by
  set Dq := K.Dq layer hLayer
  set up : GBranch (nativeCoupleLayered D hS layer hLayer q).garden.tree → ℝ :=
    fun b => if b.1.1 = 0 then ts 0 else ts 1 with hupdef
  have e := kDomainR_eq_kDomainFix (nativeCoupleLayered D hS layer hLayer q) up
    (fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q))
  rw [e]
  refine (kernelNodeWR_kDomainFix_eq_kernelProt L γ δ _ _ _ up k _ _ _ Dq.not_loneParent).trans ?_
  refine (CapG.kernelProt_capG_T1 Dq L γ δ _ _ up _ k).trans ?_
  have hu : (fun b => up (Dq.βc b)) = fun _ => ts K.j0 := funext fun b1 => K.up_βc layer hLayer ts b1
  have hf : (fun b => fixNative D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q)
      (Dq.βc b)) = (CapP.cfgPat K layer hLayer pat).fix K.X s t (ts K.j0) :=
    funext fun b1 => CapP.capFixPat K layer hLayer hGeo pat t s (ts K.j0) b1
  rw [hu, hf]

/-! ### The per-slot factor of the cap couple -/

/-- The per-slot factor of the cap couple, as a function of a decoration of the native couple. -/
def capΘ {d : ℕ} (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (k' : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree → Mom d) : ℂ :=
  ∏ a : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree,
    if ∃ β : GBranch S.tree, (nativeCoupleForest D hS q).nodeEmbedding a = (D.coreBranch hS β).toNode then 1
    else MkSlotsI.genNW (layeredReconstruction D hS layer hLayer) J L σ kSel Rs
      ((nativeCoupleForest D hS q).nodeEmbedding a) (MkSlotsS.omegaAt k' a)

omit K in
theorem genΘs_inl {d : ℕ} (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (k : Mom d) :
    MkSlotsI.genΘs D hS layer hLayer J L σ kSel Rs (.inl q) k =
      fun κ => capΘ layer hLayer (q := q) (J := J) L σ kSel Rs
        (cosetDecoration (nativeCoupleLayered D hS layer hLayer q).garden L k κ.1) := rfl

/-- The per-slot factor transported to the paired tree. -/
def capθ1 {d : ℕ} (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (K' : GNode (K.Dq layer hLayer).T1.garden.tree → Mom d) : ℂ :=
  capΘ layer hLayer (q := q) (J := J) L σ kSel Rs (fun a => K' ((K.Dq layer hLayer).ρ a))

/-! ### The slot kernel identity -/

include hGeo in
/-- **The general cap slot kernel of a nontrivial cap slot** at the cap momentum: `c₀` times the filtered
configuration kernel of the paired tree at the chain clock. -/
theorem slotFn_cap_T1 {d : ℕ} (L γ δ : ℝ) (pat : Fin w → FixPat) (t s : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (roots : Fin w → (Fin d → ℤ)) (Rf : Fin w → Option ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) (hq : IsCapPair S hS J q) (ts : Fin 2 → ℝ) :
    slotFnGWFRL D hS L γ δ (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)
        (chainW D hS layer hLayer L γ δ p s J Rf dag) (MkSlotsI.genΘs D hS layer hLayer J L σ kSel Rs) layer hLayer
        (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) (.inl q) ts
        (latticePoint L (roots K.cleaf.1.1)) =
      K.capC0 L γ δ s (latticePoint L (roots K.cleaf.1.1)) dag *
        capCfgKer L γ δ (K.Dq layer hLayer)
          (CapG.capH1 K.j0 (CapSide.Hq (q := q) layer hLayer
            (anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots)))
          (fun K' => IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
            (K.capInd layer hLayer dag K' : ℂ) * capθ1 K layer hLayer L σ kSel Rs K')
          (CapP.cfgPat K layer hLayer pat) s t (latticePoint L (roots K.cleaf.1.1)) (ts K.j0) := by
  set k₀ := latticePoint L (roots K.cleaf.1.1)
  set H := anchProfiles J (layeredReconstruction D hS layer hLayer) h L roots
  have hW : (fun k' : GNode (nativeCoupleLayered D hS layer hLayer q).garden.tree → Mom d =>
      ∏ a, chainW D hS layer hLayer L γ δ p s J Rf dag ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a)) =
      fun k' => ∏ a, capNodeW L γ δ p s (layeredReconstruction D hS layer hLayer) J Rf dag
        ((nativeCoupleForest D hS q).nodeEmbedding a) (k' a) := by
    funext k'
    refine Finset.prod_congr rfl fun a _ => ?_
    have hin := IntGeo.inCapNative_nativeNodeAt D hS J q hq a
    unfold chainW capNodeW
    simp only [show InCapNative D hS J ((nativeCoupleForest D hS q).nodeEmbedding a) from hin, ↓reduceIte]
  dsimp only [slotFnGWFRL]
  rw [hW, genΘs_inl]
  refine (kernelNodeWR_fold L γ δ (nativeCoupleLayered D hS layer hLayer q) _ _ _ k₀ _ _ _ _).trans ?_
  refine (capKer_T1 K layer hLayer hGeo L γ δ pat t s H _ ts k₀).trans ?_
  rw [kernelProt_congr_m L γ δ _ _ _ (fun K' => K.capC0 L γ δ s k₀ dag *
      (IncTop.starWeight (K.frontS layer hLayer p) (IncTop.topStar (fun _ => frontierG (Rf K.u.1))) K' *
        (K.capInd layer hLayer dag K' : ℂ) * capθ1 K layer hLayer L σ kSel Rs K')) _ _ _ _ _ _ (fun κ => ?_)]
  · exact kernelProt_const_mul L γ δ _ _ _ _ _ _ _ _ _ _
  · have e := K.m1_eq layer hLayer hGeo L γ δ s h roots Rf dag κ
    unfold CapSide.m1 at e
    unfold capθ1
    beta_reduce
    rw [mul_right_comm]
    exact (congrArg (fun z => z * _) e).trans (by ring)

end CapK

end WaveTurbulence.Flower.MkSlotsO
