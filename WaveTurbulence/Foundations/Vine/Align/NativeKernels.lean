/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.Align.OrdinaryProfiles
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw9Native
/-! Actual native kernels at ordinary slots of one LF construction. -/
@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineAlign
open VineEstS4 Reg RegRed RegRedLeaf LFTwist Reg.Skeleton LGSpine Links TTree

/-- Only the profiles of actual input leaves affect the leafwise kernel. -/
theorem kernelLeaves_congr_inputs {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w)
    (H H' : LeafProfiles w d) (hH : ∀ l ∈ inputLeaves LG.garden, H l.1 = H' l.1)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    kernelLeaves L γ δ LG H up s k roots nfl = kernelLeaves L γ δ LG H' up s k roots nfl := by
  unfold kernelLeaves
  congr 1
  apply tsum_congr
  intro z
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  rw [hH l hl]

/-- The native couple profile reads exactly the actual embedded leaf address. -/
theorem nativeCoupleProfiles_leaf {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (H : LeafProfiles w d) (q : SourcePair S) (l : NativeLeaf D (.inl q)) :
    nativeCoupleProfiles D hS H q l.1 = H (nativeLeafAt D hS (.inl q) l).1 := by
  unfold nativeCoupleProfiles
  have hn : l.1.2 ∈ ((nativeCoupleGarden D hS q).tree l.1.1).nodes := leaves_subset_nodes _ l.2
  rw [dite_eq_left hn]
  exact congrArg (fun x : GNode (D.forest hS) => H x.1) (nativeLeafAt_toNode D hS (.inl q) l).symm

/-- The native tree profile reads exactly the actual embedded internal leaf address. -/
theorem nativeChainProfiles_leaf {w d : ℕ} {S : Garden w} (D : ReconstructionData S)
    (hS : S.IsPlain) (H : LeafProfiles w d) (b : GBranch S.tree) (l : NativeLeaf D (.inr b)) :
    nativeChainProfiles D hS H b l.1.1 = H (nativeLeafAt D hS (.inr b) l).1 := by
  unfold nativeChainProfiles
  rw [dite_eq_left (leaves_subset_nodes _ l.1.2)]
  exact congrArg (fun x : GNode (D.forest hS) => H x.1) (nativeLeafAt_toNode D hS (.inr b) l).symm

variable {w p d : ℕ} {kind ε : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG}
  (h : LFConstruction s ε)
  (layer : GNode (s.data.forest s.plain) → ℕ) (hLayer : IsLayering (s.data.garden s.plain) layer)
  (hspec : layeredReconstruction s.data s.plain layer hLayer = LG)
  (layer' : GNode (h.data.forest (s.chosen_plain ε)) → ℕ)
  (hLayer' : IsLayering (h.data.garden (s.chosen_plain ε)) layer')
  (hspec' : layeredReconstruction h.data (s.chosen_plain ε) layer' hLayer' = h.output)
  (f : ℕ → Fin w → Fin w → Mom d → ℝ) (L γ δ : ℝ)

include hspec hspec'

/-- Actual ordinary-couple kernels agree for every pair of times and every momentum. -/
theorem ordinary_couple_kernel (q : SourcePair s.skeleton) (hq : q ≠ s.exceptional)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    coupleLeaves L γ δ (nativeCoupleLayered h.data (s.chosen_plain ε) layer' hLayer' (s.pairs ε q))
      (nativeCoupleProfiles h.data (s.chosen_plain ε) (typeProfiles h.output f) (s.pairs ε q)) (ts 0) (ts 1) k =
    coupleLeaves L γ δ (nativeCoupleLayered s.data s.plain layer hLayer q)
      (nativeCoupleProfiles s.data s.plain (typeProfiles LG f) q) (ts 0) (ts 1) k := by
  rw [native_couple_eq h layer hLayer hspec layer' hLayer' hspec' q hq]
  apply kernelLeaves_congr_inputs
  intro l hl
  obtain ⟨l', he⟩ := h.coupleTransport q hq l
  have hc : h.OrdCorr (nativeLeafAt s.data s.plain (.inl q) l)
      (nativeLeafAt h.data (s.chosen_plain ε) (.inl (s.pairs ε q)) l') :=
    Or.inl ⟨q, hq, l, l', he, rfl, rfl⟩
  calc
    _ = nativeCoupleProfiles h.data (s.chosen_plain ε) (typeProfiles h.output f) (s.pairs ε q) l'.1 :=
      congrArg _ he
    _ = _ := nativeCoupleProfiles_leaf _ _ _ _ _
    _ = _ := (ordinary_typeProfiles h layer hLayer hspec layer' hLayer' hspec' hc f).symm
    _ = _ := (nativeCoupleProfiles_leaf _ _ _ _ _).symm

/-- Actual ordinary-tree kernels agree for every pair of times and every momentum. -/
theorem ordinary_tree_kernel (b : GBranch s.skeleton.tree) (hb : b ≠ s.placement.lower)
    (ts : Fin 2 → ℝ) (k : Mom d) :
    treeLeaves L γ δ (nativeChainLayered h.data (s.chosen_plain ε) layer' hLayer' (s.branches ε b))
      (nativeChainProfiles h.data (s.chosen_plain ε) (typeProfiles h.output f) (s.branches ε b)) (ts 0) (ts 1) k =
    treeLeaves L γ δ (nativeChainLayered s.data s.plain layer hLayer b)
      (nativeChainProfiles s.data s.plain (typeProfiles LG f) b) (ts 0) (ts 1) k := by
  rw [native_tree_eq h layer hLayer hspec layer' hLayer' hspec' b hb]
  apply kernelLeaves_congr_inputs
  intro l hl
  let q : NativeLeaf s.data (.inr b) := ⟨l, fun he => not_mem_inputLeaves_chain_lone s.data b l he hl⟩
  obtain ⟨q', he⟩ := h.chainTransport b hb q
  have hc : h.OrdCorr (nativeLeafAt s.data s.plain (.inr b) q)
      (nativeLeafAt h.data (s.chosen_plain ε) (.inr (s.branches ε b)) q') :=
    Or.inr ⟨b, hb, q, q', he, rfl, rfl⟩
  calc
    _ = nativeChainProfiles h.data (s.chosen_plain ε) (typeProfiles h.output f) (s.branches ε b) q'.1.1 :=
      congrArg _ he
    _ = _ := nativeChainProfiles_leaf _ _ _ _ _
    _ = _ := (ordinary_typeProfiles h layer hLayer hspec layer' hLayer' hspec' hc f).symm
    _ = _ := (nativeChainProfiles_leaf _ _ _ _ q).symm

end WaveTurbulence.VineAlign
