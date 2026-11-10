/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WVine.WRegion2
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB11
public import WaveTurbulence.Foundations.Stage1.Represents.RepVB9

/-! # STAGE1W-VINE (T3): the regional bound of the weighted slot family, and its unit kernel is the pinned kernel

* `regBoundFW`: the abstract regional bound `RegBound` for the frontier-weighted slot family (V5's `localBound` times
  `cψ`-powers, the weight being `|g| ≤ cψ`); measurability from the time continuity of the weighted leaf kernels.
* `unitKernelMG_slotFW_eq`: for the blocks of the unit regions of a state `X` decoded by `layer`, VINE-B♯'s generic unit
  factor of the weighted slot family is the pinned `unitRecenteredFW p (g j₁) none X (us j) … (modW λ)` (S-V5W §1),
  at the unit's layer profile.  This is the per-member input of T4 (`WeightedClassFactorization`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option linter.unusedSectionVars false
noncomputable section
namespace WaveTurbulence.Flower.Stage1WVine
open TTree WaveTurbulence WaveTurbulence.RegRed WaveTurbulence.RedSplice Finset WaveTurbulence.Represents
  WaveTurbulence.Reg.Skeleton WaveTurbulence.LGSpine WaveTurbulence.RegRedLeaf WaveTurbulence.VineEstS3.FS
  WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C MeasureTheory
  WaveTurbulence.VineB WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.V5W WaveTurbulence.VineC
  WaveTurbulence.LFTwist

/-! ## Norms and continuity of the weighted rows -/

theorem norm_rowTopWeight_le {w d : ℕ} (p : ℕ) (g : Mom d → ℂ) (LG : LayeredGarden w) (qr : Fin w → ℕ)
    (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ) (k : GNode LG.garden.tree → Mom d) :
    ‖rowTopWeight p g LG qr k‖ ≤ cψ ^ Fintype.card (GNode LG.garden.tree) := by
  unfold rowTopWeight
  refine (Finset.norm_prod_le _ _).trans ?_
  refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => ?_)).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ])
  unfold topPsi
  split_ifs
  · exact hg _
  · simpa using hc

/-- Time continuity of a leaf kernel with a bounded decoration weight (cf. main's `continuous_kernelK_time`). -/
theorem continuous_kernelLeavesW_time' {w d : ℕ} (L γ δ : ℝ) (H : LeafProfiles w d)
    (LG : LayeredGarden w) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (M : ℝ) (hm : ∀ k, ‖m k‖ ≤ M)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k₀ + latticePoint L n)|) :
    Continuous (fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
      kernelLeavesW L γ δ LG H x.1 x.2 k₀ nroot nfl m) := by
  unfold kernelLeavesW
  apply Continuous.mul continuous_const
  apply continuous_tsum
  · intro κ
    exact continuous_const.mul ((continuous_const.mul
      (continuous_phaseIntegral_no_flower L γ δ LG hflower
        (cosetDecoration LG.garden L k₀ κ.1))).mul continuous_const)
  · exact (summable_leafInputMajorant L H LG k₀ nroot nfl hlone hF).mul_left M
  · intro κ x
    rw [norm_mul]
    exact mul_le_mul (hm _) (norm_leafKernel_summand_le_leafInputMajorant L γ δ H LG x.1 x.2 k₀ κ)
      (norm_nonneg _) ((norm_nonneg _).trans (hm 0))

section Bound
variable {w d : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (L γ δ : ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (p : ℕ)
  (gT : Fin w → Mom d → ℂ)

theorem norm_slotFW_couple_le (u : CLBlock S) {pr : SourcePair S} (hp : pr ∈ clRegionalPairs hS u.atoms)
    (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖gT j x‖ ≤ cψ) (base : Mom d)
    (hF : HF D hS L (fun q => h q u.upper.1.1 u.upper.1.1) layer base) (ts : Fin 2 → ℝ) (x : Fin d → ℤ) :
    ‖slotFW D hS layer hLayer L γ δ h p gT (.inl pr) ts (base + latticePoint L x)‖ ≤
      cψ ^ Fintype.card (GNode (nativeCoupleLayered D hS layer hLayer pr).garden.tree) *
        pairBound D hS L γ δ (fun q => h q u.upper.1.1 u.upper.1.1) layer hLayer base pr x := by
  rw [slotFW_regional_couple D hS layer hLayer L γ δ h p gT u hp]
  have key := norm_kernelLeavesW_le L γ δ (fun q => h q u.upper.1.1 u.upper.1.1)
    (nativeCoupleLayered D hS layer hLayer pr) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0
    (base + latticePoint L x) (fun _ => 0) 0
    (rowTopWeight p (gT u.upper.1.1) (nativeCoupleLayered D hS layer hLayer pr)
      ![coupleRootParents p D hS layer hLayer pr 0, coupleRootParents p D hS layer hLayer pr 1])
    (cψ ^ Fintype.card (GNode (nativeCoupleLayered D hS layer hLayer pr).garden.tree))
    (fun k => norm_rowTopWeight_le p (gT u.upper.1.1) (nativeCoupleLayered D hS layer hLayer pr)
      ![coupleRootParents p D hS layer hLayer pr 0, coupleRootParents p D hS layer hLayer pr 1] cψ hc
      (hg u.upper.1.1) k)
    (native_couple_lone D hS layer hLayer pr) (couple_hF hF pr x)
  unfold coupleLeavesTop pairBound majSum
  exact key

theorem norm_slotFW_chain_le (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms) (hva : v ≠ u.upper)
    (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖gT j x‖ ≤ cψ) (base : Mom d)
    (hF : HF D hS L (fun q => h q u.upper.1.1 u.upper.1.1) layer base) (ts : Fin 2 → ℝ) (x : Fin d → ℤ) :
    ‖slotFW D hS layer hLayer L γ δ h p gT (.inr v) ts (base + latticePoint L x)‖ ≤
      cψ ^ Fintype.card (GNode (nativeChainLayered D hS layer hLayer v).garden.tree) *
        chainBound D hS L γ δ (fun q => h q u.upper.1.1 u.upper.1.1) layer hLayer base v := by
  rw [slotFW_regional_chain D hS layer hLayer L γ δ h p gT u hv hva]
  have key := norm_kernelLeavesW_le L γ δ (fun q => h q u.upper.1.1 u.upper.1.1)
    (nativeChainLayered D hS layer hLayer v) (fun _ => ts 0) (ts 1)
    (base + latticePoint L x) (fun _ => 0) 0
    (rowTopWeight p (gT u.upper.1.1) (nativeChainLayered D hS layer hLayer v) ![treeRootParent p D hS layer hLayer v])
    (cψ ^ Fintype.card (GNode (nativeChainLayered D hS layer hLayer v).garden.tree))
    (fun k => norm_rowTopWeight_le p (gT u.upper.1.1) (nativeChainLayered D hS layer hLayer v)
      ![treeRootParent p D hS layer hLayer v] cψ hc (hg u.upper.1.1) k)
    (native_chain_lone D hS layer hLayer v) (chain_hF hF v x)
  have hmaj := majSum_le L (fun q => h q u.upper.1.1 u.upper.1.1) (nativeChainLayered D hS layer hLayer v) base
    (native_chain_lone D hS layer hLayer v) (chain_hF_base hF v) (fun _ => 0) 0 x
  unfold majSum at hmaj
  unfold treeLeavesTop chainBound
  refine key.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_left hmaj (by positivity)

theorem continuous_slotFW_couple (u : CLBlock S) {pr : SourcePair S} (hp : pr ∈ clRegionalPairs hS u.atoms)
    (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖gT j x‖ ≤ cψ) (base : Mom d)
    (hF : HF D hS L (fun q => h q u.upper.1.1 u.upper.1.1) layer base) (x : Fin d → ℤ) :
    Continuous fun ts : Fin 2 → ℝ => slotFW D hS layer hLayer L γ δ h p gT (.inl pr) ts (base + latticePoint L x) := by
  have e : (fun ts : Fin 2 → ℝ => slotFW D hS layer hLayer L γ δ h p gT (.inl pr) ts (base + latticePoint L x)) =
      fun ts => coupleLeavesTop L γ δ p (gT u.upper.1.1) (coupleRootParents p D hS layer hLayer pr 0)
        (coupleRootParents p D hS layer hLayer pr 1) (nativeCoupleLayered D hS layer hLayer pr)
        (layerProfiles (nativeCoupleLayered D hS layer hLayer pr) (fun q => h q u.upper.1.1 u.upper.1.1))
        (ts 0) (ts 1) (base + latticePoint L x) :=
    funext fun ts => slotFW_regional_couple D hS layer hLayer L γ δ h p gT u hp ts _
  rw [e]
  have hplain := native_couple_plain D hS layer hLayer pr
  have hc' := continuous_kernelLeavesW_time' L γ δ
    (layerProfiles (nativeCoupleLayered D hS layer hLayer pr) (fun q => h q u.upper.1.1 u.upper.1.1))
    (nativeCoupleLayered D hS layer hLayer pr) (base + latticePoint L x) (fun _ => 0) 0
    (rowTopWeight p (gT u.upper.1.1) (nativeCoupleLayered D hS layer hLayer pr)
      ![coupleRootParents p D hS layer hLayer pr 0, coupleRootParents p D hS layer hLayer pr 1])
    (cψ ^ Fintype.card (GNode (nativeCoupleLayered D hS layer hLayer pr).garden.tree))
    (fun k => norm_rowTopWeight_le p (gT u.upper.1.1) (nativeCoupleLayered D hS layer hLayer pr)
      ![coupleRootParents p D hS layer hLayer pr 0, coupleRootParents p D hS layer hLayer pr 1] cψ hc
      (hg u.upper.1.1) k)
    (no_flowerParent_of_plain _ hplain) (native_couple_lone D hS layer hLayer pr)
    (fun ℓ hℓ => by
      have := couple_hF hF pr x ℓ hℓ
      simpa only [layerProfiles_leaf] using this)
  have hv : Continuous fun ts : Fin 2 → ℝ =>
      ((fun b : GBranch (nativeCoupleLayered D hS layer hLayer pr).garden.tree =>
        if b.1.1 = 0 then ts 0 else ts 1), (0 : ℝ)) := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro b
    by_cases hb : b.1.1 = 0
    · simpa only [hb, ite_true] using (continuous_apply (0 : Fin 2))
    · simpa only [hb, ite_false] using (continuous_apply (1 : Fin 2))
  have h2 := hc'.comp hv
  unfold coupleLeavesTop
  exact h2

theorem continuous_slotFW_chain (u : CLBlock S) {v : GBranch S.tree} (hv : v ∈ u.atoms) (hva : v ≠ u.upper)
    (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖gT j x‖ ≤ cψ) (base : Mom d)
    (hF : HF D hS L (fun q => h q u.upper.1.1 u.upper.1.1) layer base) (x : Fin d → ℤ) :
    Continuous fun ts : Fin 2 → ℝ => slotFW D hS layer hLayer L γ δ h p gT (.inr v) ts (base + latticePoint L x) := by
  have e : (fun ts : Fin 2 → ℝ => slotFW D hS layer hLayer L γ δ h p gT (.inr v) ts (base + latticePoint L x)) =
      fun ts => treeLeavesTop L γ δ p (gT u.upper.1.1) (treeRootParent p D hS layer hLayer v)
        (nativeChainLayered D hS layer hLayer v)
        (layerProfiles (nativeChainLayered D hS layer hLayer v) (fun q => h q u.upper.1.1 u.upper.1.1))
        (ts 0) (ts 1) (base + latticePoint L x) :=
    funext fun ts => slotFW_regional_chain D hS layer hLayer L γ δ h p gT u hv hva ts _
  rw [e]
  have hT := native_chain_paired D hS layer hLayer v
  have hc' := continuous_kernelLeavesW_time' L γ δ
    (layerProfiles (nativeChainLayered D hS layer hLayer v) (fun q => h q u.upper.1.1 u.upper.1.1))
    (nativeChainLayered D hS layer hLayer v) (base + latticePoint L x) (fun _ => 0) 0
    (rowTopWeight p (gT u.upper.1.1) (nativeChainLayered D hS layer hLayer v) ![treeRootParent p D hS layer hLayer v])
    (cψ ^ Fintype.card (GNode (nativeChainLayered D hS layer hLayer v).garden.tree))
    (fun k => norm_rowTopWeight_le p (gT u.upper.1.1) (nativeChainLayered D hS layer hLayer v)
      ![treeRootParent p D hS layer hLayer v] cψ hc (hg u.upper.1.1) k)
    (no_flowerParent_of_pairedTree _ hT) (native_chain_lone D hS layer hLayer v)
    (fun ℓ hℓ => by
      have := chain_hF hF v x ℓ hℓ
      simpa only [layerProfiles_leaf] using this)
  have hf : Continuous fun ts : Fin 2 → ℝ =>
      ((fun _ : GBranch (nativeChainLayered D hS layer hLayer v).garden.tree => ts 0), ts 1) :=
    (continuous_pi fun _ => continuous_apply 0).prodMk (continuous_apply 1)
  have h2 := hc'.comp hf
  unfold treeLeavesTop
  exact h2

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The `cψ`-constant of a unit (one power per native node of each regional row). -/
def unitCψ (blk : J → CLBlock S) (cψ : ℝ) (j : J) : ℝ :=
  (∏ pr ∈ clRegionalPairs hS (blk j).atoms,
      cψ ^ Fintype.card (GNode (nativeCoupleLayered D hS layer hLayer pr).garden.tree)) *
    ∏ v ∈ (blk j).atoms.erase (blk j).upper,
      cψ ^ Fintype.card (GNode (nativeChainLayered D hS layer hLayer v).garden.tree)

theorem unitCψ_nonneg (blk : J → CLBlock S) (cψ : ℝ) (hc : 1 ≤ cψ) (j : J) :
    0 ≤ unitCψ D hS layer hLayer blk cψ j :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (by linarith) _)
    (Finset.prod_nonneg fun _ _ => pow_nonneg (by linarith) _)

/-- **The regional bound of the frontier-weighted slot family.** -/
def regBoundFW (blk : J → CLBlock S) (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖gT j x‖ ≤ cψ) (base : Mom d)
    (hL : L ≠ 0) (hF : ∀ j, HF D hS L (unitProfile blk h j) layer base) :
    RegBound blk hS (slotFW D hS layer hLayer L γ δ h p gT) L base where
  lb j x := unitCψ D hS layer hLayer blk cψ j *
    localBound D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j)) x
  lbC j := unitCψ D hS layer hLayer blk cψ j *
    lbConst D hS L γ δ (unitProfile blk h j) layer hLayer base (regionOf (blk j))
  nonneg j x := mul_nonneg (unitCψ_nonneg D hS layer hLayer blk cψ hc j) (localBound_nonneg _ _)
  norm_le j x top u := by
    have hint : clInteriorBranches (regionOf (blk j)) = (blk j).atoms.erase (blk j).upper := rfl
    unfold starProdG unitCψ localBound
    rw [hint, norm_mul, norm_prod, norm_prod, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun pr hpr => ?_))
      (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v hv => ?_))
      (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      (Finset.prod_nonneg fun _ _ => mul_nonneg (pow_nonneg (by linarith) _) ?_)
    · exact norm_slotFW_couple_le D hS layer hLayer L γ δ h p gT (blk j) hpr cψ hc hg base (hF j) _ _
    · obtain ⟨hva, hvU⟩ := Finset.mem_erase.mp hv
      exact norm_slotFW_chain_le D hS layer hLayer L γ δ h p gT (blk j) hvU hva cψ hc hg base (hF j) _ _
    · unfold pairBound majSum
      exact mul_nonneg (by positivity) (tsum_nonneg fun ρ => Finset.prod_nonneg fun ℓ _ => abs_nonneg _)
  summable j β := ((summable_tsum_localBound (γ := γ) (δ := δ) (hLayer := hLayer) (blk j).isBlock
    (regionOf (blk j)) (hF j) hL β).1).mul_left _
  tsum_le j β := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (summable_tsum_localBound (γ := γ) (δ := δ) (hLayer := hLayer) (blk j).isBlock
      (regionOf (blk j)) (hF j) hL β).2 (unitCψ_nonneg D hS layer hLayer blk cψ hc j)
  meas j := ⟨fun pr hpr n => (continuous_slotFW_couple D hS layer hLayer L γ δ h p gT (blk j) hpr cψ hc hg base
      (hF j) n).measurable,
    fun v hv n => (continuous_slotFW_chain D hS layer hLayer L γ δ h p gT (blk j) (Finset.mem_erase.mp hv).2
      (Finset.mem_erase.mp hv).1 cψ hc hg base (hF j) n).measurable⟩

end Bound

/-! ## The unit factor of the weighted slot family is the pinned kernel -/

section Unit

variable {w d : ℕ} {ι : Type*} {J : Type} [Fintype J] [DecidableEq J] {Q : J → ι → Prop}

end Unit

end WaveTurbulence.Flower.Stage1WVine
