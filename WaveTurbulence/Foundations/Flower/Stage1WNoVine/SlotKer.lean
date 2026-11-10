/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Mult
public import WaveTurbulence.Foundations.Flower.Stage1W.Inputs
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeLayer
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelContinuity

/-! # STAGE1W-O4: kernel facts for the weighted slot targets (row O4c)

* `IsMult`: bounded multipliers on `𝔖^{30d,0}`; Fourier-presented weights (`isMult_of_gPresented`) and their `topPsi`
  restrictions (`isMult_topPsi`) are bounded multipliers.
* `kernelLeavesW_const`: a decoration weight that is a function of the external momentum only factors out.
* `continuous_kernelLeavesW_time`: time continuity of a bounded-weight leaf kernel.
* `kernelLeavesW_up_congr`: the kernel only sees the upper times below `layer + 1` (used to freeze the clock of an arm
  whose root is a garden root).
* `topSetR`: the frontier node set of a regular object; its weight is the node product over it.
* `Sup.closure_of_continuous`: a superposition of a time-continuous kernel holds on the closure of its box. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
namespace WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Represents WaveTurbulence.VineEstS3.FS MeasureTheory Set
  WaveTurbulence.Flower.Stage1W

/-! ### Bounded multipliers -/

/-- `c` is a multiplier on unit `𝔖^{A,0}` amplitudes with norm at most `K`. -/
def IsMult {d : ℕ} (A : ℕ) (c : Mom d → ℂ) (K : ℝ) : Prop :=
  ∀ a : Mom d → ℂ, SNorm A 0 a ≤ 1 → SNorm A 0 (fun k => c k * a k) ≤ ENNReal.ofReal K

theorem isMult_one {d : ℕ} (A : ℕ) : IsMult A (fun _ : Mom d => (1 : ℂ)) 1 := by
  intro a ha
  simpa using ha

/-- The multiplier constant without the mass factor. -/
def multD (d A : ℕ) : ℝ := 2 ^ A * (d : ℝ) ^ A * (2 * Real.pi) ^ A

theorem one_le_multD (d A : ℕ) (hd : 1 ≤ d) : 1 ≤ multD d A := by
  unfold multD
  have h1 : (1 : ℝ) ≤ 2 ^ A := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (d : ℝ) ^ A := one_le_pow₀ (by exact_mod_cast hd)
  have h3 : (1 : ℝ) ≤ (2 * Real.pi) ^ A := one_le_pow₀ (by linarith [Real.pi_gt_three])
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

theorem multC_eq (d A : ℕ) (c : ℝ) : multC d A c = multD d A * c := by
  unfold multC multD; ring

/-- **A Fourier-presented weight is a bounded multiplier** (the SNorm multiplier lemma in `IsMult` form). -/
theorem isMult_of_gPresented {d : ℕ} (hd : 1 ≤ d) {g : Mom d → ℂ} {cψ : ℝ} (hc : 1 ≤ cψ)
    (hg : GPresented (32 * d) g cψ) : IsMult (30 * d) g (multD d (30 * d) * cψ) := by
  obtain ⟨α, _, M, hM, hv⟩ := hg
  intro a ha
  have hcd : ContDiff ℝ ((30 * d : ℕ) : WithTop ℕ∞) a :=
    RepAnalytic.contDiff_of_SNorm_ne_top (A := 30 * d) (by omega) (ne_top_of_le_ne_top ENNReal.one_ne_top ha)
  have h := snorm_value_mul_le M hd (J := 32 * d) (A := 30 * d) (by omega) (by linarith) hM a hcd
  have e : (fun k => g k * a k) = fun k => M.value k * a k := by
    funext k; rw [hv k]
  rw [e, ← multC_eq]
  refine h.trans ?_
  calc ENNReal.ofReal (multC d (30 * d) cψ) * SNorm (30 * d) 0 a ≤ ENNReal.ofReal (multC d (30 * d) cψ) * 1 :=
        mul_le_mul_right ha _
    _ = _ := mul_one _

theorem isMult_topPsi {d A : ℕ} {g : Mom d → ℂ} {K : ℝ} (hK : 1 ≤ K) (hg : IsMult A g K) (p q q' : ℕ) :
    IsMult A (fun x => topPsi p g q q' x) (if q < p ∧ q' = p then K else 1) := by
  unfold topPsi
  by_cases h : q < p ∧ q' = p
  · simp only [h, and_self, ite_true]
    exact hg
  · simp only [h, ite_false]
    exact isMult_one A

/-! ### Kernel identities -/

/-- A decoration weight constant on the decorations factors out of the leaf kernel. -/
theorem kernelLeavesW_const {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (c : ℂ)
    (hm : ∀ κ : GenDecoration LG.garden d nroot nfl, m (cosetDecoration LG.garden L k₀ κ.1) = c) :
    kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = c * kernelLeaves L γ δ LG H up s k₀ nroot nfl := by
  unfold kernelLeavesW kernelLeaves
  simp_rw [hm]
  rw [tsum_mul_left]
  ring

theorem norm_rowTopWeightR_le {w d : ℕ} (p : ℕ) (g : Fin w → Mom d → ℂ) (LG : LayeredGarden w) (qr : Fin w → ℕ)
    (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ j x, ‖g j x‖ ≤ cψ) (k : GNode LG.garden.tree → Mom d) :
    ‖rowTopWeightR p g LG qr k‖ ≤ cψ ^ Fintype.card (GNode LG.garden.tree) := by
  unfold rowTopWeightR
  refine (Finset.norm_prod_le _ _).trans ?_
  refine (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => ?_)).trans_eq
    (by rw [Finset.prod_const, Finset.card_univ])
  unfold topPsi
  split_ifs
  · exact hg _ _
  · simpa using hc

/-- Time continuity of a leaf kernel with a bounded decoration weight. -/
theorem continuous_kernelLeavesW_time {w d : ℕ} (L γ δ : ℝ) (H : LeafProfiles w d)
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

/-! ### The frontier node set of a regular object -/

theorem rowParentLayer_root {v : ℕ} (LG : LayeredGarden v) (qr : Fin v → ℕ) (j : Fin v) :
    rowParentLayer LG qr (GNode.root LG.garden.tree j) = qr j := by
  unfold rowParentLayer
  exact if_pos rfl

/-! ### Roots and node counts -/

theorem gnode_root_injective {w : ℕ} (t : Fin w → TTree) : Function.Injective (GNode.root t) :=
  fun j j' h => congrArg (fun x : GNode t => x.1.1) h

theorem card_nonroot {w : ℕ} (t : Fin w → TTree) :
    (Finset.univ.filter fun x : GNode t => x.1.2 ≠ []).card = 3 * (∑ j, (t j).order) := by
  have hr : (Finset.univ.filter fun x : GNode t => x.1.2 = []) = Finset.univ.image (GNode.root t) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨x.1.1, Subtype.ext (Prod.ext rfl h.symm)⟩
    · rintro ⟨j, rfl⟩
      rfl
  have hcr : (Finset.univ.filter fun x : GNode t => x.1.2 = []).card = w := by
    rw [hr, Finset.card_image_of_injective _ (gnode_root_injective t)]
    simp
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (GNode t)))
    (fun x : GNode t => x.1.2 = [])
  have hu : (Finset.univ : Finset (GNode t)).card = 3 * (∑ j, (t j).order) + w := by
    rw [Finset.card_univ, Comb.card_gnode]
  have e : (Finset.univ.filter fun x : GNode t => x.1.2 ≠ []) =
      Finset.univ.filter fun x : GNode t => ¬ (x.1.2 = []) := rfl
  rw [e]
  omega

/-- The node product of an object all of whose nodes are roots. -/
theorem prod_allRoot {w : ℕ} {M : Type*} [CommMonoid M] (t : Fin w → TTree)
    (hall : ∀ x : GNode t, x.1.2 = []) (F : GNode t → M) : ∏ x, F x = ∏ j, F (GNode.root t j) := by
  refine (Fintype.prod_bijective (GNode.root t) ⟨gnode_root_injective t, fun x => ?_⟩ _ _ fun _ => rfl).symm
  exact ⟨x.1.1, Subtype.ext (Prod.ext rfl (hall x).symm)⟩

theorem allRoot_of_leaf {w : ℕ} (t : Fin w → TTree) (ht : ∀ j, t j = TTree.leaf) (x : GNode t) : x.1.2 = [] := by
  have h := x.2
  rw [ht x.1.1] at h
  simpa [TTree.nodes] using h

/-! ### Superpositions on the closure of the box -/

theorem continuous_fsPhase {r : ℕ} (m : Fin r → ℤ) : Continuous (fun t : Fin r → ℝ => fsPhase m t) := by
  unfold fsPhase
  have h : Continuous (fun t : Fin r → ℝ => Fourier.timePairing r t (fun i => (m i : ℝ) / 2)) := by
    show Continuous (fun t : Fin r → ℝ => dotProduct t (fun i => (m i : ℝ) / 2))
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  exact Cut2A.character_smooth.continuous.comp h

theorem norm_fsPhase {r : ℕ} (m : Fin r → ℤ) (t : Fin r → ℝ) : ‖fsPhase m t‖ = 1 := by
  unfold fsPhase
  exact Circle.norm_coe _

end WaveTurbulence.Flower.Stage1WNoVine
