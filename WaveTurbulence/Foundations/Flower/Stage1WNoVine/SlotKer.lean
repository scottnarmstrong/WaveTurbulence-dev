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

theorem IsMult.mono {d A : ℕ} {c : Mom d → ℂ} {K K' : ℝ} (h : IsMult A c K) (hK : K ≤ K') : IsMult A c K' :=
  fun a ha => (h a ha).trans (ENNReal.ofReal_le_ofReal hK)

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

theorem CenSup.mulM {r A d : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : CenSup A B f μ) {c : Mom d → ℂ} {K : ℝ} (hK : 0 < K) (hc : IsMult A c K) :
    CenSup A B (fun t k => c k * f t k) (ENNReal.ofReal K * μ) :=
  CenSup.mul_left h c K hK hc

theorem Sup.mulM {r A d : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ} {μ : ℝ≥0∞}
    (h : Sup A B f μ) {c : Mom d → ℂ} {K : ℝ} (hK : 0 < K) (hc : IsMult A c K) :
    Sup A B (fun t k => c k * f t k) (ENNReal.ofReal K * μ) :=
  Sup.mul_left h c K hK hc

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

theorem continuous_coupleLeavesTopR_time {d : ℕ} (L γ δ : ℝ) (p : ℕ) (g : Fin 2 → Mom d → ℂ) (q q' : ℕ)
    (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (hplain : LG.garden.IsPlain) (k : Mom d)
    (M : ℝ) (hm : ∀ k', ‖rowTopWeightR p g LG ![q, q'] k'‖ ≤ M)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => coupleLeavesTopR L γ δ p g q q' LG H (ts 0) (ts 1) k) := by
  have hc := continuous_kernelLeavesW_time L γ δ H LG k (fun _ => 0) 0 (rowTopWeightR p g LG ![q, q']) M hm
    (no_flowerParent_of_plain LG.garden hplain) (card_lone_le_one_of_plain LG.garden hplain) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) :=
    fun ts => ((fun b => if b.1.1 = 0 then ts 0 else ts 1), 0)
  have hu : Continuous u := by
    apply Continuous.prodMk _ continuous_const
    apply continuous_pi
    intro b
    by_cases h : b.1.1 = 0
    · simpa only [h, ite_true] using (continuous_apply (0 : Fin 2))
    · simpa only [h, ite_false] using (continuous_apply (1 : Fin 2))
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    kernelLeavesW L γ δ LG H x.1 x.2 k (fun _ => 0) 0 (rowTopWeightR p g LG ![q, q'])) ∘ u)
  exact hc.comp hu

theorem continuous_treeLeavesTop_time {d : ℕ} (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q : ℕ)
    (LG : LayeredGarden 1) (H : LeafProfiles 1 d)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1) (k : Mom d)
    (M : ℝ) (hm : ∀ k', ‖rowTopWeight p g LG ![q] k'‖ ≤ M)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => treeLeavesTop L γ δ p g q LG H (ts 0) (ts 1) k) := by
  have hc := continuous_kernelLeavesW_time L γ δ H LG k (fun _ => 0) 0 (rowTopWeight p g LG ![q]) M hm
    hflower hlone hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) := fun ts => ((fun _ => ts 0), ts 1)
  have hu : Continuous u := (continuous_pi fun _ => continuous_apply 0).prodMk (continuous_apply 1)
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    kernelLeavesW L γ δ LG H x.1 x.2 k (fun _ => 0) 0 (rowTopWeight p g LG ![q])) ∘ u)
  exact hc.comp hu

/-- The kernel only sees an upper time through the constraint below `layer + 1`. -/
theorem kernelLeavesW_up_congr {w d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (up up' : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) (m : (GNode LG.garden.tree → Mom d) → ℂ)
    (h : ∀ b, up b = up' b ∨ ((LG.layer b.toNode : ℝ) + 1 ≤ up b ∧ (LG.layer b.toNode : ℝ) + 1 ≤ up' b)) :
    kernelLeavesW L γ δ LG H up s k₀ nroot nfl m = kernelLeavesW L γ δ LG H up' s k₀ nroot nfl m := by
  have hD : kDomain LG up s = kDomain LG up' s := by
    ext τ
    simp only [kDomain, Set.mem_setOf_eq]
    constructor
    · intro hτ b
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hτ b
      refine ⟨h1, h2, h3, ?_, h5, h6⟩
      rcases h b with e | ⟨-, e2⟩
      · rw [← e]; exact h4
      · linarith
    · intro hτ b
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hτ b
      refine ⟨h1, h2, h3, ?_, h5, h6⟩
      rcases h b with e | ⟨e1, -⟩
      · rw [e]; exact h4
      · linarith
  unfold kernelLeavesW
  rw [hD]

/-- Every branch of tree `j` lies at a layer at most that of the root of tree `j`. -/
theorem branch_layer_le_root {w : ℕ} (LG : LayeredGarden w) (b : GBranch LG.garden.tree) :
    LG.layer b.toNode ≤ LG.layer (GNode.root LG.garden.tree b.1.1) := by
  obtain ⟨r, hr1, hr2, hle⟩ := FlowerP7.layer_le_root LG b.1.2.length b rfl
  have e : r.toNode = GNode.root LG.garden.tree b.1.1 := Subtype.ext (Prod.ext hr1 hr2)
  rw [← e]
  exact hle

/-- Freezing the clock of arm `0` of a couple at `c`, when every branch of arm `0` lies below `c`. -/
theorem coupleLeavesTopR_freeze0 {d : ℕ} (L γ δ : ℝ) (p : ℕ) (g : Fin 2 → Mom d → ℂ) (q q' : ℕ)
    (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (k : Mom d) (c t s : ℝ)
    (hlay : ((LG.layer (GNode.root LG.garden.tree 0) : ℕ) : ℝ) + 1 ≤ c) (hct : c ≤ t) :
    coupleLeavesTopR L γ δ p g q q' LG H t s k = coupleLeavesTopR L γ δ p g q q' LG H c s k := by
  unfold coupleLeavesTopR
  refine kernelLeavesW_up_congr L γ δ LG H _ _ 0 k _ 0 _ fun b => ?_
  by_cases hb : b.1.1 = 0
  · right
    simp only [hb, ite_true]
    have h1 := branch_layer_le_root LG b
    rw [hb] at h1
    have h2 : (LG.layer b.toNode : ℝ) ≤ LG.layer (GNode.root LG.garden.tree 0) := by exact_mod_cast h1
    constructor <;> linarith
  · left
    simp only [hb, ite_false]

/-- Freezing the clock of arm `1` of a couple. -/
theorem coupleLeavesTopR_freeze1 {d : ℕ} (L γ δ : ℝ) (p : ℕ) (g : Fin 2 → Mom d → ℂ) (q q' : ℕ)
    (LG : LayeredGarden 2) (H : LeafProfiles 2 d) (k : Mom d) (c t s : ℝ)
    (hlay : ((LG.layer (GNode.root LG.garden.tree 1) : ℕ) : ℝ) + 1 ≤ c) (hct : c ≤ s) :
    coupleLeavesTopR L γ δ p g q q' LG H t s k = coupleLeavesTopR L γ δ p g q q' LG H t c k := by
  unfold coupleLeavesTopR
  refine kernelLeavesW_up_congr L γ δ LG H _ _ 0 k _ 0 _ fun b => ?_
  by_cases hb : b.1.1 = 0
  · left
    simp only [hb, ite_true]
  · right
    simp only [hb, ite_false]
    have hb1 : b.1.1 = 1 := by omega
    have h1 := branch_layer_le_root LG b
    rw [hb1] at h1
    have h2 : (LG.layer b.toNode : ℝ) ≤ LG.layer (GNode.root LG.garden.tree 1) := by exact_mod_cast h1
    constructor <;> linarith

/-- Freezing the clock of a tree. -/
theorem treeLeavesTop_freeze {d : ℕ} (L γ δ : ℝ) (p : ℕ) (g : Mom d → ℂ) (q : ℕ)
    (LG : LayeredGarden 1) (H : LeafProfiles 1 d) (k : Mom d) (c t s : ℝ)
    (hlay : ((LG.layer (GNode.root LG.garden.tree 0) : ℕ) : ℝ) + 1 ≤ c) (hct : c ≤ t) :
    treeLeavesTop L γ δ p g q LG H t s k = treeLeavesTop L γ δ p g q LG H c s k := by
  unfold treeLeavesTop
  refine kernelLeavesW_up_congr L γ δ LG H _ _ s k _ 0 _ fun b => ?_
  right
  have hb0 : b.1.1 = 0 := Subsingleton.elim _ _
  have h1 := branch_layer_le_root LG b
  rw [hb0] at h1
  have h2 : (LG.layer b.toNode : ℝ) ≤ LG.layer (GNode.root LG.garden.tree 0) := by exact_mod_cast h1
  constructor <;> linarith

/-! ### The frontier node set of a regular object -/

/-- The nodes carrying a frontier factor (layer `< p`, parent layer `= p`). -/
def topSetR {v : ℕ} (p : ℕ) (LG : LayeredGarden v) (qr : Fin v → ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun a => LG.layer a < p ∧ rowParentLayer LG qr a = p

theorem rowParentLayer_root {v : ℕ} (LG : LayeredGarden v) (qr : Fin v → ℕ) (j : Fin v) :
    rowParentLayer LG qr (GNode.root LG.garden.tree j) = qr j := by
  unfold rowParentLayer
  exact if_pos rfl

theorem rowTopWeightR_eq_topSet {v d : ℕ} (p : ℕ) (g : Fin v → Mom d → ℂ) (LG : LayeredGarden v)
    (qr : Fin v → ℕ) (k : GNode LG.garden.tree → Mom d) :
    rowTopWeightR p g LG qr k = ∏ a ∈ topSetR p LG qr, g a.1.1 (k a) := by
  unfold rowTopWeightR topSetR topPsi
  rw [Finset.prod_filter]

theorem card_topSetR_le_one {v d : ℕ} (p : ℕ) (LG : LayeredGarden v) (qr : Fin v → ℕ)
    (k : GNode LG.garden.tree → Mom d)
    (h : ‖rowTopWeightR p (fun _ _ => (2 : ℂ)) LG qr k‖ ≤ 2) : (topSetR p LG qr).card ≤ 1 := by
  rw [rowTopWeightR_eq_topSet, Finset.prod_const, norm_pow] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2] at h
  by_contra hc
  have : (2 : ℝ) ^ 2 ≤ 2 ^ (topSetR p LG qr).card := pow_le_pow_right₀ (by norm_num) (by omega)
  norm_num at this
  linarith

theorem topSetR_mono {v : ℕ} (p : ℕ) (LG : LayeredGarden v) (qr qw : Fin v → ℕ)
    (h : ∀ j, qw j = qr j ∨ ¬ (LG.layer (GNode.root LG.garden.tree j) < p ∧ qw j = p)) :
    topSetR p LG qw ⊆ topSetR p LG qr := by
  intro a ha
  simp only [topSetR, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
  refine ⟨ha.1, ?_⟩
  unfold rowParentLayer at ha ⊢
  by_cases hr : a.1.2 = []
  · simp only [hr, ite_true] at ha ⊢
    have e : a = GNode.root LG.garden.tree a.1.1 := Subtype.ext (Prod.ext rfl hr)
    rcases h a.1.1 with h1 | h1
    · rw [← h1]; exact ha.2
    · exact absurd ⟨by rw [← e]; exact ha.1, ha.2⟩ h1
  · simp only [hr, ite_false] at ha ⊢
    exact ha.2

/-- **Coherent objects with a root factor removed**: if the frontier set has at most one node, removing root
factors either changes nothing or removes every factor. -/
theorem rowTopWeightR_of_subset {v d : ℕ} (p : ℕ) (g : Fin v → Mom d → ℂ) (LG : LayeredGarden v)
    (qr qw : Fin v → ℕ) (hsub : topSetR p LG qw ⊆ topSetR p LG qr) (hcard : (topSetR p LG qr).card ≤ 1)
    (k : GNode LG.garden.tree → Mom d) :
    rowTopWeightR p g LG qw k =
      if topSetR p LG qw = topSetR p LG qr then rowTopWeightR p g LG qr k else 1 := by
  by_cases heq : topSetR p LG qw = topSetR p LG qr
  · rw [if_pos heq, rowTopWeightR_eq_topSet, rowTopWeightR_eq_topSet, heq]
  · rw [if_neg heq, rowTopWeightR_eq_topSet]
    have hss : topSetR p LG qw ⊂ topSetR p LG qr := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩
    have hlt := Finset.card_lt_card hss
    have h0 : topSetR p LG qw = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [h0, Finset.prod_empty]

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

/-- **A superposition of a time-continuous kernel extends to the closure of the box.** -/
theorem Sup.closure_of_continuous {r A d : ℕ} {B : Set (Fin r → ℝ)} {f : (Fin r → ℝ) → Mom d → ℂ}
    {μ : ℝ≥0∞} (h : Sup A B f μ) (hf : ∀ k, Continuous fun t => f t k) : Sup A (closure B) f μ := by
  obtain ⟨Λ, hcnt, w, m, a, h1, h2, h3, h5, h6⟩ := h
  refine ⟨Λ, hcnt, w, m, a, h1, h2, h3, fun t ht k => ?_, h6⟩
  have hb : ∀ l t', ‖(w l : ℂ) * a l k * fsPhase (m l) t'‖ ≤ w l := by
    intro l t'
    rw [norm_mul, norm_mul, norm_fsPhase, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h1 l)]
    exact mul_le_of_le_one_right (h1 l) (snorm_le_one_pointwise _ _ (h3 l) k)
  have hsum : ∀ t', Summable (fun l => (w l : ℂ) * a l k * fsPhase (m l) t') :=
    fun t' => Summable.of_norm_bounded h2 (hb · t')
  have hcont : Continuous (fun t' => ∑' l, (w l : ℂ) * a l k * fsPhase (m l) t') :=
    continuous_tsum (fun l => continuous_const.mul (continuous_fsPhase (m l))) h2 (fun l t' => hb l t')
  have hclosed : IsClosed {t' | ∑' l, (w l : ℂ) * a l k * fsPhase (m l) t' = f t' k} :=
    isClosed_eq hcont (hf k)
  have hBsub : B ⊆ {t' | ∑' l, (w l : ℂ) * a l k * fsPhase (m l) t' = f t' k} :=
    fun t' ht' => (h5 t' ht' k).tsum_eq
  have heq := hclosed.closure_subset_iff.mpr hBsub ht
  rw [← heq]
  exact (hsum t).hasSum

end WaveTurbulence.Flower.Stage1WNoVine
