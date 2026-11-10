/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.TreeTranslate
public import WaveTurbulence.Foundations.RegularAsymptotics.KernelContinuity

/-!
# Leafwise kernels (for LG-SPINE, TARGET L2065–L2067)

TARGET L2065–L2067 modifies the inputs of a few individual leaves (weights, derivatives) of a regular couple or tree.
B1's `kernelK` takes a **layer-indexed** input family; here the same decoration sum with a **leaf-indexed** family
`Fl : GLeaf → (ℝ^d → ℝ)`:

* `kernelKLeaf`, `KQstarLeaf`, `KTstarLeaf`; `kernelK F = kernelKLeaf (ℓ ↦ F 𝔏_ℓ)` (`kernelK_eq_kernelKLeaf`, `rfl`);
* **multilinearity** in each input leaf: `kernelKLeaf_update_smul`, `kernelKLeaf_update_add` (the latter under the
  leafwise summability of `summable_kernelKLeaf_summand`);
* leafwise summability (`summable_kernelKLeaf_summand`) and continuity in all times (`continuous_kernelKLeaf_time`,
  `continuous_KTstarLeaf_time`), with the uniform input-leaf majorant of lg-spine;
* the RA2 translation/relayering/`s`-independence lemmas in leafwise form: `KQstarLeaf_shift`, `KTstarLeaf_shift`,
  `KTstarLeaf_relayer`, `KTstarLeaf_indep_of_le` (the layer of a leaf never enters a leafwise kernel's inputs).
-/

@[expose] public section

open MeasureTheory Set Finset Filter

namespace WaveTurbulence.Regref

open TTree

variable (L γ δ : ℝ) {d : ℕ}

/-- **The one kernel with leafwise inputs** `Fl ℓ` (B1 `kernelK` with `F_{𝔏_ℓ}` replaced by `Fl ℓ`). -/
noncomputable def kernelKLeaf {w : ℕ} (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden, (Fl ℓ (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

/-- The leafwise couple kernel `K*_𝒬[Fl](t, s, k)`. -/
noncomputable def KQstarLeaf (LG : LayeredGarden 2) (Fl : GLeaf LG.garden.tree → Mom d → ℝ) (t s : ℝ)
    (k : Mom d) : ℂ :=
  kernelKLeaf L γ δ LG Fl (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0

/-- The leafwise tree kernel `K*_𝒯[Fl](t, s, k)`. -/
noncomputable def KTstarLeaf (LG : LayeredGarden 1) (Fl : GLeaf LG.garden.tree → Mom d → ℝ) (t s : ℝ)
    (k : Mom d) : ℂ :=
  kernelKLeaf L γ δ LG Fl (fun _ => t) s k (fun _ => 0) 0

/-! ### Summability, continuity -/

variable {L γ δ}

/-- The leafwise summand and its majorant. -/
noncomputable def leafSummand {w : ℕ} (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) : ℂ :=
  (epsDec LG.garden κ.1 : ℂ) *
    phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
    ∏ ℓ ∈ inputLeaves LG.garden, (Fl ℓ (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

theorem norm_leafSummand_le {w : ℕ} (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Mom d → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    ‖leafSummand (L := L) (γ := γ) (δ := δ) LG Fl up s k₀ κ‖ ≤
      ∏ ℓ ∈ inputLeaves LG.garden, |Fl ℓ (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| := by
  unfold leafSummand
  rw [norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have he := abs_epsDec_le_one LG.garden κ.1
  have hp := LGSpine.norm_phaseIntegral_le_one L γ δ LG up s (cosetDecoration LG.garden L k₀ κ.1)
  have hprod : 0 ≤ ∏ ℓ ∈ inputLeaves LG.garden, |Fl ℓ (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| :=
    prod_nonneg fun _ _ => abs_nonneg _
  have hmul : |epsDec LG.garden κ.1| * ‖phaseIntegral L γ δ LG.garden (kDomain LG up s) s
      (cosetDecoration LG.garden L k₀ κ.1)‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans (by simpa only [one_mul] using hp)
  exact (mul_le_mul_of_nonneg_right hmul hprod).trans_eq (one_mul _)

/-- **Leafwise summable majorant** (uniform in the times): each input leaf summable on its coset suffices. -/
theorem summable_leafMajorant {w : ℕ} (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Mom d → ℝ)
    (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |Fl ℓ (k₀ + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d nroot nfl =>
      ∏ ℓ ∈ inputLeaves LG.garden, |Fl ℓ (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode)| := by
  classical
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let f : ι → (Fin d → ℤ) → ℝ := fun ℓ n => |Fl ℓ.1 (k₀ + latticePoint L n)|
  have hf : Summable (fun z : ι → (Fin d → ℤ) => ∏ ℓ, f ℓ (z ℓ)) :=
    summable_pi_prod f (fun _ _ => abs_nonneg _) (fun ℓ => hF ℓ.1 ℓ.2)
  have h := hf.comp_injective (LGSpine.genDecoration_input_injective LG nroot nfl hlone)
  refine h.congr fun κ => ?_
  rw [← Finset.prod_coe_sort]
  rfl

/-- **Continuity of the leafwise kernel in all times** (no flower parents, at most one lone leaf per tree). -/
theorem continuous_kernelKLeaf_time {w : ℕ} (LG : LayeredGarden w) (Fl : GLeaf LG.garden.tree → Mom d → ℝ)
    (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hflower : ∀ b, ¬ LG.garden.IsFlowerParent b)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |Fl ℓ (k₀ + latticePoint L n)|) :
    Continuous (fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
      kernelKLeaf L γ δ LG Fl x.1 x.2 k₀ nroot nfl) := by
  unfold kernelKLeaf
  apply Continuous.mul continuous_const
  apply continuous_tsum
  · intro κ
    exact (continuous_const.mul
      (LGSpine.continuous_phaseIntegral_no_flower L γ δ LG hflower
        (cosetDecoration LG.garden L k₀ κ.1))).mul continuous_const
  · exact summable_leafMajorant LG Fl k₀ nroot nfl hlone hF
  · intro κ x
    exact norm_leafSummand_le LG Fl x.1 x.2 k₀ κ

theorem continuous_KTstarLeaf_time (LG : LayeredGarden 1) (hT : IsPairedTree LG.garden)
    (Fl : GLeaf LG.garden.tree → Mom d → ℝ) (k : Mom d)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden, Summable fun n : Fin d → ℤ => |Fl ℓ (k + latticePoint L n)|) :
    Continuous (fun ts : Fin 2 → ℝ => KTstarLeaf L γ δ LG Fl (ts 0) (ts 1) k) := by
  have hc := continuous_kernelKLeaf_time (L := L) (γ := γ) (δ := δ) LG Fl k (fun _ => 0) 0
    (LGSpine.no_flowerParent_of_pairedTree LG.garden hT)
    (card_lone_le_one (fun _ _ h h' => hT.eq_of_isLone h h')) hF
  let u : (Fin 2 → ℝ) → ((GBranch LG.garden.tree → ℝ) × ℝ) := fun ts => ((fun _ => ts 0), ts 1)
  have hu : Continuous u := by fun_prop
  change Continuous ((fun x : (GBranch LG.garden.tree → ℝ) × ℝ =>
    kernelKLeaf L γ δ LG Fl x.1 x.2 k (fun _ => 0) 0) ∘ u)
  exact hc.comp hu

/-! ### Multilinearity in each input leaf -/

/-! ### Translation, relayering and `s`-independence, leafwise -/

variable (L γ δ)

/-- **Shifting a single-layer couple to layer `0`, leafwise inputs.** -/
theorem KQstarLeaf_shift (LG : LayeredGarden 2) (hG : IsCouple LG.garden) (Fl : GLeaf LG.garden.tree → Mom d → ℝ)
    (r : ℕ) (hr : ∀ a, LG.layer a = r) (t s : ℝ) (k : Mom d) :
    KQstarLeaf L γ δ LG Fl t s k = KQstarLeaf L γ δ (layer0 LG) Fl (t - r) (s - r) k := by
  unfold KQstarLeaf kernelKLeaf
  congr 1
  refine tsum_congr fun κ => ?_
  congr 2
  have hpair : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    simp only [cosetDecoration, κ.2.1.2 ℓ]
  have hroot : cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 0) =
      cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 1) := by
    simp only [cosetDecoration, κ.2.2.1 0, κ.2.2.1 1]
  rw [phaseIntegral_shift L γ δ LG hG.1 r hr _ _ (sum_sign_omega_couple LG.garden hG _ hpair hroot)]
  congr 2
  funext b
  split_ifs <;> rfl

/-- **Shifting a single-layer regular tree to layer `0`, leafwise inputs.** -/
theorem KTstarLeaf_shift (LG : LayeredGarden 1) {X : RegChain} (hX : X.DecodesTree LG.garden)
    (Fl : GLeaf LG.garden.tree → Mom d → ℝ) (r : ℕ) (hr : ∀ a, LG.layer a = r) (t s : ℝ) (k : Mom d) :
    KTstarLeaf L γ δ LG Fl t s k = KTstarLeaf L γ δ (layer0 LG) Fl (t - r) (s - r) k := by
  have hT := LGSpine.no_flowerParent_of_pairedTree LG.garden (isPairedTree_of_decodesTree hX)
  unfold KTstarLeaf kernelKLeaf
  congr 1
  refine tsum_congr fun κ => ?_
  congr 2
  have hpair : ∀ ℓ : GLeaf LG.garden.tree, cosetDecoration LG.garden L k κ.1 ℓ.toNode =
      cosetDecoration LG.garden L k κ.1 (LG.garden.pair ℓ).toNode := fun ℓ => by
    simp only [cosetDecoration, κ.2.1.2 ℓ]
  have hlone : cosetDecoration LG.garden L k κ.1 (Links.loneLeaf hX).toNode =
      cosetDecoration LG.garden L k κ.1 (GNode.root LG.garden.tree 0) := by
    simp only [cosetDecoration, Links.tree_root_eq_lone hX κ.2.1]
  exact phaseIntegral_shift' L γ δ LG hT r hr _ s _ (sum_sign_omega_tree hX _ hpair hlone)

/-- The leafwise tree kernel depends on the layering only through the branching nodes. -/
theorem KTstarLeaf_relayer (LG : LayeredGarden 1) (layer' : GNode LG.garden.tree → ℕ)
    (h' : IsLayering LG.garden layer') (hb : ∀ b : GBranch LG.garden.tree, layer' b.toNode = LG.layer b.toNode)
    (Fl : GLeaf LG.garden.tree → Mom d → ℝ) (t s : ℝ) (k : Mom d) :
    KTstarLeaf L γ δ ⟨LG.garden, layer', h'⟩ Fl t s k = KTstarLeaf L γ δ LG Fl t s k := by
  have hD : kDomain (⟨LG.garden, layer', h'⟩ : LayeredGarden 1) (fun _ => t) s =
      kDomain LG (fun _ => t) s := by
    ext τ
    simp only [kDomain, Set.mem_ofPred_eq, hb]
  unfold KTstarLeaf kernelKLeaf phaseIntegral
  rw [hD]

/-- For `s, s'` below every lone parent, `K*_𝒯[Fl](t, s) = K*_𝒯[Fl](t, s')`. -/
theorem KTstarLeaf_indep_of_le (LG : LayeredGarden 1) (hP : IsPairedTree LG.garden)
    (Fl : GLeaf LG.garden.tree → Mom d → ℝ) (t s s' : ℝ) (k : Mom d)
    (hs : ∀ b, LG.garden.IsLoneParent b → s ≤ LG.layer b.toNode ∧ s' ≤ LG.layer b.toNode) :
    KTstarLeaf L γ δ LG Fl t s k = KTstarLeaf L γ δ LG Fl t s' k := by
  have hfl := LGSpine.no_flowerParent_of_pairedTree LG.garden hP
  have hD : kDomain LG (fun _ => t) s = kDomain LG (fun _ => t) s' := by
    ext τ
    simp only [kDomain, Set.mem_ofPred_eq]
    constructor
    · intro h b
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := h b
      exact ⟨h1, h2, h3, h4, h5, fun hb => lt_of_le_of_lt (by exact_mod_cast (hs b hb).2) h1⟩
    · intro h b
      obtain ⟨h1, h2, h3, h4, h5, -⟩ := h b
      exact ⟨h1, h2, h3, h4, h5, fun hb => lt_of_le_of_lt (by exact_mod_cast (hs b hb).1) h1⟩
  have hE : ∀ τ, LG.garden.extendTime s τ = LG.garden.extendTime s' τ := fun τ => by
    funext b
    simp only [Garden.extendTime, hfl b, ↓reduceDIte]
  simp only [KTstarLeaf, kernelKLeaf, phaseIntegral, hD, hE]

end WaveTurbulence.Regref
