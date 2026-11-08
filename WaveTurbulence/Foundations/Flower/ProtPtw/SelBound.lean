/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.SelKernel

/-! # D6a PROT-PTW: the designated paired-tree kernel with one selected time, pointwise

`kernelProt` with a free branch `v = (j, ev)` whose link weight vanishes where `⟨x, y⟩ = 0`: the `t_v` integral is
done exactly, the selected link `j` becomes exceptional with the reciprocal weight `selWeight`, and the remaining
times give the core bound (factor `2`: two endpoints). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links

variable {d : ℕ} {LG : LayeredGarden 1} {X : RegChain}

theorem supG_update (hX : X.DecodesTree LG.garden) (L γ δ : ℝ)
    (E : Finset (Fin (X.treeLinks (LG.garden.sig 0)).length)) (cE : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) {j : Fin (X.treeLinks (LG.garden.sig 0)).length}
    (hj : j ∈ E) (ev : Fin 2) (g : GBranch LG.garden.tree → ℝ) (x : ℝ) (i : Fin (X.treeLinks (LG.garden.sig 0)).length)
    (A : LayerLink d) :
    supG L γ δ E cE ψ i ((treeClockEquiv hX).symm (Function.update g (treeLinkBranch hX j ev) x) i) A =
      supG L γ δ E cE ψ i ((treeClockEquiv hX).symm g i) A := by
  unfold supG
  by_cases hi : i ∈ E
  · simp only [hi, ite_true]
  · simp only [hi, ite_false]
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    congr 3
    funext e
    rw [treeClockEquiv_symm_apply, treeClockEquiv_symm_apply,
      Function.update_of_ne (fun h => hij ((treeLinkBranch_eq_iff hX i j e ev).1 h).1)]

theorem extendFix_join (fix : GBranch LG.garden.tree → Option ℝ) (v : {b : GBranch LG.garden.tree // fix b = none})
    (τ' : {i // i ≠ v} → ℝ) (x : ℝ) :
    LG.garden.extendFix fix (join v τ' x) = Function.update (LG.garden.extendFix fix (join v τ' 0)) v.1 x := by
  funext b
  by_cases hb : b = v.1
  · subst hb
    rw [Function.update_self, extendFix_free _ fix _ v, join_apply_self]
  · rw [Function.update_of_ne hb]
    by_cases hf : fix b = none
    · have hne : (⟨b, hf⟩ : {b : GBranch LG.garden.tree // fix b = none}) ≠ v := fun h => hb (congrArg Subtype.val h)
      rw [extendFix_free _ fix _ ⟨b, hf⟩, extendFix_free _ fix _ ⟨b, hf⟩, join_apply_ne v τ' x hne,
        join_apply_ne v τ' 0 hne]
    · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hf
      rw [extendFix_some _ fix _ hw, extendFix_some _ fix _ hw]

theorem freeBox_join (fix : GBranch LG.garden.tree → Option ℝ) (v : {b : GBranch LG.garden.tree // fix b = none})
    (τ' : {i // i ≠ v} → ℝ) (x : ℝ) :
    (unitBox fun b : {b // fix b = none} => (LG.layer b.1.toNode : ℝ)).indicator 1 (join v τ' x) =
      (unitBox fun b : {i // i ≠ v} => (LG.layer b.1.1.toNode : ℝ)).indicator
          (1 : ({i // i ≠ v} → ℝ) → ℝ≥0∞) τ' *
        (Icc (LG.layer v.1.toNode : ℝ) (LG.layer v.1.toNode + 1)).indicator 1 x := by
  have hiff : join v τ' x ∈ (unitBox fun b : {b // fix b = none} => (LG.layer b.1.toNode : ℝ)) ↔
      τ' ∈ (unitBox fun b : {i // i ≠ v} => (LG.layer b.1.1.toNode : ℝ)) ∧
        x ∈ Icc (LG.layer v.1.toNode : ℝ) (LG.layer v.1.toNode + 1) := by
    simp only [unitBox, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      refine ⟨fun i => ?_, ?_⟩
      · have := h i.1; rwa [join_apply_ne v τ' x i.2] at this
      · have := h v; rwa [join_apply_self] at this
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = v
      · subst hi; rw [join_apply_self]; exact h2
      · rw [join_apply_ne v τ' x hi]; exact h1 ⟨i, hi⟩
  by_cases h1 : τ' ∈ (unitBox fun b : {i // i ≠ v} => (LG.layer b.1.1.toNode : ℝ)) <;>
    by_cases h2 : x ∈ Icc (LG.layer v.1.toNode : ℝ) (LG.layer v.1.toNode + 1) <;>
    simp [Set.indicator, h1, h2, hiff]

/-- **Re-merging the selected time** as a dummy unit interval, for a function not reading it. -/
theorem lintegral_merge (fix : GBranch LG.garden.tree → Option ℝ) (v : {b : GBranch LG.garden.tree // fix b = none})
    (f : (GBranch LG.garden.tree → ℝ) → ℝ≥0∞) (hf : Measurable f)
    (hfv : ∀ g x, f (Function.update g v.1 x) = f g) :
    ∫⁻ τ' : {i // i ≠ v} → ℝ, (unitBox fun b : {i // i ≠ v} => (LG.layer b.1.1.toNode : ℝ)).indicator 1 τ' *
        f (LG.garden.extendFix fix (join v τ' 0)) =
      ∫⁻ τ : {b // fix b = none} → ℝ, (unitBox fun b : {b // fix b = none} => (LG.layer b.1.toNode : ℝ)).indicator 1 τ *
        f (LG.garden.extendFix fix τ) := by
  have hm : Measurable (fun τ : {b // fix b = none} → ℝ =>
      (unitBox fun b : {b // fix b = none} => (LG.layer b.1.toNode : ℝ)).indicator 1 τ * f (LG.garden.extendFix fix τ)) :=
    (measurable_one.indicator (measurableSet_unitBox _)).mul (hf.comp (measurable_extendFix _ _))
  rw [lintegral_split v _ hm]
  apply lintegral_congr
  intro τ'
  have h1 : ∀ x, (unitBox fun b : {b // fix b = none} => (LG.layer b.1.toNode : ℝ)).indicator 1 (join v τ' x) *
      f (LG.garden.extendFix fix (join v τ' x)) =
      (Icc (LG.layer v.1.toNode : ℝ) (LG.layer v.1.toNode + 1)).indicator 1 x *
        ((unitBox fun b : {i // i ≠ v} => (LG.layer b.1.1.toNode : ℝ)).indicator 1 τ' *
          f (LG.garden.extendFix fix (join v τ' 0))) := by
    intro x
    rw [freeBox_join, extendFix_join fix v τ' x, hfv]
    ring
  rw [show (fun x => (unitBox fun b : {b // fix b = none} => (LG.layer b.1.toNode : ℝ)).indicator 1 (join v τ' x) *
      f (LG.garden.extendFix fix (join v τ' x))) = _ from funext h1]
  rw [lintegral_mul_const _ (measurable_one.indicator measurableSet_Icc), lintegral_indicator_one measurableSet_Icc,
    Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_one, one_mul]

/-- **The pointwise bound of the designated paired-tree kernel with one selected time.** -/
theorem enorm_kernelProt_tree_sel_le (hX : X.DecodesTree LG.garden) {α : Type*} [MeasurableSpace α]
    {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ) (H : LeafProfiles 1 d) (mult : (GNode LG.garden.tree → Mom d) → ℂ)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k : Mom d)
    (F : SpatialMeasure (PairedMomentum d (X.treeLinks (LG.garden.sig 0)).length) α)
    (ψ : Fin (X.treeLinks (LG.garden.sig 0)).length → LPair d → ℂ) {Bψ : ℝ} (hBψ : 0 ≤ Bψ)
    (hψ : ∀ i q, ‖ψ i q‖ ≤ Bψ)
    (hW : ∀ p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ,
      mult (cosetDecoration LG.garden L k (treeDecOfParams hX (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
        F.value (pairedLattice L p) * arrayWeight ψ p)
    (hs : Summable (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 → Fin d → ℤ =>
      ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k (fun i j => latticePoint L (p (i, j)))‖))
    {K M : ℕ} {B : ℝ} (hK : d + 1 ≤ K) (hM : 2 * d ≤ M) (hB : 0 ≤ B)
    (hf : ∀ a, Fourier.spatialNorm K M (treeInputFunctionsL LG H a) ≤ ENNReal.ofReal B)
    (S : (Fin (Fintype.card (Links.TPlus LG.garden)) → Fin d → ℤ) →
      Finset ((Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ))
    (hcover : ∀ c x, (treeCarrier hX).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2 => x p.1 p.2) ≠ 0 →
        z ∈ S c)
    {C : ℝ} (hS : ∀ c, ((S c).card : ℝ) ≤ C ^ (X.treeLinks (LG.garden.sig 0)).length)
    (j : Fin (X.treeLinks (LG.garden.sig 0)).length) (ev : Fin 2) (hv : fix (treeLinkBranch hX j ev) = none)
    (hann : ∀ q, selFreq (X := X) (LG := LG) L γ δ (treeLayerLinks LG hX) j ev q = 0 → ψ j q = 0)
    {Bψ' : ℝ} (hBψ' : 0 ≤ Bψ') (hψ' : ∀ i q, ‖selWeight L γ δ (treeLayerLinks LG hX) j ev ψ i q‖ ≤ Bψ')
    (E : Finset (Fin (X.treeLinks (LG.garden.sig 0)).length)) (hj : j ∈ E)
    (cE : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ)
    (hcE : ∀ i ∈ E, 0 ≤ cE i ∧ ∀ q, ‖selWeight L γ δ (treeLayerLinks LG hX) j ev ψ i q‖ ≤ cE i)
    (Mi : Fin (X.treeLinks (LG.garden.sig 0)).length → ℝ≥0∞)
    (hMi : ∀ i ∉ E, ∀ A : LayerLink d, A.leftLayer = (treeLayerLinks (d := d) LG hX i).leftLayer →
      A.rightLayer = (treeLayerLinks (d := d) LG hX i).rightLayer →
      ∫⁻ s in linkBox A, ‖genLinkTimeFactor L γ δ A (selWeight L γ δ (treeLayerLinks LG hX) j ev ψ i) s‖ₑ ≤ Mi i)
    (hfree : ∀ i ∉ E, ∀ e, fix (treeLinkBranch hX i e) = none) :
    ‖kernelProt L γ δ LG H mult up s fix k (fun _ => 0) 0‖ₑ ≤
      ENNReal.ofReal (coupling d L γ δ ^ (2 * (X.treeLinks (LG.garden.sig 0)).length)) *
        (2 * (ENNReal.ofReal F.mass * cellMass d (X.treeLinks (LG.garden.sig 0)).length
          (Fintype.card (Links.TPlus LG.garden)) M C B *
          ∏ i, (if i ∈ E then ENNReal.ofReal (cE i * (5 * L) ^ (2 * d)) else Mi i))) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  rw [kernelProt_tree_eq_integral hX hLp γ δ H mult up s fix k F ψ hBψ hψ hW hs, enorm_mul]
  have hc : ‖(coupling d L γ δ : ℂ) ^ (2 * (X.treeLinks (LG.garden.sig 0)).length)‖ₑ =
      ENNReal.ofReal (coupling d L γ δ ^ (2 * (X.treeLinks (LG.garden.sig 0)).length)) := by
    rw [← Complex.ofReal_pow, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact (even_two_mul _).pow_nonneg _
  rw [hc]
  apply mul_le_mul' le_rfl
  set Q := treeLayerLinks (d := d) LG hX
  set ψ' := selWeight L γ δ Q j ev ψ
  let v' : {b : GBranch LG.garden.tree // fix b = none} := ⟨treeLinkBranch hX j ev, hv⟩
  obtain ⟨hcont, hbd⟩ := continuous_treeIntegrand_bound hX L γ δ H k F ψ hBψ hψ hs
  set Bt := F.mass * Bψ ^ (X.treeLinks (LG.garden.sig 0)).length * ∑' p : Fin (X.treeLinks (LG.garden.sig 0)).length ×
    Fin 2 → Fin d → ℤ, ‖(treeCarrier hX).sourceLeafWeight (treeInputFunctionsL LG H) k
      (fun i j => latticePoint L (p (i, j)))‖
  have hBm : MeasurableSet (freeBox LG fix) := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hint1 : Integrable ((freeBox LG fix).indicator (1 : ({b : GBranch LG.garden.tree //
      fix b = none} → ℝ) → ℝ)) := by
    rw [integrable_indicator_iff hBm]
    exact integrableOn_const (by rw [volume_freeBox]; exact ENNReal.one_ne_top)
  have hI : Integrable (fun τ : {b // fix b = none} → ℝ =>
      (protDom LG up s fix).indicator (treeIntegrand hX L γ δ H k F ψ) (LG.garden.extendFix fix τ)) := by
    refine (hint1.const_mul Bt).mono'
      ((hcont.measurable.indicator (measurableSet_protDom LG up s fix)).comp (measurable_extendFix _ _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun τ => ?_)
    by_cases hτ : LG.garden.extendFix fix τ ∈ protDom LG up s fix
    · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem (protDom_subset_freeBox LG up s fix τ hτ), Pi.one_apply,
        mul_one]
      exact hbd _
    · rw [Set.indicator_of_notMem hτ, norm_zero]
      exact mul_nonneg (mul_nonneg (mul_nonneg F.mass_nonneg (pow_nonneg hBψ _)) (tsum_nonneg fun _ => norm_nonneg _))
        (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  rw [integral_split v' _ hI]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  let tf := fun τ' : {i // i ≠ v'} → ℝ => (treeClockEquiv hX).symm (LG.garden.extendFix fix (join v' τ' 0))
  let Env := fun t => arrayEnvelope (treeCarrier hX) F (gardenCircle LG.garden) L γ δ Q ψ'
    (treeInputFunctionsL LG H) S k (supG L γ δ E cE ψ') t
  have hEnv (g : GBranch LG.garden.tree → ℝ) (x : ℝ) :
      Env ((treeClockEquiv hX).symm (Function.update g (treeLinkBranch hX j ev) x)) =
        Env ((treeClockEquiv hX).symm g) := by
    simp only [Env, arrayEnvelope, supG_update hX L γ δ E cE ψ' hj ev g x]
  set box' := (unitBox fun b : {i // i ≠ v'} => (LG.layer b.1.1.toNode : ℝ))
  have hpt (τ' : {i // i ≠ v'} → ℝ) :
      ‖∫ x, (protDom LG up s fix).indicator (treeIntegrand hX L γ δ H k F ψ)
        (LG.garden.extendFix fix (join v' τ' x))‖ₑ ≤ box'.indicator 1 τ' * (2 * Env (tf τ')) := by
    rw [show (fun x => (protDom LG up s fix).indicator (treeIntegrand hX L γ δ H k F ψ)
        (LG.garden.extendFix fix (join v' τ' x))) = fun x => (protDom LG up s fix).indicator
          (treeIntegrand hX L γ δ H k F ψ)
            (Function.update (LG.garden.extendFix fix (join v' τ' 0)) (treeLinkBranch hX j ev) x) from
        funext fun x => by rw [extendFix_join fix v' τ' x]]
    by_cases hτ' : τ' ∈ box'
    · rw [Set.indicator_of_mem hτ', Pi.one_apply, one_mul]
      refine enorm_integral_section_le hX hLp γ δ H k F ψ hBψ hψ j ev hann hBψ' hψ' hs up s fix hv _ fun x => ?_
      refine (enorm_arrayIntegrand_le (treeCarrier hX) F _ hL γ δ Q ψ' hBψ' hψ' _ hK hM hB hf S k hcover hS
        (supG L γ δ E cE ψ') (supG_ge hL γ δ E cE ψ' hcE) _).trans ?_
      exact (hEnv _ x).le
    · rw [Set.indicator_of_notMem hτ', zero_mul]
      have h0 (x : ℝ) : (protDom LG up s fix).indicator (treeIntegrand hX L γ δ H k F ψ)
          (Function.update (LG.garden.extendFix fix (join v' τ' 0)) (treeLinkBranch hX j ev) x) = 0 := by
        apply Set.indicator_of_notMem
        intro hmem
        apply hτ'
        rw [← extendFix_join fix v' τ' x] at hmem
        have hb := protDom_subset_freeBox LG up s fix (join v' τ' x) hmem
        intro i _
        have := hb i.1 (mem_univ _)
        rwa [join_apply_ne v' τ' x i.2] at this
      simp only [h0, integral_zero, enorm_zero, le_refl]
  refine (lintegral_mono hpt).trans ?_
  have hbox' : MeasurableSet box' := measurableSet_unitBox _
  have htf (i : Fin (X.treeLinks (LG.garden.sig 0)).length) : Measurable (fun τ' => tf τ' i) :=
    (measurable_pi_apply i).comp ((treeClockEquiv hX).symm.measurable.comp ((measurable_extendFix _ _).comp
      ((joinEquiv v').measurable.comp (measurable_id.prodMk measurable_const))))
  have hrestr : (∫⁻ τ', box'.indicator 1 τ' * (2 * Env (tf τ'))) = 2 * ∫⁻ τ' in box', Env (tf τ') := by
    rw [← lintegral_const_mul' _ _ (by simp), ← lintegral_indicator hbox']
    apply lintegral_congr
    intro τ'
    by_cases hτ' : τ' ∈ box' <;> simp [Set.indicator, hτ']
  rw [hrestr]
  apply mul_le_mul' le_rfl
  have hGm (z : (Fin (X.treeLinks (LG.garden.sig 0)).length × Fin 2) → Fin d → ℤ) :
      Measurable (fun w : ({i // i ≠ v'} → ℝ) × α × (LocalizedCellIndex (X.treeLinks (LG.garden.sig 0)).length
          (Fintype.card (Links.TPlus LG.garden)) → Fin d → ℝ) =>
        ∏ i, supG L γ δ E cE ψ' i (tf w.1 i) (cellLinks (treeCarrier hX) F Q z w.2.1 w.2.2 i)) := by
    refine Finset.measurable_prod _ fun i _ => ?_
    unfold supG
    by_cases hi : i ∈ E
    · simp only [hi, ite_true]; exact measurable_const
    · simp only [hi, ite_false]
      exact ((measurable_genLinkTimeFactor_cellLinks (treeCarrier hX) F Q hLp γ δ (ψ' i) z i).comp
        (((htf i).comp measurable_fst).prodMk measurable_snd)).enorm
  refine lintegral_arrayEnvelope_le _ (treeCarrier hX) F (gardenCircle LG.garden) L γ δ Q ψ' _ hK hM hB hf S hS k
    (supG L γ δ E cE ψ') tf hGm ?_
  intro z a ξ
  let f := fun g : GBranch LG.garden.tree → ℝ =>
    ∏ i, supG L γ δ E cE ψ' i ((treeClockEquiv hX).symm g i) (cellLinks (treeCarrier hX) F Q z a ξ i)
  have hfm : Measurable f := by
    refine Finset.measurable_prod _ fun i _ => ?_
    unfold supG
    by_cases hi : i ∈ E
    · simp only [hi, ite_true]; exact measurable_const
    · simp only [hi, ite_false]
      exact ((continuous_genLinkTimeFactor hLp γ δ _ (ψ' i)).measurable.comp
        ((measurable_pi_apply i).comp (treeClockEquiv hX).symm.measurable)).enorm
  have hfv (g : GBranch LG.garden.tree → ℝ) (x : ℝ) : f (Function.update g v'.1 x) = f g :=
    Finset.prod_congr rfl fun i _ => supG_update hX L γ δ E cE ψ' hj ev g x i _
  rw [← lintegral_indicator hbox']
  rw [show box'.indicator (fun τ' => ∏ i, supG L γ δ E cE ψ' i (tf τ' i) (cellLinks (treeCarrier hX) F Q z a ξ i)) =
      fun τ' => box'.indicator 1 τ' * f (LG.garden.extendFix fix (join v' τ' 0)) from
    funext fun τ' => by by_cases hτ' : τ' ∈ box' <;> simp [Set.indicator, hτ', f, tf]]
  rw [lintegral_merge fix v' f hfm hfv]
  simp_rw [extendFix_eq_fill]
  exact lintegral_links_le hX hLp γ δ ψ' E cE Mi hMi (fun b => fix b = none) (fun b => (fix b).getD 0) hfree _
    (fun _ => rfl) (fun _ => rfl)

end WaveTurbulence.Flower.ProtPtw
