/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.FlFace.Domain
/-! # FL-FACE: supplement Lemma 9.1 on the `kernelKgen` time domain (exact face expansion)

This file holds the analytic steps, for a general phase product `phaseVec θ = ∏_b exp(iθ_b t_b)` (the assembly is in
`Main`). Proof: separate the selected coordinates (`splitEquiv`, measure preserving), apply Fubini, factor the integrand over
the selected nodes (`integrand_split`; the selected nodes share no constraint), integrate each selected time exactly
(`integral_slice_faces`, (9.1)), expand the product of the per-node sums over the faces (`prod_sum_faces`) and
recognize each term as the face integrand (`restFac_mul_prod_cellFac`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.FlFace
open Finset MeasureTheory Set

variable {w : ℕ}

/-! ### Separating the selected coordinates -/

section Split

variable {G : Garden w} (fix : GBranch G.tree → Option ℝ) (S : Finset (GBranch G.tree))

/-- The selected nodes as free coordinates. -/
def selEquiv (hfix : ∀ v ∈ S, fix v = none) : S ≃ {i : {b : GBranch G.tree // fix b = none} // i.1 ∈ S} where
  toFun v := ⟨⟨v.1, hfix v.1 v.2⟩, v.2⟩
  invFun i := ⟨i.1.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The free coordinates of `fixSel fix S` are the unselected free coordinates. -/
def restEquiv :
    {b : GBranch G.tree // fixSel fix S b = none} ≃ {i : {b : GBranch G.tree // fix b = none} // ¬ i.1 ∈ S} where
  toFun b := ⟨⟨b.1, (fixSel_eq_none.1 b.2).2⟩, (fixSel_eq_none.1 b.2).1⟩
  invFun i := ⟨i.1.1, fixSel_eq_none.2 ⟨i.2, i.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Free times = (selected times, remaining free times). -/
def splitEquiv (hfix : ∀ v ∈ S, fix v = none) :
    ((S → ℝ) × ({b : GBranch G.tree // fixSel fix S b = none} → ℝ)) ≃ᵐ
      ({b : GBranch G.tree // fix b = none} → ℝ) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (selEquiv fix S hfix))
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (restEquiv fix S))).trans
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {b : GBranch G.tree // fix b = none} => ℝ)
      fun i => i.1 ∈ S).symm

theorem measurePreserving_splitEquiv (hfix : ∀ v ∈ S, fix v = none) :
    MeasurePreserving (splitEquiv fix S hfix) volume volume := by
  have h1 := volume_measurePreserving_piCongrLeft (fun _ => ℝ) (selEquiv fix S hfix)
  have h2 := volume_measurePreserving_piCongrLeft (fun _ => ℝ) (restEquiv fix S)
  have h3 := MeasurePreserving.symm _ (volume_preserving_piEquivPiSubtypeProd
    (fun _ : {b : GBranch G.tree // fix b = none} => ℝ) fun i => i.1 ∈ S)
  have hp : MeasurePreserving (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (selEquiv fix S hfix))
      (MeasurableEquiv.piCongrLeft (fun _ => ℝ) (restEquiv fix S))) volume volume := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact h1.prod h2
  exact h3.comp hp

theorem splitEquiv_apply (hfix : ∀ v ∈ S, fix v = none)
    (x : (S → ℝ) × ({b : GBranch G.tree // fixSel fix S b = none} → ℝ)) (i : {b : GBranch G.tree // fix b = none}) :
    splitEquiv fix S hfix x i =
      if h : i.1 ∈ S then x.1 ⟨i.1, h⟩ else x.2 ⟨i.1, fixSel_eq_none.2 ⟨h, i.2⟩⟩ := by
  have e : splitEquiv fix S hfix x =
      (Equiv.piEquivPiSubtypeProd (fun i : {b : GBranch G.tree // fix b = none} => i.1 ∈ S) (fun _ => ℝ)).symm
        ((Equiv.piCongrLeft (fun _ => ℝ) (selEquiv fix S hfix)) x.1,
          (Equiv.piCongrLeft (fun _ => ℝ) (restEquiv fix S)) x.2) := rfl
  rw [e, Equiv.piEquivPiSubtypeProd_symm_apply]
  split_ifs with h
  · exact Equiv.piCongrLeft_apply_apply (fun _ => ℝ) (selEquiv fix S hfix) x.1 ⟨i.1, h⟩
  · exact Equiv.piCongrLeft_apply_apply (fun _ => ℝ) (restEquiv fix S) x.2 ⟨i.1, fixSel_eq_none.2 ⟨h, i.2⟩⟩

/-- The branch times of the split free times: the selected times at `S`, the `fixSel` extension elsewhere. -/
theorem extendFix_splitEquiv (hfix : ∀ v ∈ S, fix v = none)
    (x : (S → ℝ) × ({b : GBranch G.tree // fixSel fix S b = none} → ℝ)) (b : GBranch G.tree) :
    G.extendFix fix (splitEquiv fix S hfix x) b =
      if h : b ∈ S then x.1 ⟨b, h⟩ else G.extendFix (fixSel fix S) x.2 b := by
  by_cases hb : b ∈ S
  · rw [extendFix_of_none fix _ b (hfix b hb), splitEquiv_apply]
    simp only [hb, ↓reduceDIte]
  · simp only [hb, ↓reduceDIte]
    rcases hf : fix b with _ | y
    · rw [extendFix_of_none fix _ b hf, splitEquiv_apply,
        extendFix_of_none (fixSel fix S) _ b (fixSel_eq_none.2 ⟨hb, hf⟩)]
      simp only [hb, ↓reduceDIte]
    · have hs : fixSel fix S b = some y := by simp [fixSel, hb, hf]
      rw [extendFix_of_some fix _ b hf, extendFix_of_some (fixSel fix S) _ b hs]

end Split

/-! ### The phase and integrability -/

section Phase

variable {T : Fin w → TTree}

theorem continuous_phaseVec (θ : GBranch T → ℝ) : Continuous (phaseVec θ) := by
  unfold phaseVec
  refine continuous_finsetProd _ fun b _ => ?_
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul (continuous_apply b))).mul continuous_const)

theorem norm_phaseVec (θ : GBranch T → ℝ) (t : GBranch T → ℝ) : ‖phaseVec θ t‖ = 1 := by
  rw [phaseVec, norm_prod]
  exact prod_eq_one fun b _ => Complex.norm_exp_ofReal_mul_I _

/-- `phaseProdOff` is the phase product with the frequencies `offFreq`. -/
theorem phaseProdOff_eq_phaseVec (L γ δ : ℝ) {d : ℕ} (G : Garden w) (off : Finset (GBranch G.tree))
    (k : GNode G.tree → Mom d) : phaseProdOff L γ δ G off k = phaseVec (offFreq L γ δ G off k) := by
  funext t
  unfold phaseProdOff phaseVec offFreq
  refine prod_congr rfl fun b _ => ?_
  split_ifs
  · simp
  · rfl

end Phase

/-- A bounded measurable integrand, supported (through a measurable change of variables) in a unit box, is
integrable. -/
theorem integrable_indicator_comp {ι β : Type*} [Fintype ι] [MeasurableSpace β] (Tm : (ι → ℝ) → β)
    (hT : Measurable Tm) (D : Set β) (hD : MeasurableSet D) (g : β → ℂ) (hg : Measurable g)
    (hg1 : ∀ y, ‖g y‖ ≤ 1) (a : ι → ℝ) (hbox : ∀ τ, Tm τ ∈ D → ∀ i, a i < τ i ∧ τ i < a i + 1) :
    Integrable fun τ => D.indicator g (Tm τ) := by
  set B : Set (ι → ℝ) := Set.pi univ fun i => Ioo (a i) (a i + 1) with hBdef
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hBfin : volume B ≠ ⊤ := by
    rw [hBdef, Real.volume_pi_Ioo]
    exact (ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top).ne
  have hint : Integrable (B.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hB).2 (integrableOn_const hBfin)
  refine hint.mono' ((hg.indicator hD).comp hT).aestronglyMeasurable (Filter.Eventually.of_forall fun τ => ?_)
  by_cases h : Tm τ ∈ D
  · have hτ : τ ∈ B := Set.mem_univ_pi.2 fun i => hbox τ h i
    simp only [Set.indicator_of_mem h, Set.indicator_of_mem hτ]
    exact hg1 _
  · simp only [Set.indicator_of_notMem h, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) τ

/-! ### The factorization over the selected nodes -/

section Layered

variable (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
  (fix : GBranch LG.garden.tree → Option ℝ) (θ : GBranch LG.garden.tree → ℝ) (S : Finset (GBranch LG.garden.tree))

/-- The unselected factor: the unselected constraints times the unselected phases. -/
def restFac (t : GBranch LG.garden.tree → ℝ) : ℂ :=
  if t ∈ restDomain LG up fix S then ∏ b ∈ Sᶜ, Complex.exp (((θ b * t b : ℝ) : ℂ) * Complex.I) else 0

/-- The factor of a selected node `v` at time `u`: its slice condition times its phase. -/
def sliceFac (v : GBranch LG.garden.tree) (t : GBranch LG.garden.tree → ℝ) (u : ℝ) : ℂ :=
  if sliceCond LG up v t u then Complex.exp (((θ v * u : ℝ) : ℂ) * Complex.I) else 0

/-- The factor of a selected node `v` on the face with endpoint `E`: its cell times the phase at the endpoint. -/
def cellFac (v : GBranch LG.garden.tree) (E : FaceEnd LG.garden.tree) (t : GBranch LG.garden.tree → ℝ) : ℂ :=
  if faceCell LG up v E t then Complex.exp (((θ v * endVal LG up v t E : ℝ) : ℂ) * Complex.I) else 0

/-- The phase product splits into the selected phases and the unselected ones. -/
theorem phaseVec_split (t : GBranch LG.garden.tree → ℝ) :
    phaseVec θ t = (∏ v ∈ S, Complex.exp (((θ v * t v : ℝ) : ℂ) * Complex.I)) *
      ∏ b ∈ Sᶜ, Complex.exp (((θ b * t b : ℝ) : ℂ) * Complex.I) :=
  (prod_mul_prod_compl S _).symm

/-- **The integrand factorizes over the selected nodes.** -/
theorem integrand_split (hS : SelOnePerTree S) (hfix : ∀ v ∈ S, fix v = none)
    (x : (S → ℝ) × ({b : GBranch LG.garden.tree // fixSel fix S b = none} → ℝ)) :
    (kDomainFix LG up fix).indicator (phaseVec θ) (LG.garden.extendFix fix (splitEquiv fix S hfix x)) =
      restFac LG up fix θ S (LG.garden.extendFix (fixSel fix S) x.2) *
        ∏ i : S, sliceFac LG up θ i.1 (LG.garden.extendFix (fixSel fix S) x.2) (x.1 i) := by
  set t₀ := LG.garden.extendFix (fixSel fix S) x.2 with ht₀
  set t := LG.garden.extendFix fix (splitEquiv fix S hfix x) with ht
  have hT : ∀ b, t b = if h : b ∈ S then x.1 ⟨b, h⟩ else t₀ b := extendFix_splitEquiv fix S hfix x
  have hag : ∀ b ∉ S, t b = t₀ b := fun b hb => by rw [hT b]; simp only [hb, ↓reduceDIte]
  have hsel : ∀ i : S, t i.1 = x.1 i := fun i => by rw [hT i.1]; simp only [i.2, ↓reduceDIte]
  have hdom : t ∈ kDomainFix LG up fix ↔
      t₀ ∈ restDomain LG up fix S ∧ ∀ i : S, sliceCond LG up i.1 t₀ (x.1 i) := by
    rw [mem_kDomainFix_iff LG up fix S hfix, restDomain_congr LG up fix S hag]
    refine and_congr Iff.rfl ⟨fun H i => ?_, fun H v hv => ?_⟩
    · have := H i.1 i.2
      rwa [hsel i, sliceCond_congr LG up hS i.2 hag] at this
    · have := H ⟨v, hv⟩
      rwa [← hsel ⟨v, hv⟩, ← sliceCond_congr LG up hS hv hag] at this
  rw [Set.indicator_apply]
  by_cases hA : t₀ ∈ restDomain LG up fix S ∧ ∀ i : S, sliceCond LG up i.1 t₀ (x.1 i)
  · rw [ite_eq_left (hdom.2 hA), phaseVec_split LG θ S t, restFac, ite_eq_left hA.1]
    have h1 : (∏ v ∈ S, Complex.exp (((θ v * t v : ℝ) : ℂ) * Complex.I)) =
        ∏ i : S, sliceFac LG up θ i.1 t₀ (x.1 i) := by
      rw [← prod_coe_sort S]
      refine prod_congr rfl fun i _ => ?_
      rw [sliceFac, ite_eq_left (hA.2 i), hsel i]
    have h2 : (∏ b ∈ Sᶜ, Complex.exp (((θ b * t b : ℝ) : ℂ) * Complex.I)) =
        ∏ b ∈ Sᶜ, Complex.exp (((θ b * t₀ b : ℝ) : ℂ) * Complex.I) :=
      prod_congr rfl fun b hb => by rw [hag b (mem_compl.1 hb)]
    rw [h1, h2, mul_comm]
  · rw [ite_eq_right (fun h => hA (hdom.1 h))]
    rcases not_and_or.1 hA with h | h
    · rw [restFac, ite_eq_right h, zero_mul]
    · obtain ⟨i, hi⟩ := not_forall.1 h
      rw [prod_eq_zero (mem_univ i) (by rw [sliceFac, ite_eq_right hi]), mul_zero]

end Layered

end WaveTurbulence.Flower.FlFace
