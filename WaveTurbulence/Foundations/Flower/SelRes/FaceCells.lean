/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Cells

/-! # D7 SEL-RES / FaceCells: the cell integrands of the face expansion

Integrability and measurability of the cell integrands (`Tcell` upper, `Scell` lower), the inner one-dimensional
integral over the selected time (`integral_inner`), almost-sure genericity of the rest times (`ae_generic`), and the
pointwise identification of each cell with a pinned time-domain integrand (`Tcell_none_eq`, `Scell_none_eq`,
`Tcell_some_eq`, `Scell_some_eq`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne measurable_extendFix' measurable_lt_pred measurable_le_pred
  measurable_finset_forall)

variable {w : ℕ} {G : Garden w}

/-! ### Integrability and measurability -/

/-- A bounded measurable integrand supported in a closed unit box is integrable. -/
theorem integrable_of_closed_box {ι β : Type*} [Fintype ι] [MeasurableSpace β] (Tm : (ι → ℝ) → β)
    (hT : Measurable Tm) (D : Set β) (hD : MeasurableSet D) (g : β → ℂ) (hg : Measurable g)
    (hg1 : ∀ y, ‖g y‖ ≤ 1) (a : ι → ℝ) (hbox : ∀ τ, Tm τ ∈ D → ∀ i, a i ≤ τ i ∧ τ i ≤ a i + 1) :
    Integrable fun τ => D.indicator g (Tm τ) := by
  set B : Set (ι → ℝ) := Set.pi univ fun i => Icc (a i) (a i + 1) with hBdef
  have hB : MeasurableSet B := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hBfin : volume B ≠ ⊤ := by
    rw [hBdef, volume_pi_pi]
    exact (ENNReal.prod_lt_top fun _ _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top).ne
  have hint : Integrable (B.indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff hB).2 (integrableOn_const hBfin)
  refine hint.mono' ((hg.indicator hD).comp hT).aestronglyMeasurable (Filter.Eventually.of_forall fun τ => ?_)
  by_cases h : Tm τ ∈ D
  · have hτ : τ ∈ B := Set.mem_univ_pi.2 fun i => hbox τ h i
    simp only [Set.indicator_of_mem h, Set.indicator_of_mem hτ]
    exact hg1 _
  · simp only [Set.indicator_of_notMem h, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) τ

variable (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)

theorem measurableSet_restOK (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) :
    MeasurableSet {X : GBranch G.tree → ℝ | restOK layer rootTime fix v X} := by
  unfold restOK
  refine Measurable.setOf (Measurable.and ?_ ?_)
  · refine Measurable.forall fun x => Measurable.imp measurable_const (Measurable.imp measurable_const
      (Measurable.and (Measurable.and ?_ ?_) ?_))
    · exact measurable_le_pred measurable_const (measurable_pi_apply x)
    · exact measurable_le_pred (measurable_pi_apply x) measurable_const
    · exact measurable_lt_pred (measurable_pi_apply x) measurable_const
  · exact Measurable.forall fun x => Measurable.forall fun u => Measurable.imp measurable_const
      (Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const
        (measurable_lt_pred (measurable_pi_apply x) (measurable_pi_apply u)))))

variable {layer rootTime}

theorem measurable_upV (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (o : Option (GBranch G.tree)) :
    Measurable fun X : GBranch G.tree → ℝ => upV layer rootTime fix v X o := by
  cases o with
  | none => exact measurable_const
  | some x => exact measurable_pi_apply x

theorem measurable_loV (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (o : Option (GBranch G.tree)) :
    Measurable fun X : GBranch G.tree → ℝ => loV layer fix v X o := by
  cases o with
  | none => exact measurable_const
  | some x => exact measurable_pi_apply x

/-- The upper cell of the index `i` and the lower cell of the index `j`. -/
def upCell (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (i : Option (GBranch G.tree))
    (X : GBranch G.tree → ℝ) : Prop :=
  (∀ j ∈ loI fix v, loV layer fix v X j < upV layer rootTime fix v X i) ∧
    ∀ j ∈ upI fix v, j ≠ i → upV layer rootTime fix v X i < upV layer rootTime fix v X j

def loCell (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (j : Option (GBranch G.tree))
    (X : GBranch G.tree → ℝ) : Prop :=
  (∀ i ∈ upI fix v, loV layer fix v X j < upV layer rootTime fix v X i) ∧
    ∀ j' ∈ loI fix v, j' ≠ j → loV layer fix v X j' < loV layer fix v X j

theorem measurableSet_upCell (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (i : Option (GBranch G.tree)) :
    MeasurableSet {X | restOK layer rootTime fix v X ∧ upCell (layer := layer) (rootTime := rootTime) fix v i X} := by
  refine (measurableSet_restOK layer rootTime fix v).inter (Measurable.setOf (Measurable.and ?_ ?_))
  · exact measurable_finset_forall _ fun j _ => measurable_lt_pred (measurable_loV fix v j) (measurable_upV fix v i)
  · exact measurable_finset_forall _ fun j _ => Measurable.imp measurable_const
      (measurable_lt_pred (measurable_upV fix v i) (measurable_upV fix v j))

theorem measurableSet_loCell (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (j : Option (GBranch G.tree)) :
    MeasurableSet {X | restOK layer rootTime fix v X ∧ loCell (layer := layer) (rootTime := rootTime) fix v j X} := by
  refine (measurableSet_restOK layer rootTime fix v).inter (Measurable.setOf (Measurable.and ?_ ?_))
  · exact measurable_finset_forall _ fun i _ => measurable_lt_pred (measurable_loV fix v j) (measurable_upV fix v i)
  · exact measurable_finset_forall _ fun j' _ => Measurable.imp measurable_const
      (measurable_lt_pred (measurable_loV fix v j') (measurable_loV fix v j))

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne measurable_extendFix')

variable {w : ℕ} {G : Garden w} {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ}

theorem integrable_dom (fix : GBranch G.tree → Option ℝ) (α : GBranch G.tree → ℝ) :
    Integrable fun τ : {x : GBranch G.tree // fix x = none} → ℝ =>
      (splicedTimeDomainFix G layer rootTime fix).indicator (phaseF α) (G.extendFix fix τ) :=
  integrable_of_closed_box (G.extendFix fix) (measurable_extendFix' fix) _
    (WaveTurbulence.FlowerP5.measurableSet_splicedTimeDomainFix G layer rootTime fix) _ (continuous_phaseF α).measurable
    (fun t => (norm_phaseF α t).le) (fun i => (layer i.1 : ℝ))
    (fun τ hτ i => by
      have h := (hτ.1 i.1 i.2).1
      rw [extendFix_of_none fix τ i.1 i.2] at h
      exact ⟨h.1, h.2⟩)

/-- The pinned values of the rest extension. -/
theorem extendFix_fixSel_pinned (fix : GBranch G.tree → Option ℝ) (S : Finset (GBranch G.tree))
    (hS : ∀ v ∈ S, fix v = none) (ρ : {x : GBranch G.tree // fixSel fix S x = none} → ℝ) :
    ∀ x s, fix x = some s → G.extendFix (fixSel fix S) ρ x = s := by
  intro x s hs
  have hx : x ∉ S := fun h => by rw [hS x h] at hs; exact absurd hs (by simp)
  have : fixSel fix S x = some s := by simp [fixSel, hx, hs]
  exact extendFix_of_some _ ρ x this

/-- The exponential at the selected frequency. -/
def expAt (θ : ℝ) (s : ℝ) : ℂ := Complex.exp ((θ * s : ℝ) * Complex.I)

/-- **The inner integral over the selected time.** -/
theorem integral_inner (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (hv : fix v = none)
    (α : GBranch G.tree → ℝ) (hα : Real.pi * α v ≠ 0) (X : GBranch G.tree → ℝ)
    (hX : ∀ x s, fix x = some s → X x = s) :
    (∫ r, (splicedTimeDomainFix G layer rootTime fix).indicator (phaseF α) (Function.update X v r)) =
      (if restOK layer rootTime fix v X then phaseF α (Function.update X v 0) else 0) *
        ((((Real.pi * α v : ℝ) : ℂ) * Complex.I)⁻¹ *
          (if loX layer fix v X < hiX layer rootTime fix v X then
            expAt (Real.pi * α v) (hiX layer rootTime fix v X) - expAt (Real.pi * α v) (loX layer fix v X)
          else 0)) := by
  have hpt : ∀ r, (splicedTimeDomainFix G layer rootTime fix).indicator (phaseF α) (Function.update X v r) =
      (if restOK layer rootTime fix v X then phaseF α (Function.update X v 0) else 0) *
        (slotA layer rootTime v X).indicator (fun r => Complex.exp ((Real.pi * α v * r : ℝ) * Complex.I)) r := by
    intro r
    by_cases hR : restOK layer rootTime fix v X
    · by_cases hA : r ∈ slotA layer rootTime v X
      · rw [indicator_of_mem ((mem_dom_update layer rootTime fix v hv X r).2 ⟨hR, hA⟩), ite_eq_left hR,
          indicator_of_mem hA, phaseF_update]
      · rw [indicator_of_notMem (fun h => hA ((mem_dom_update layer rootTime fix v hv X r).1 h).2),
          indicator_of_notMem hA, mul_zero]
    · rw [indicator_of_notMem (fun h => hR ((mem_dom_update layer rootTime fix v hv X r).1 h).1), ite_eq_right hR,
        zero_mul]
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  obtain ⟨h1, h2⟩ := slotA_squeeze (layer := layer) (rootTime := rootTime) X hX
  have := integral_slot (Real.pi * α v) hα (slotA layer rootTime v X) _ _ h1 h2
  simp only [mul_assoc] at this ⊢
  rw [this]
  split_ifs
  · unfold expAt; rw [div_eq_inv_mul]; simp only [mul_assoc]
  · simp

/-! ### Generic rest times -/

theorem extendFix_free (fix : GBranch G.tree → Option ℝ) (ρ : {x : GBranch G.tree // fix x = none} → ℝ)
    {x : GBranch G.tree} (hx : fix x = none) : G.extendFix fix ρ x = ρ ⟨x, hx⟩ := extendFix_of_none fix ρ x hx

theorem fixSel_none_of {fix : GBranch G.tree → Option ℝ} {v x : GBranch G.tree} (hxv : x ≠ v) (hx : fix x = none) :
    fixSel fix {v} x = none := by simp [fixSel, hxv, hx]

/-- Almost every rest time vector has distinct free endpoint times, distinct from the constant endpoints. -/
theorem ae_generic (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) :
    ∀ᵐ ρ : ({x : GBranch G.tree // fixSel fix {v} x = none} → ℝ),
      Set.InjOn (upV layer rootTime fix v (G.extendFix (fixSel fix {v}) ρ)) (upI fix v) ∧
      Set.InjOn (loV layer fix v (G.extendFix (fixSel fix {v}) ρ)) (loI fix v) := by
  set ι := {x : GBranch G.tree // fixSel fix {v} x = none}
  -- the bad sets
  let N1 : GBranch G.tree → ℝ → Set (ι → ℝ) := fun x c => {ρ | G.extendFix (fixSel fix {v}) ρ x = c}
  let N2 : GBranch G.tree → GBranch G.tree → Set (ι → ℝ) := fun x y =>
    {ρ | G.extendFix (fixSel fix {v}) ρ x = G.extendFix (fixSel fix {v}) ρ y}
  have hN1 : ∀ x, x ≠ v → fix x = none → ∀ c, volume (N1 x c) = 0 := by
    intro x hxv hx c
    have hs : N1 x c = {ρ : ι → ℝ | ρ ⟨x, fixSel_none_of hxv hx⟩ = c} := by
      ext ρ; simp only [N1, mem_ofPred_eq, extendFix_free _ ρ (fixSel_none_of hxv hx)]
    rw [hs]; exact volume_eval_eq_null _ c
  have hN2 : ∀ x y, x ≠ v → fix x = none → y ≠ v → fix y = none → x ≠ y → volume (N2 x y) = 0 := by
    intro x y hxv hx hyv hy hxy
    have hs : N2 x y = {ρ : ι → ℝ | ρ ⟨x, fixSel_none_of hxv hx⟩ = ρ ⟨y, fixSel_none_of hyv hy⟩} := by
      ext ρ
      simp only [N2, mem_ofPred_eq, extendFix_free _ ρ (fixSel_none_of hxv hx),
        extendFix_free _ ρ (fixSel_none_of hyv hy)]
    rw [hs]
    exact volume_eval_eq_eval_null fun h => hxy (congrArg Subtype.val h)
  set Bad : Set (ι → ℝ) :=
    (⋃ x ∈ Uf fix v, N1 x (ctop layer rootTime fix v)) ∪ (⋃ x ∈ Uf fix v, ⋃ y ∈ (Uf fix v).erase x, N2 x y) ∪
    (⋃ x ∈ Cf fix v, N1 x (cfl layer fix v)) ∪ (⋃ x ∈ Cf fix v, ⋃ y ∈ (Cf fix v).erase x, N2 x y) with hBad
  have hUv : ∀ x ∈ Uf fix v, x ≠ v ∧ fix x = none := fun x hx =>
    ⟨(IsChildOf.ne (mem_Uf.1 hx).1).symm, (mem_Uf.1 hx).2⟩
  have hCv : ∀ x ∈ Cf fix v, x ≠ v ∧ fix x = none := fun x hx => ⟨IsChildOf.ne (mem_Cf.1 hx).1, (mem_Cf.1 hx).2⟩
  have hnull : volume Bad = 0 := by
    refine measure_union_null (measure_union_null (measure_union_null ?_ ?_) ?_) ?_
    · exact (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun x hx =>
        hN1 x (hUv x hx).1 (hUv x hx).2 _
    · refine (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun x hx =>
        (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun y hy => ?_
      exact hN2 x y (hUv x hx).1 (hUv x hx).2 (hUv y (mem_of_mem_erase hy)).1 (hUv y (mem_of_mem_erase hy)).2
        (ne_of_mem_erase hy).symm
    · exact (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun x hx =>
        hN1 x (hCv x hx).1 (hCv x hx).2 _
    · refine (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun x hx =>
        (measure_biUnion_null_iff (Finset.countable_toSet _)).2 fun y hy => ?_
      exact hN2 x y (hCv x hx).1 (hCv x hx).2 (hCv y (mem_of_mem_erase hy)).1 (hCv y (mem_of_mem_erase hy)).2
        (ne_of_mem_erase hy).symm
  refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun ρ hρ => ?_
  simp only [hBad, mem_union, mem_iUnion, not_or, not_exists] at hρ
  obtain ⟨⟨⟨hA, hB⟩, hC⟩, hD⟩ := hρ
  constructor
  · intro i hi j hj hij
    rcases mem_insert.1 hi with rfl | hi <;> rcases mem_insert.1 hj with rfl | hj
    · rfl
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hj
      exact absurd hij.symm (hA y hy)
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
      exact absurd hij (hA x hx)
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hj
      by_contra hne
      have hxy : x ≠ y := fun h => hne (h ▸ rfl)
      exact hB x hx y (mem_erase.2 ⟨Ne.symm hxy, hy⟩) hij
  · intro i hi j hj hij
    rcases mem_insert.1 hi with rfl | hi <;> rcases mem_insert.1 hj with rfl | hj
    · rfl
    · obtain ⟨y, hy, rfl⟩ := mem_image.1 hj
      exact absurd hij.symm (hC y hy)
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
      exact absurd hij (hC x hx)
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hi
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hj
      by_contra hne
      have hxy : x ≠ y := fun h => hne (h ▸ rfl)
      exact hD x hx y (mem_erase.2 ⟨Ne.symm hxy, hy⟩) hij

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne measurable_extendFix')

variable {w : ℕ} {G : Garden w} {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ}
  {fix : GBranch G.tree → Option ℝ} {v : GBranch G.tree}

theorem splicedFourierBMK_eq (fix : GBranch G.tree → Option ℝ) (α : GBranch G.tree → ℝ) :
    splicedFourierBMK G layer rootTime fix α =
      ∫ τ : {x : GBranch G.tree // fix x = none} → ℝ,
        (splicedTimeDomainFix G layer rootTime fix).indicator (phaseF α) (G.extendFix fix τ) := rfl

/-- The rest-time cell integrands. -/
def Tcell (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (v : GBranch G.tree) (α : GBranch G.tree → ℝ) (i : Option (GBranch G.tree)) (X : GBranch G.tree → ℝ) : ℂ :=
  if restOK layer rootTime fix v X ∧ upCell (layer := layer) (rootTime := rootTime) fix v i X then
    phaseF α (Function.update X v 0) * expAt (Real.pi * α v) (upV layer rootTime fix v X i) else 0

def Scell (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (v : GBranch G.tree) (α : GBranch G.tree → ℝ) (j : Option (GBranch G.tree)) (X : GBranch G.tree → ℝ) : ℂ :=
  if restOK layer rootTime fix v X ∧ loCell (layer := layer) (rootTime := rootTime) fix v j X then
    phaseF α (Function.update X v 0) * expAt (Real.pi * α v) (loV layer fix v X j) else 0

theorem continuous_cellg (α : GBranch G.tree → ℝ) (v : GBranch G.tree) (f : (GBranch G.tree → ℝ) → ℝ)
    (hf : Continuous f) :
    Continuous fun X : GBranch G.tree → ℝ => phaseF α (Function.update X v 0) * expAt (Real.pi * α v) (f X) := by
  refine ((continuous_phaseF α).comp (continuous_id.update v continuous_const)).mul ?_
  unfold expAt
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul hf)).mul
    continuous_const)

theorem norm_cellg (α : GBranch G.tree → ℝ) (v : GBranch G.tree) (X : GBranch G.tree → ℝ) (s : ℝ) :
    ‖phaseF α (Function.update X v 0) * expAt (Real.pi * α v) s‖ = 1 := by
  rw [norm_mul, norm_phaseF, expAt, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem continuous_upV (o : Option (GBranch G.tree)) :
    Continuous fun X : GBranch G.tree → ℝ => upV layer rootTime fix v X o := by
  cases o with
  | none => exact continuous_const
  | some x => exact continuous_apply x
theorem continuous_loV (o : Option (GBranch G.tree)) :
    Continuous fun X : GBranch G.tree → ℝ => loV layer fix v X o := by
  cases o with
  | none => exact continuous_const
  | some x => exact continuous_apply x

theorem integrable_Tcell (α : GBranch G.tree → ℝ) (i : Option (GBranch G.tree))
    (fix₁ : GBranch G.tree → Option ℝ) (h₁ : ∀ x, fix₁ x = none → x ≠ v ∧ fix x = none) :
    Integrable fun ρ : {x : GBranch G.tree // fix₁ x = none} → ℝ =>
      Tcell layer rootTime fix v α i (G.extendFix fix₁ ρ) := by
  have := integrable_of_closed_box (G.extendFix fix₁) (measurable_extendFix' fix₁) _
    (measurableSet_upCell (layer := layer) (rootTime := rootTime) fix v i) _
    (continuous_cellg α v _ (continuous_upV (layer := layer) (rootTime := rootTime) (fix := fix) (v := v) i)).measurable (fun X => (norm_cellg α v X _).le)
    (fun x => (layer x.1 : ℝ)) (fun ρ hρ x => by
      have h := (hρ.1.1 x.1 (h₁ x.1 x.2).1 (h₁ x.1 x.2).2).1
      rw [extendFix_of_none fix₁ ρ x.1 x.2] at h
      exact ⟨h.1, h.2⟩)
  refine this.congr (Filter.Eventually.of_forall fun ρ => ?_)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Tcell]

theorem integrable_Scell (α : GBranch G.tree → ℝ) (j : Option (GBranch G.tree))
    (fix₁ : GBranch G.tree → Option ℝ) (h₁ : ∀ x, fix₁ x = none → x ≠ v ∧ fix x = none) :
    Integrable fun ρ : {x : GBranch G.tree // fix₁ x = none} → ℝ =>
      Scell layer rootTime fix v α j (G.extendFix fix₁ ρ) := by
  have := integrable_of_closed_box (G.extendFix fix₁) (measurable_extendFix' fix₁) _
    (measurableSet_loCell (layer := layer) (rootTime := rootTime) fix v j) _
    (continuous_cellg α v _ (continuous_loV (layer := layer) (fix := fix) (v := v) j)).measurable (fun X => (norm_cellg α v X _).le)
    (fun x => (layer x.1 : ℝ)) (fun ρ hρ x => by
      have h := (hρ.1.1 x.1 (h₁ x.1 x.2).1 (h₁ x.1 x.2).2).1
      rw [extendFix_of_none fix₁ ρ x.1 x.2] at h
      exact ⟨h.1, h.2⟩)
  refine this.congr (Filter.Eventually.of_forall fun ρ => ?_)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Scell]

theorem fixSel_single_none {x : GBranch G.tree} (h : fixSel fix {v} x = none) : x ≠ v ∧ fix x = none := by
  by_cases hx : x = v
  · subst hx; simp [fixSel] at h
  · exact ⟨hx, by simpa [fixSel, hx] using h⟩

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne measurable_extendFix')

variable {w : ℕ} {G : Garden w} {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ}
  {fix : GBranch G.tree → Option ℝ} {v : GBranch G.tree}

/-! ### Rewriting the cell conditions -/

theorem loI_lt_iff (X : GBranch G.tree → ℝ) (y : ℝ) :
    (∀ j ∈ loI fix v, loV layer fix v X j < y) ↔ cfl layer fix v < y ∧ ∀ c ∈ Cf fix v, X c < y := by
  constructor
  · intro h
    exact ⟨h none (mem_insert_self _ _), fun c hc => h (some c) (mem_insert_of_mem (mem_image_of_mem _ hc))⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases mem_insert.1 hj with rfl | hj
    · exact h1
    · obtain ⟨c, hc, rfl⟩ := mem_image.1 hj; exact h2 c hc

theorem lt_upI_iff (X : GBranch G.tree → ℝ) (y : ℝ) :
    (∀ i ∈ upI fix v, y < upV layer rootTime fix v X i) ↔ y < ctop layer rootTime fix v ∧ ∀ u ∈ Uf fix v, y < X u := by
  constructor
  · intro h
    exact ⟨h none (mem_insert_self _ _), fun u hu => h (some u) (mem_insert_of_mem (mem_image_of_mem _ hu))⟩
  · rintro ⟨h1, h2⟩ j hj
    rcases mem_insert.1 hj with rfl | hj
    · exact h1
    · obtain ⟨u, hu, rfl⟩ := mem_image.1 hj; exact h2 u hu

theorem upI_ne_none_iff (X : GBranch G.tree → ℝ) (y : ℝ) :
    (∀ j ∈ upI fix v, j ≠ none → y < upV layer rootTime fix v X j) ↔ ∀ u ∈ Uf fix v, y < X u := by
  constructor
  · intro h u hu; exact h (some u) (mem_insert_of_mem (mem_image_of_mem _ hu)) (by simp)
  · intro h j hj hjn
    rcases mem_insert.1 hj with rfl | hj
    · exact absurd rfl hjn
    · obtain ⟨u, hu, rfl⟩ := mem_image.1 hj; exact h u hu

theorem upI_ne_some_iff {u : GBranch G.tree} (hu : u ∈ Uf fix v) (X : GBranch G.tree → ℝ) (y : ℝ) :
    (∀ j ∈ upI fix v, j ≠ some u → y < upV layer rootTime fix v X j) ↔ y < ctop layer rootTime fix v := by
  constructor
  · intro h; exact h none (mem_insert_self _ _) (by simp)
  · intro h j hj hjn
    rcases mem_insert.1 hj with rfl | hj
    · exact h
    · obtain ⟨u', hu', rfl⟩ := mem_image.1 hj
      exact absurd (congrArg some (isChildOf_parent_unique (mem_Uf.1 hu').1 (mem_Uf.1 hu).1)) hjn

theorem loI_ne_none_iff (X : GBranch G.tree → ℝ) (y : ℝ) :
    (∀ j ∈ loI fix v, j ≠ none → loV layer fix v X j < y) ↔ ∀ c ∈ Cf fix v, X c < y := by
  constructor
  · intro h c hc; exact h (some c) (mem_insert_of_mem (mem_image_of_mem _ hc)) (by simp)
  · intro h j hj hjn
    rcases mem_insert.1 hj with rfl | hj
    · exact absurd rfl hjn
    · obtain ⟨c, hc, rfl⟩ := mem_image.1 hj; exact h c hc

theorem loI_ne_some_iff (c : GBranch G.tree) (X : GBranch G.tree → ℝ) (y : ℝ) :
    (∀ j ∈ loI fix v, j ≠ some c → loV layer fix v X j < y) ↔
      cfl layer fix v < y ∧ ∀ c' ∈ Cf fix v, c' ≠ c → X c' < y := by
  constructor
  · intro h
    exact ⟨h none (mem_insert_self _ _) (by simp), fun c' hc' hcc =>
      h (some c') (mem_insert_of_mem (mem_image_of_mem _ hc')) (by simpa using hcc)⟩
  · rintro ⟨h1, h2⟩ j hj hjn
    rcases mem_insert.1 hj with rfl | hj
    · exact h1
    · obtain ⟨c', hc', rfl⟩ := mem_image.1 hj; exact h2 c' hc' (by simpa using hjn)

/-! ### The four kinds of faces -/

theorem Tcell_none_eq (α : GBranch G.tree → ℝ) (hct : cfl layer fix v < ctop layer rootTime fix v)
    (X : GBranch G.tree → ℝ) :
    Tcell layer rootTime fix v α none X =
      (splicedTimeDomainFix G layer rootTime (pin fix v (ctop layer rootTime fix v))).indicator (phaseF α)
        (Function.update X v (ctop layer rootTime fix v)) := by
  have hiff : (restOK layer rootTime fix v X ∧ upCell (layer := layer) (rootTime := rootTime) fix v none X) ↔
      Function.update X v (ctop layer rootTime fix v) ∈
        splicedTimeDomainFix G layer rootTime (pin fix v (ctop layer rootTime fix v)) := by
    rw [mem_dom_pin_update, upCell, loI_lt_iff, upI_ne_none_iff]
    simp only [upV, Option.elim]
    constructor
    · rintro ⟨h1, ⟨-, h2⟩, h3⟩
      exact ⟨h1, fun c hc hfc => h2 c (mem_Cf.2 ⟨hc, hfc⟩), fun u hu hfu => h3 u (mem_Uf.2 ⟨hu, hfu⟩)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, ⟨hct, fun c hc => h2 c (mem_Cf.1 hc).1 (mem_Cf.1 hc).2⟩,
        fun u hu => h3 u (mem_Uf.1 hu).1 (mem_Uf.1 hu).2⟩
  unfold Tcell
  rw [indicator_apply]
  by_cases h : restOK layer rootTime fix v X ∧ upCell (layer := layer) (rootTime := rootTime) fix v none X
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h), phaseF_update α X v (ctop layer rootTime fix v)]; rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.2 h'))]

theorem Scell_none_eq (α : GBranch G.tree → ℝ) (hct : cfl layer fix v < ctop layer rootTime fix v)
    (X : GBranch G.tree → ℝ) :
    Scell layer rootTime fix v α none X =
      (splicedTimeDomainFix G layer rootTime (pin fix v (cfl layer fix v))).indicator (phaseF α)
        (Function.update X v (cfl layer fix v)) := by
  have hiff : (restOK layer rootTime fix v X ∧ loCell (layer := layer) (rootTime := rootTime) fix v none X) ↔
      Function.update X v (cfl layer fix v) ∈
        splicedTimeDomainFix G layer rootTime (pin fix v (cfl layer fix v)) := by
    rw [mem_dom_pin_update, loCell, lt_upI_iff, loI_ne_none_iff]
    simp only [loV, Option.elim]
    constructor
    · rintro ⟨h1, ⟨-, h3⟩, h2⟩
      exact ⟨h1, fun c hc hfc => h2 c (mem_Cf.2 ⟨hc, hfc⟩), fun u hu hfu => h3 u (mem_Uf.2 ⟨hu, hfu⟩)⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, ⟨hct, fun u hu => h3 u (mem_Uf.1 hu).1 (mem_Uf.1 hu).2⟩,
        fun c hc => h2 c (mem_Cf.1 hc).1 (mem_Cf.1 hc).2⟩
  unfold Scell
  rw [indicator_apply]
  by_cases h : restOK layer rootTime fix v X ∧ loCell (layer := layer) (rootTime := rootTime) fix v none X
  · rw [ite_eq_left h, ite_eq_left (hiff.1 h), phaseF_update α X v (cfl layer fix v)]; rfl
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.2 h'))]

theorem Tcell_none_zero (α : GBranch G.tree → ℝ) (hct : ¬ cfl layer fix v < ctop layer rootTime fix v)
    (X : GBranch G.tree → ℝ) : Tcell layer rootTime fix v α none X = 0 := by
  unfold Tcell; rw [ite_eq_right]; rintro ⟨-, h, -⟩; exact hct (h none (mem_insert_self _ _))

theorem Scell_none_zero (α : GBranch G.tree → ℝ) (hct : ¬ cfl layer fix v < ctop layer rootTime fix v)
    (X : GBranch G.tree → ℝ) : Scell layer rootTime fix v α none X = 0 := by
  unfold Scell; rw [ite_eq_right]; rintro ⟨-, h, -⟩; exact hct (h none (mem_insert_self _ _))

/-- **The parent face, pointwise.** -/
theorem Tcell_some_eq (hv : fix v = none) (α : GBranch G.tree → ℝ) {u : GBranch G.tree} (hu : u ∈ Uf fix v)
    (Y : GBranch G.tree → ℝ) (hY : ∀ x s, fix x = some s → Y x = s) (r : ℝ) (hYu : Y u = r) :
    Tcell layer rootTime fix v α (some u) Y =
      (Iup layer rootTime fix v u).indicator (fun r =>
        (splicedTimeDomainFix G layer rootTime (pin (pin fix v r) u r)).indicator (phaseF α)
          (Function.update Y v r)) r := by
  obtain ⟨hvu, hfu⟩ := mem_Uf.1 hu
  have hK := mem_Iup_dom_iff (layer := layer) (rootTime := rootTime) hv hvu hfu Y hY r hYu
  have hiff : (restOK layer rootTime fix v Y ∧ upCell (layer := layer) (rootTime := rootTime) fix v (some u) Y) ↔
      (restOK layer rootTime fix v Y ∧ loX layer fix v Y < r ∧ r < ctop layer rootTime fix v) := by
    rw [upCell, upI_ne_some_iff hu, loX_lt_iff, ← loI_lt_iff]
    simp only [upV, Option.elim, hYu]
  unfold Tcell
  simp only [indicator_apply]
  by_cases h : restOK layer rootTime fix v Y ∧ upCell (layer := layer) (rootTime := rootTime) fix v (some u) Y
  · obtain ⟨h1, h2⟩ := hK.2 (hiff.1 h)
    rw [ite_eq_left h, ite_eq_left h1, ite_eq_left h2, phaseF_update α Y v r]
    simp only [upV, Option.elim, hYu]; rfl
  · rw [ite_eq_right h]
    by_cases h1 : r ∈ Iup layer rootTime fix v u
    · rw [ite_eq_left h1, ite_eq_right (fun h2 => h (hiff.2 (hK.1 ⟨h1, h2⟩)))]
    · rw [ite_eq_right h1]

/-- **The child face, pointwise.** -/
theorem Scell_some_eq (hv : fix v = none) (α : GBranch G.tree → ℝ) {c : GBranch G.tree} (hc : c ∈ Cf fix v)
    (Y : GBranch G.tree → ℝ) (hY : ∀ x s, fix x = some s → Y x = s) (r : ℝ) (hYc : Y c = r) :
    Scell layer rootTime fix v α (some c) Y =
      (Ilo layer rootTime fix v c).indicator (fun r =>
        (splicedTimeDomainFix G layer rootTime (pin (pin fix v r) c r)).indicator (phaseF α)
          (Function.update Y v r)) r := by
  obtain ⟨hcv, hfc⟩ := mem_Cf.1 hc
  have hK := mem_Ilo_dom_iff (layer := layer) (rootTime := rootTime) hv hcv hfc Y hY r hYc
  have hiff : (restOK layer rootTime fix v Y ∧ loCell (layer := layer) (rootTime := rootTime) fix v (some c) Y) ↔
      (restOK layer rootTime fix v Y ∧ r < hiX layer rootTime fix v Y ∧ cfl layer fix v < r ∧
        ∀ c' ∈ Cf fix v, c' ≠ c → Y c' < r) := by
    rw [loCell, loI_ne_some_iff, lt_hiX_iff, ← lt_upI_iff]
    simp only [loV, Option.elim, hYc]
  unfold Scell
  simp only [indicator_apply]
  by_cases h : restOK layer rootTime fix v Y ∧ loCell (layer := layer) (rootTime := rootTime) fix v (some c) Y
  · obtain ⟨h1, h2⟩ := hK.2 (hiff.1 h)
    rw [ite_eq_left h, ite_eq_left h1, ite_eq_left h2, phaseF_update α Y v r]
    simp only [loV, Option.elim, hYc]; rfl
  · rw [ite_eq_right h]
    by_cases h1 : r ∈ Ilo layer rootTime fix v c
    · rw [ite_eq_left h1, ite_eq_right (fun h2 => h (hiff.2 (hK.1 ⟨h1, h2⟩)))]
    · rw [ite_eq_right h1]

end WaveTurbulence.Flower.SelRes

