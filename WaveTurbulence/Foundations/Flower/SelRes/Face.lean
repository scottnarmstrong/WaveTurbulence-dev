/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.FaceCells

/-! # D7 SEL-RES / Face: supplement Lemma 9.1 for the pinned time transform, in pinned form (o73 (20.5))

`face_expand`: for a free branch `v` with frequency `α_v ≠ 0`, `splicedFourierBMK … fix α` is `(iπα_v)⁻¹` times
(top face + parent faces − floor face − child faces), each face a pinned transform: `v` pinned at the constant
endpoint, or `v` and its free parent (child) pinned at a common time `r` integrated over the interval `Iup` (`Ilo`).
`integrable_parFace`, `integrable_chFace`: the face integrands are integrable in `r`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne measurable_extendFix')

variable {w : ℕ} {G : Garden w} {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ}

theorem integral_pin2_eq (fix : GBranch G.tree → Option ℝ) (v u : GBranch G.tree) (huv : u ≠ v) (r : ℝ)
    (F : (GBranch G.tree → ℝ) → ℂ) :
    (∫ τ : {x : GBranch G.tree // pin (pin fix v r) u r x = none} → ℝ, F (G.extendFix (pin (pin fix v r) u r) τ)) =
      ∫ ρ : {x : GBranch G.tree // fixSel (fixSel fix {v}) {u} x = none} → ℝ,
        F (Function.update (Function.update (G.extendFix (fixSel (fixSel fix {v}) {u}) ρ) u r) v r) := by
  refine integral_extendFix_congr _ _ (fun x => ?_) F
    (fun t => F (Function.update (Function.update t u r) v r)) fun t => ?_
  · by_cases hxu : x = u
    · subst hxu; simp [pin, fixSel]
    by_cases hxv : x = v
    · subst hxv; simp [pin, fixSel, hxu]
    · simp [pin, fixSel, hxu, hxv]
  · congr 1
    funext x
    by_cases hxv : x = v
    · subst hxv; simp [fillT, pin, Function.update_of_ne (Ne.symm huv)]
    by_cases hxu : x = u
    · subst hxu; simp [fillT, pin, hxv]
    · simp [fillT, pin, fixSel, hxu, hxv]

/-- **Supplement Lemma 9.1 for the pinned time transform, in pinned form.** For a free branch `v` with nonzero
frequency, the pinned time transform is `(iπα_v)⁻¹` times: the top face (`v` pinned at the constant upper endpoint)
plus the parent faces (`v` and its free parent pinned at a common time `r`, integrated over `r`), minus the floor face
(`v` pinned at the constant lower endpoint) and minus the child faces (`v` and a free child pinned at `r`). -/
theorem face_expand (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (hv : fix v = none)
    (α : GBranch G.tree → ℝ) (hα : Real.pi * α v ≠ 0) :
    splicedFourierBMK G layer rootTime fix α =
      (((Real.pi * α v : ℝ) : ℂ) * Complex.I)⁻¹ *
        (((if cfl layer fix v < ctop layer rootTime fix v then
              splicedFourierBMK G layer rootTime (pin fix v (ctop layer rootTime fix v)) α else 0) +
            ∑ u ∈ Uf fix v, ∫ r, (Iup layer rootTime fix v u).indicator
              (fun r => splicedFourierBMK G layer rootTime (pin (pin fix v r) u r) α) r) -
          ((if cfl layer fix v < ctop layer rootTime fix v then
              splicedFourierBMK G layer rootTime (pin fix v (cfl layer fix v)) α else 0) +
            ∑ c ∈ Cf fix v, ∫ r, (Ilo layer rootTime fix v c).indicator
              (fun r => splicedFourierBMK G layer rootTime (pin (pin fix v r) c r) α) r)) := by
  have h₁ : ∀ x, (fixSel fix {v}) x = none → x ≠ v ∧ fix x = none := fun x hx => fixSel_single_none hx
  have hpin : ∀ ρ : {x // (fixSel fix {v}) x = none} → ℝ, ∀ x s, fix x = some s → G.extendFix (fixSel fix {v}) ρ x = s :=
    extendFix_fixSel_pinned fix {v} (by simpa using hv)
  -- Steps 1–2: Fubini at `v` and the inner integral
  rw [splicedFourierBMK_eq, integral_extendFix_split fix v hv _ (integrable_dom (layer := layer) (rootTime := rootTime) fix α)]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun ρ =>
    integral_inner (layer := layer) (rootTime := rootTime) fix v hv α hα _ (hpin ρ))]
  -- Step 3: the cell identity, almost everywhere
  have hcell : ∀ᵐ ρ : ({x // (fixSel fix {v}) x = none} → ℝ),
      (if restOK layer rootTime fix v (G.extendFix (fixSel fix {v}) ρ) then
          phaseF α (Function.update (G.extendFix (fixSel fix {v}) ρ) v 0) else 0) *
        ((((Real.pi * α v : ℝ) : ℂ) * Complex.I)⁻¹ *
          (if loX layer fix v (G.extendFix (fixSel fix {v}) ρ) < hiX layer rootTime fix v (G.extendFix (fixSel fix {v}) ρ) then
            expAt (Real.pi * α v) (hiX layer rootTime fix v (G.extendFix (fixSel fix {v}) ρ)) - expAt (Real.pi * α v) (loX layer fix v (G.extendFix (fixSel fix {v}) ρ))
          else 0)) =
        (((Real.pi * α v : ℝ) : ℂ) * Complex.I)⁻¹ *
          ((∑ i ∈ upI fix v, Tcell layer rootTime fix v α i (G.extendFix (fixSel fix {v}) ρ)) -
            ∑ j ∈ loI fix v, Scell layer rootTime fix v α j (G.extendFix (fixSel fix {v}) ρ)) := by
    refine (ae_generic (layer := layer) (rootTime := rootTime) fix v).mono fun ρ ⟨hU, hL⟩ => ?_
    set X := G.extendFix (fixSel fix {v}) ρ
    have hci := cells_identity (upI fix v) (upI_nonempty fix v) (upV layer rootTime fix v X) hU
      (loI fix v) (loI_nonempty fix v) (loV layer fix v X) hL (expAt (Real.pi * α v))
    have e1 : loX layer fix v X = (loI fix v).sup' (loI_nonempty fix v) (loV layer fix v X) := rfl
    have e2 : hiX layer rootTime fix v X = (upI fix v).inf' (upI_nonempty fix v) (upV layer rootTime fix v X) := rfl
    rw [e1, e2, hci]
    unfold Tcell Scell upCell loCell
    by_cases hR : restOK layer rootTime fix v X
    · simp only [hR, true_and, ite_true]
      rw [mul_left_comm, mul_sub, Finset.mul_sum, Finset.mul_sum]
      congr 2 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> split_ifs <;> simp
    · simp only [hR, false_and, ite_false, zero_mul, Finset.sum_const_zero, sub_self, mul_zero]
  rw [integral_congr_ae hcell, integral_const_mul]
  congr 1
  -- Step 4: linearity
  have hT : ∀ i, Integrable fun ρ : {x // (fixSel fix {v}) x = none} → ℝ => Tcell layer rootTime fix v α i (G.extendFix (fixSel fix {v}) ρ) :=
    fun i => integrable_Tcell α i (fixSel fix {v}) h₁
  have hS : ∀ j, Integrable fun ρ : {x // (fixSel fix {v}) x = none} → ℝ => Scell layer rootTime fix v α j (G.extendFix (fixSel fix {v}) ρ) :=
    fun j => integrable_Scell α j (fixSel fix {v}) h₁
  rw [integral_sub (integrable_finsetSum _ fun i _ => hT i) (integrable_finsetSum _ fun j _ => hS j),
    integral_finsetSum _ fun i _ => hT i, integral_finsetSum _ fun j _ => hS j]
  -- Step 5: split the index sets
  have hnU : none ∉ (Uf fix v).image some := by simp
  have hnC : none ∉ (Cf fix v).image some := by simp
  rw [upI, loI, Finset.sum_insert hnU, Finset.sum_insert hnC,
    Finset.sum_image (fun _ _ _ _ h => Option.some_injective _ h),
    Finset.sum_image (fun _ _ _ _ h => Option.some_injective _ h)]
  -- Step 6: the constant faces
  have htop : (∫ ρ : {x // (fixSel fix {v}) x = none} → ℝ, Tcell layer rootTime fix v α none (G.extendFix (fixSel fix {v}) ρ)) =
      if cfl layer fix v < ctop layer rootTime fix v then
        splicedFourierBMK G layer rootTime (pin fix v (ctop layer rootTime fix v)) α else 0 := by
    split_ifs with hct
    · rw [splicedFourierBMK_eq, integral_pin_eq]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ρ => Tcell_none_eq α hct _)
    · exact (integral_congr_ae (Filter.Eventually.of_forall fun ρ => Tcell_none_zero α hct _)).trans (integral_zero _ _)
  have hfl : (∫ ρ : {x // (fixSel fix {v}) x = none} → ℝ, Scell layer rootTime fix v α none (G.extendFix (fixSel fix {v}) ρ)) =
      if cfl layer fix v < ctop layer rootTime fix v then
        splicedFourierBMK G layer rootTime (pin fix v (cfl layer fix v)) α else 0 := by
    split_ifs with hct
    · rw [splicedFourierBMK_eq, integral_pin_eq]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ρ => Scell_none_eq α hct _)
    · exact (integral_congr_ae (Filter.Eventually.of_forall fun ρ => Scell_none_zero α hct _)).trans (integral_zero _ _)
  -- Step 7: the parent and child faces
  have hpar : ∀ u ∈ Uf fix v,
      (∫ ρ : {x // (fixSel fix {v}) x = none} → ℝ, Tcell layer rootTime fix v α (some u) (G.extendFix (fixSel fix {v}) ρ)) =
        ∫ r, (Iup layer rootTime fix v u).indicator
          (fun r => splicedFourierBMK G layer rootTime (pin (pin fix v r) u r) α) r := by
    intro u hu
    obtain ⟨hvu, hfu⟩ := mem_Uf.1 hu
    have huv : u ≠ v := (IsChildOf.ne hvu).symm
    have hf1u : (fixSel fix {v}) u = none := fixSel_none_of huv hfu
    rw [integral_extendFix_split' (fixSel fix {v}) u hf1u _ (hT (some u))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [splicedFourierBMK_eq]
    have hY : ∀ ρ' : {x // fixSel (fixSel fix {v}) {u} x = none} → ℝ, ∀ x s, fix x = some s →
        Function.update (G.extendFix (fixSel (fixSel fix {v}) {u}) ρ') u r x = s := by
      intro ρ' x s hs
      have hxu : x ≠ u := fun h => by rw [h, hfu] at hs; exact absurd hs (by simp)
      have hxv : x ≠ v := fun h => by rw [h, hv] at hs; exact absurd hs (by simp)
      rw [Function.update_of_ne hxu]
      refine extendFix_fixSel_pinned (fixSel fix {v}) {u} (by simpa using hf1u) ρ' x s ?_
      simp [fixSel, hxv, hs]
    simp_rw [fun ρ' => Tcell_some_eq (layer := layer) (rootTime := rootTime) hv α hu _ (hY ρ') r
      (Function.update_self _ _ _)]
    by_cases hr : r ∈ Iup layer rootTime fix v u
    · simp only [indicator_of_mem hr]
      exact (integral_pin2_eq fix v u huv r _).symm
    · simp only [indicator_of_notMem hr, integral_zero]
  have hch : ∀ c ∈ Cf fix v,
      (∫ ρ : {x // (fixSel fix {v}) x = none} → ℝ, Scell layer rootTime fix v α (some c) (G.extendFix (fixSel fix {v}) ρ)) =
        ∫ r, (Ilo layer rootTime fix v c).indicator
          (fun r => splicedFourierBMK G layer rootTime (pin (pin fix v r) c r) α) r := by
    intro c hc
    obtain ⟨hcv, hfc⟩ := mem_Cf.1 hc
    have hcv' : c ≠ v := IsChildOf.ne hcv
    have hf1c : (fixSel fix {v}) c = none := fixSel_none_of hcv' hfc
    rw [integral_extendFix_split' (fixSel fix {v}) c hf1c _ (hS (some c))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [splicedFourierBMK_eq]
    have hY : ∀ ρ' : {x // fixSel (fixSel fix {v}) {c} x = none} → ℝ, ∀ x s, fix x = some s →
        Function.update (G.extendFix (fixSel (fixSel fix {v}) {c}) ρ') c r x = s := by
      intro ρ' x s hs
      have hxc : x ≠ c := fun h => by rw [h, hfc] at hs; exact absurd hs (by simp)
      have hxv : x ≠ v := fun h => by rw [h, hv] at hs; exact absurd hs (by simp)
      rw [Function.update_of_ne hxc]
      refine extendFix_fixSel_pinned (fixSel fix {v}) {c} (by simpa using hf1c) ρ' x s ?_
      simp [fixSel, hxv, hs]
    simp_rw [fun ρ' => Scell_some_eq (layer := layer) (rootTime := rootTime) hv α hc _ (hY ρ') r
      (Function.update_self _ _ _)]
    by_cases hr : r ∈ Ilo layer rootTime fix v c
    · simp only [indicator_of_mem hr]
      exact (integral_pin2_eq fix v c hcv' r _).symm
    · simp only [indicator_of_notMem hr, integral_zero]
  rw [htop, hfl, Finset.sum_congr rfl hpar, Finset.sum_congr rfl hch]

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.FlFace (splitEquiv measurePreserving_splitEquiv fixSel fixSel_eq_none extendFix_of_none
  extendFix_of_some children parents mem_children mem_parents IsChildOf.ne measurable_extendFix')

variable {w : ℕ} {G : Garden w} {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ}

/-- The inner integral of the one-branch Fubini decomposition is integrable in the branch time. -/
theorem integrable_extendFix_split' (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) (hb : fix b = none)
    (F : (GBranch G.tree → ℝ) → ℂ)
    (hF : Integrable fun τ : {x : GBranch G.tree // fix x = none} → ℝ => F (G.extendFix fix τ)) :
    Integrable fun r : ℝ => ∫ ρ : {x : GBranch G.tree // fixSel fix {b} x = none} → ℝ,
      F (Function.update (G.extendFix (fixSel fix {b}) ρ) b r) := by
  have hb' : ∀ v ∈ ({b} : Finset (GBranch G.tree)), fix v = none := by simpa using hb
  have hmp := measurePreserving_splitEquiv fix {b} hb'
  set f : ({x : GBranch G.tree // fix x = none} → ℝ) → ℂ := fun τ => F (G.extendFix fix τ) with hf
  have hint : Integrable (fun x => f (splitEquiv fix {b} hb' x)) ((volume : Measure (({b} : Finset _) → ℝ)).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hmp.integrable_comp_emb (splitEquiv fix {b} hb').measurableEmbedding).2 hF
  have h2 := hint.integral_prod_left
  have e1 : ∀ (y : (({b} : Finset (GBranch G.tree)) → ℝ)) ρ,
      f (splitEquiv fix {b} hb' (y, ρ)) =
        F (Function.update (G.extendFix (fixSel fix {b}) ρ) b (MeasurableEquiv.funUnique _ ℝ y)) := by
    intro y ρ
    simp only [hf]
    rw [extendFix_splitEquiv_single fix b hb]
    congr 2
  simp_rw [e1] at h2
  have hu := volume_preserving_funUnique (({b} : Finset (GBranch G.tree))) ℝ
  exact (hu.integrable_comp_emb (MeasurableEquiv.funUnique _ ℝ).measurableEmbedding).1 h2

theorem integrable_parFace (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (hv : fix v = none)
    (α : GBranch G.tree → ℝ) {u : GBranch G.tree} (hu : u ∈ Uf fix v) :
    Integrable fun r => (Iup layer rootTime fix v u).indicator
      (fun r => splicedFourierBMK G layer rootTime (pin (pin fix v r) u r) α) r := by
  obtain ⟨hvu, hfu⟩ := mem_Uf.1 hu
  have huv : u ≠ v := (IsChildOf.ne hvu).symm
  have hf1u : fixSel fix {v} u = none := fixSel_none_of huv hfu
  have h₁ : ∀ x, (fixSel fix {v}) x = none → x ≠ v ∧ fix x = none := fun x hx => fixSel_single_none hx
  have hint := integrable_extendFix_split' (fixSel fix {v}) u hf1u _
    (integrable_Tcell (layer := layer) (rootTime := rootTime) (fix := fix) (v := v) α (some u) _ h₁)
  refine hint.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [splicedFourierBMK_eq]
  have hY : ∀ ρ' : {x // fixSel (fixSel fix {v}) {u} x = none} → ℝ, ∀ x s, fix x = some s →
      Function.update (G.extendFix (fixSel (fixSel fix {v}) {u}) ρ') u r x = s := by
    intro ρ' x s hs
    have hxu : x ≠ u := fun h => by rw [h, hfu] at hs; exact absurd hs (by simp)
    have hxv : x ≠ v := fun h => by rw [h, hv] at hs; exact absurd hs (by simp)
    rw [Function.update_of_ne hxu]
    refine extendFix_fixSel_pinned (fixSel fix {v}) {u} (by simpa using hf1u) ρ' x s ?_
    simp [fixSel, hxv, hs]
  simp_rw [fun ρ' => Tcell_some_eq (layer := layer) (rootTime := rootTime) hv α hu _ (hY ρ') r
    (Function.update_self _ _ _)]
  by_cases hr : r ∈ Iup layer rootTime fix v u
  · simp only [indicator_of_mem hr]
    exact (integral_pin2_eq fix v u huv r _).symm
  · simp only [indicator_of_notMem hr, integral_zero]

theorem integrable_chFace (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (hv : fix v = none)
    (α : GBranch G.tree → ℝ) {c : GBranch G.tree} (hc : c ∈ Cf fix v) :
    Integrable fun r => (Ilo layer rootTime fix v c).indicator
      (fun r => splicedFourierBMK G layer rootTime (pin (pin fix v r) c r) α) r := by
  obtain ⟨hcv, hfc⟩ := mem_Cf.1 hc
  have hcv' : c ≠ v := IsChildOf.ne hcv
  have hf1c : fixSel fix {v} c = none := fixSel_none_of hcv' hfc
  have h₁ : ∀ x, (fixSel fix {v}) x = none → x ≠ v ∧ fix x = none := fun x hx => fixSel_single_none hx
  have hint := integrable_extendFix_split' (fixSel fix {v}) c hf1c _
    (integrable_Scell (layer := layer) (rootTime := rootTime) (fix := fix) (v := v) α (some c) _ h₁)
  refine hint.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [splicedFourierBMK_eq]
  have hY : ∀ ρ' : {x // fixSel (fixSel fix {v}) {c} x = none} → ℝ, ∀ x s, fix x = some s →
      Function.update (G.extendFix (fixSel (fixSel fix {v}) {c}) ρ') c r x = s := by
    intro ρ' x s hs
    have hxc : x ≠ c := fun h => by rw [h, hfc] at hs; exact absurd hs (by simp)
    have hxv : x ≠ v := fun h => by rw [h, hv] at hs; exact absurd hs (by simp)
    rw [Function.update_of_ne hxc]
    refine extendFix_fixSel_pinned (fixSel fix {v}) {c} (by simpa using hf1c) ρ' x s ?_
    simp [fixSel, hxv, hs]
  simp_rw [fun ρ' => Scell_some_eq (layer := layer) (rootTime := rootTime) hv α hc _ (hY ρ') r
    (Function.update_self _ _ _)]
  by_cases hr : r ∈ Ilo layer rootTime fix v c
  · simp only [indicator_of_mem hr]
    exact (integral_pin2_eq fix v c hcv' r _).symm
  · simp only [indicator_of_notMem hr, integral_zero]

end WaveTurbulence.Flower.SelRes
