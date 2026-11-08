/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Fine
public import WaveTurbulence.Foundations.Flower.FlFace.Expand
public import WaveTurbulence.Foundations.FlowerTop.Port.FixLemmas

/-! # D7 SEL-RES / Pin: pinning one free branch of the marked time domain

- `pin fix b r`: the branch `b` pinned at the time `r`; `fillT` the filled time vector.
- `integral_extendFix_congr`: reindexing the free coordinates; `integral_pin_eq`: a pinned integral as an integral
  over the remaining free coordinates (`fixSel fix {b}`, FL-FACE).
- `integral_extendFix_split`, `integral_extendFix_split'`: Fubini at one free branch (both orders), from FL-FACE's
  measure-preserving `splitEquiv`.
- `mem_dom_update`, `mem_dom_pin_update`: the time domain `splicedTimeDomainFix` around a free branch `v`
  (`restOK`, the constraints not involving `v`; `slotA`, the admissible times of `v`).
- `phaseF_update` and `integral_slot`: the phase factor of `v` and the one-dimensional integral. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset
open WaveTurbulence.Flower.FlFace (splitEquiv measurePreserving_splitEquiv extendFix_splitEquiv fixSel
  fixSel_eq_none extendFix_of_none extendFix_of_some measurable_extendFix')

variable {w : ℕ} {G : Garden w}

/-- Pin the branch `b` at the time `r`. -/
def pin (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) (r : ℝ) : GBranch G.tree → Option ℝ :=
  Function.update fix b (some r)

/-- The time vector with the pinned values of `fix` and the free values of `t`. -/
def fillT (fix : GBranch G.tree → Option ℝ) (t : GBranch G.tree → ℝ) : GBranch G.tree → ℝ :=
  fun x => (fix x).getD (t x)

theorem extendFix_eq_fillT (fix : GBranch G.tree → Option ℝ) (τ : {x : GBranch G.tree // fix x = none} → ℝ) :
    G.extendFix fix τ = fillT fix (fun x => if h : fix x = none then τ ⟨x, h⟩ else 0) := by
  funext x
  rcases hx : fix x with _ | s
  · rw [extendFix_of_none fix τ x hx]; simp [fillT, hx]
  · rw [extendFix_of_some fix τ x hx]; simp [fillT, hx]

/-- Reindexing the free coordinates: two pin maps with the same free set give the same integral when the
integrands agree on the filled time vectors. -/
theorem integral_extendFix_congr (fix₁ fix₂ : GBranch G.tree → Option ℝ) (h : ∀ x, fix₁ x = none ↔ fix₂ x = none)
    (F₁ F₂ : (GBranch G.tree → ℝ) → ℂ) (hF : ∀ t, F₁ (fillT fix₁ t) = F₂ (fillT fix₂ t)) :
    (∫ τ : {x : GBranch G.tree // fix₁ x = none} → ℝ, F₁ (G.extendFix fix₁ τ)) =
      ∫ τ : {x : GBranch G.tree // fix₂ x = none} → ℝ, F₂ (G.extendFix fix₂ τ) := by
  set e : {x : GBranch G.tree // fix₁ x = none} ≃ {x : GBranch G.tree // fix₂ x = none} :=
    Equiv.subtypeEquivRight h with he
  have hmp := volume_measurePreserving_piCongrLeft (fun _ => ℝ) e
  rw [← hmp.integral_comp' (fun τ => F₂ (G.extendFix fix₂ τ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [extendFix_eq_fillT fix₁, extendFix_eq_fillT fix₂, hF]
  congr 2
  funext x
  by_cases h2 : fix₂ x = none
  · have h1 : fix₁ x = none := (h x).2 h2
    simp only [h1, h2, dite_true]
    rw [show (⟨x, h2⟩ : {x // fix₂ x = none}) = e ⟨x, h1⟩ from rfl]
    exact (Equiv.piCongrLeft_apply_apply (fun _ => ℝ) e τ ⟨x, h1⟩)
  · have h1 : ¬ fix₁ x = none := fun h1 => h2 ((h x).1 h1)
    simp only [h1, h2, dite_false]

theorem fillT_pin (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) (r : ℝ) (t : GBranch G.tree → ℝ) :
    fillT (pin fix b r) t = Function.update (fillT (fixSel fix {b}) t) b r := by
  funext x
  by_cases hx : x = b
  · subst hx; simp [fillT, pin]
  · simp [fillT, pin, fixSel, hx]

theorem pin_eq_none {fix : GBranch G.tree → Option ℝ} {b x : GBranch G.tree} {r : ℝ} :
    pin fix b r x = none ↔ fixSel fix {b} x = none := by
  by_cases hx : x = b
  · subst hx; simp [pin, fixSel]
  · simp [pin, fixSel, hx]

/-- A pinned integral as an integral over the remaining free coordinates (`fixSel`). -/
theorem integral_pin_eq (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) (r : ℝ)
    (F : (GBranch G.tree → ℝ) → ℂ) :
    (∫ τ : {x : GBranch G.tree // pin fix b r x = none} → ℝ, F (G.extendFix (pin fix b r) τ)) =
      ∫ ρ : {x : GBranch G.tree // fixSel fix {b} x = none} → ℝ,
        F (Function.update (G.extendFix (fixSel fix {b}) ρ) b r) := by
  refine integral_extendFix_congr _ _ (fun x => pin_eq_none) F (fun t => F (Function.update t b r)) fun t => ?_
  rw [fillT_pin]

theorem extendFix_splitEquiv_single (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) (hb : fix b = none)
    (x : (({b} : Finset (GBranch G.tree)) → ℝ) × ({y : GBranch G.tree // fixSel fix {b} y = none} → ℝ)) :
    G.extendFix fix (splitEquiv fix {b} (by simpa using hb) x) =
      Function.update (G.extendFix (fixSel fix {b}) x.2) b (x.1 ⟨b, Finset.mem_singleton_self b⟩) := by
  funext y
  rw [extendFix_splitEquiv]
  by_cases hy : y = b
  · subst hy; simp
  · simp [hy]

/-- **Fubini at one free branch** (rest outside, the branch time inside). -/
theorem integral_extendFix_split (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) (hb : fix b = none)
    (F : (GBranch G.tree → ℝ) → ℂ)
    (hF : Integrable fun τ : {x : GBranch G.tree // fix x = none} → ℝ => F (G.extendFix fix τ)) :
    (∫ τ : {x : GBranch G.tree // fix x = none} → ℝ, F (G.extendFix fix τ)) =
      ∫ ρ : {x : GBranch G.tree // fixSel fix {b} x = none} → ℝ,
        ∫ r : ℝ, F (Function.update (G.extendFix (fixSel fix {b}) ρ) b r) := by
  have hb' : ∀ v ∈ ({b} : Finset (GBranch G.tree)), fix v = none := by simpa using hb
  have hmp := measurePreserving_splitEquiv fix {b} hb'
  set f : ({x : GBranch G.tree // fix x = none} → ℝ) → ℂ := fun τ => F (G.extendFix fix τ) with hf
  rw [← hmp.integral_comp' f]
  have hint : Integrable (fun x => f (splitEquiv fix {b} hb' x)) ((volume : Measure (({b} : Finset _) → ℝ)).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hmp.integrable_comp_emb (splitEquiv fix {b} hb').measurableEmbedding).2 hF
  rw [Measure.volume_eq_prod, integral_prod_symm _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
  simp only [hf]
  have hu := volume_preserving_funUnique (({b} : Finset (GBranch G.tree))) ℝ
  have e1 : ∀ y : (({b} : Finset (GBranch G.tree)) → ℝ),
      F (G.extendFix fix (splitEquiv fix {b} hb' (y, ρ))) =
        F (Function.update (G.extendFix (fixSel fix {b}) ρ) b (MeasurableEquiv.funUnique _ ℝ y)) := by
    intro y
    rw [extendFix_splitEquiv_single fix b hb]
    congr 2
  simp_rw [e1]
  exact hu.integral_comp' (fun r => F (Function.update (G.extendFix (fixSel fix {b}) ρ) b r))

/-- **Fubini at one free branch** (the branch time outside). -/
theorem integral_extendFix_split' (fix : GBranch G.tree → Option ℝ) (b : GBranch G.tree) (hb : fix b = none)
    (F : (GBranch G.tree → ℝ) → ℂ)
    (hF : Integrable fun τ : {x : GBranch G.tree // fix x = none} → ℝ => F (G.extendFix fix τ)) :
    (∫ τ : {x : GBranch G.tree // fix x = none} → ℝ, F (G.extendFix fix τ)) =
      ∫ r : ℝ, ∫ ρ : {x : GBranch G.tree // fixSel fix {b} x = none} → ℝ,
        F (Function.update (G.extendFix (fixSel fix {b}) ρ) b r) := by
  have hb' : ∀ v ∈ ({b} : Finset (GBranch G.tree)), fix v = none := by simpa using hb
  have hmp := measurePreserving_splitEquiv fix {b} hb'
  set f : ({x : GBranch G.tree // fix x = none} → ℝ) → ℂ := fun τ => F (G.extendFix fix τ) with hf
  rw [← hmp.integral_comp' f]
  have hint : Integrable (fun x => f (splitEquiv fix {b} hb' x)) ((volume : Measure (({b} : Finset _) → ℝ)).prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hmp.integrable_comp_emb (splitEquiv fix {b} hb').measurableEmbedding).2 hF
  rw [Measure.volume_eq_prod, integral_prod _ hint]
  have hu := volume_preserving_funUnique (({b} : Finset (GBranch G.tree))) ℝ
  have e1 : ∀ (y : (({b} : Finset (GBranch G.tree)) → ℝ)) ρ,
      F (G.extendFix fix (splitEquiv fix {b} hb' (y, ρ))) =
        F (Function.update (G.extendFix (fixSel fix {b}) ρ) b (MeasurableEquiv.funUnique _ ℝ y)) := by
    intro y ρ
    rw [extendFix_splitEquiv_single fix b hb]
    congr 2
  simp only [hf]
  simp_rw [e1]
  exact hu.integral_comp' (fun r => ∫ ρ : {x : GBranch G.tree // fixSel fix {b} x = none} → ℝ,
    F (Function.update (G.extendFix (fixSel fix {b}) ρ) b r))

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FlFace (fixSel fixSel_eq_none extendFix_of_none extendFix_of_some children parents
  mem_children mem_parents IsChildOf.ne)

variable {w : ℕ} {G : Garden w}

theorem isChildOf_asymm {x y : GBranch G.tree} (h : x.IsChildOf y) : ¬ y.IsChildOf x := by
  rintro ⟨_, j, hj⟩
  obtain ⟨_, i, hi⟩ := h
  have h1 := congrArg List.length hi
  have h2 := congrArg List.length hj
  simp only [List.length_append, List.length_singleton] at h1 h2
  omega

theorem isChildOf_parent_unique {x y y' : GBranch G.tree} (h : x.IsChildOf y) (h' : x.IsChildOf y') : y = y' := by
  obtain ⟨h1, i, hi⟩ := h
  obtain ⟨h1', i', hi'⟩ := h'
  have hp : y.1.2 = y'.1.2 := by
    have := hi.symm.trans hi'
    exact (List.append_inj' this (by simp)).1
  exact Subtype.ext (Prod.ext (h1.symm.trans h1') hp)

variable (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)

/-- The constraints of the time domain not involving the branch `v`. -/
def restOK (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (X : GBranch G.tree → ℝ) : Prop :=
  (∀ x, x ≠ v → fix x = none → X x ∈ Icc (layer x : ℝ) (layer x + 1) ∧ X x < rootTime x.1.1) ∧
  ∀ x u, x ≠ v → u ≠ v → x.IsChildOf u → (fix x = none ∨ fix u = none) → X x < X u

/-- The admissible times of the free branch `v` given the other times. -/
def slotA (v : GBranch G.tree) (X : GBranch G.tree → ℝ) : Set ℝ :=
  {r | (layer v : ℝ) ≤ r ∧ r ≤ layer v + 1 ∧ r < rootTime v.1.1 ∧
    (∀ c, c.IsChildOf v → X c < r) ∧ ∀ u, v.IsChildOf u → r < X u}

theorem mem_dom_update (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (hv : fix v = none)
    (X : GBranch G.tree → ℝ) (r : ℝ) :
    Function.update X v r ∈ splicedTimeDomainFix G layer rootTime fix ↔
      restOK layer rootTime fix v X ∧ r ∈ slotA layer rootTime v X := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun x hx hfx => ?_, fun x u hx hu hxu hfn => ?_⟩, ?_, ?_, ?_, fun c hc => ?_, fun u hu => ?_⟩
    · have := h1 x hfx; rwa [Function.update_of_ne hx] at this
    · have := h2 x u hxu hfn; rwa [Function.update_of_ne hx, Function.update_of_ne hu] at this
    · have := (h1 v hv).1.1; rwa [Function.update_self] at this
    · have := (h1 v hv).1.2; rwa [Function.update_self] at this
    · have := (h1 v hv).2; rwa [Function.update_self] at this
    · have := h2 c v hc (Or.inr hv)
      rwa [Function.update_self, Function.update_of_ne (IsChildOf.ne hc)] at this
    · have := h2 v u hu (Or.inl hv)
      rwa [Function.update_self, Function.update_of_ne (IsChildOf.ne hu).symm] at this
  · rintro ⟨⟨h1, h2⟩, hl, hh, hroot, hc, hp⟩
    refine ⟨fun x hfx => ?_, fun x u hxu hfn => ?_⟩
    · by_cases hx : x = v
      · subst hx; rw [Function.update_self]; exact ⟨⟨hl, hh⟩, hroot⟩
      · rw [Function.update_of_ne hx]; exact h1 x hx hfx
    · by_cases hx : x = v
      · subst hx
        rw [Function.update_self, Function.update_of_ne (IsChildOf.ne hxu).symm]; exact hp u hxu
      · by_cases hu : u = v
        · subst hu
          rw [Function.update_self, Function.update_of_ne hx]; exact hc x hxu
        · rw [Function.update_of_ne hx, Function.update_of_ne hu]; exact h2 x u hx hu hxu hfn

theorem pin_apply_of_ne {fix : GBranch G.tree → Option ℝ} {b x : GBranch G.tree} {r : ℝ} (h : x ≠ b) :
    pin fix b r x = fix x := Function.update_of_ne h _ _

theorem mem_dom_pin_update (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree)
    (X : GBranch G.tree → ℝ) (r : ℝ) :
    Function.update X v r ∈ splicedTimeDomainFix G layer rootTime (pin fix v r) ↔
      restOK layer rootTime fix v X ∧ (∀ c, c.IsChildOf v → fix c = none → X c < r) ∧
        ∀ u, v.IsChildOf u → fix u = none → r < X u := by
  have hpv : pin fix v r v = some r := Function.update_self _ _ _
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun x hx hfx => ?_, fun x u hx hu hxu hfn => ?_⟩, fun c hc hfc => ?_, fun u hu hfu => ?_⟩
    · have := h1 x (by rwa [pin_apply_of_ne hx]); rwa [Function.update_of_ne hx] at this
    · have := h2 x u hxu (by rwa [pin_apply_of_ne hx, pin_apply_of_ne hu])
      rwa [Function.update_of_ne hx, Function.update_of_ne hu] at this
    · have := h2 c v hc (Or.inl (by rwa [pin_apply_of_ne (IsChildOf.ne hc)]))
      rwa [Function.update_self, Function.update_of_ne (IsChildOf.ne hc)] at this
    · have := h2 v u hu (Or.inr (by rwa [pin_apply_of_ne (IsChildOf.ne hu).symm]))
      rwa [Function.update_self, Function.update_of_ne (IsChildOf.ne hu).symm] at this
  · rintro ⟨⟨h1, h2⟩, hc, hp⟩
    refine ⟨fun x hfx => ?_, fun x u hxu hfn => ?_⟩
    · by_cases hx : x = v
      · subst hx; rw [hpv] at hfx; exact absurd hfx (by simp)
      · rw [Function.update_of_ne hx]; exact h1 x hx (by rwa [pin_apply_of_ne hx] at hfx)
    · by_cases hx : x = v
      · subst hx
        have hu : u ≠ x := (IsChildOf.ne hxu).symm
        rw [hpv, pin_apply_of_ne hu] at hfn
        rw [Function.update_self, Function.update_of_ne hu]
        exact hp u hxu (hfn.resolve_left (by simp))
      · by_cases hu : u = v
        · subst hu
          rw [hpv, pin_apply_of_ne hx] at hfn
          rw [Function.update_self, Function.update_of_ne hx]
          exact hc x hxu (hfn.resolve_right (by simp))
        · rw [pin_apply_of_ne hx, pin_apply_of_ne hu] at hfn
          rw [Function.update_of_ne hx, Function.update_of_ne hu]; exact h2 x u hx hu hxu hfn

/-- The phase product of `splicedFourierBMK`. -/
def phaseF (α : GBranch G.tree → ℝ) (t : GBranch G.tree → ℝ) : ℂ :=
  ∏ x, Complex.exp ((Real.pi * α x * t x : ℝ) * Complex.I)

theorem phaseF_update (α : GBranch G.tree → ℝ) (X : GBranch G.tree → ℝ) (v : GBranch G.tree) (r : ℝ) :
    phaseF α (Function.update X v r) =
      phaseF α (Function.update X v 0) * Complex.exp ((Real.pi * α v * r : ℝ) * Complex.I) := by
  unfold phaseF
  rw [← Finset.mul_prod_erase univ _ (mem_univ v), ← Finset.mul_prod_erase univ _ (mem_univ v)]
  simp only [Function.update_self, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hx), Function.update_of_ne (Finset.ne_of_mem_erase hx)]

theorem norm_phaseF (α t : GBranch G.tree → ℝ) : ‖phaseF α t‖ = 1 := by
  unfold phaseF; rw [norm_prod]; exact Finset.prod_eq_one fun _ _ => Complex.norm_exp_ofReal_mul_I _

theorem continuous_phaseF (α : GBranch G.tree → ℝ) : Continuous (phaseF α) := by
  unfold phaseF
  refine continuous_finsetProd _ fun b _ => ?_
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_apply b))).mul continuous_const)

/-- **The one-dimensional integral** over a set squeezed between `(lo, hi)` and `[lo, hi]`. -/
theorem integral_slot (θ : ℝ) (hθ : θ ≠ 0) (A : Set ℝ) (lo hi : ℝ) (h1 : Ioo lo hi ⊆ A) (h2 : A ⊆ Icc lo hi) :
    (∫ r, A.indicator (fun r => Complex.exp ((θ * r : ℝ) * Complex.I)) r) =
      if lo < hi then (Complex.exp ((θ * hi : ℝ) * Complex.I) - Complex.exp ((θ * lo : ℝ) * Complex.I)) /
        ((θ : ℂ) * Complex.I) else 0 := by
  have hae : A.indicator (fun r => Complex.exp ((θ * r : ℝ) * Complex.I)) =ᵐ[volume]
      (Ioc lo hi).indicator (fun r => Complex.exp ((θ * r : ℝ) * Complex.I)) := by
    have hnull : volume ({lo, hi} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
    refine (measure_eq_zero_iff_ae_notMem.1 hnull).mono fun r hr => ?_
    have hr' : r ≠ lo ∧ r ≠ hi := by simpa [not_or] using hr
    by_cases hA : r ∈ A
    · have : r ∈ Ioc lo hi := ⟨lt_of_le_of_ne (h2 hA).1 (Ne.symm hr'.1), (h2 hA).2⟩
      rw [indicator_of_mem hA, indicator_of_mem this]
    · have : r ∉ Ioc lo hi := fun h => hA (h1 ⟨h.1, lt_of_le_of_ne h.2 hr'.2⟩)
      rw [indicator_of_notMem hA, indicator_of_notMem this]
  rw [integral_congr_ae hae, integral_indicator measurableSet_Ioc]
  split_ifs with h
  · rw [← intervalIntegral.integral_of_le h.le]
    have hc : ((θ : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hθ) Complex.I_ne_zero
    have e : ∀ r : ℝ, Complex.exp ((θ * r : ℝ) * Complex.I) = Complex.exp (((θ : ℂ) * Complex.I) * r) := by
      intro r; congr 1; push_cast; ring
    simp_rw [e]
    exact integral_exp_mul_complex hc
  · rw [Ioc_eq_empty h, Measure.restrict_empty, integral_zero_measure]

end WaveTurbulence.Flower.SelRes
