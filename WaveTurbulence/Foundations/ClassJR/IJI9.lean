/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IJI8

/-!
# DH21 Lemma 5.6: the nine terms of `I_{εα₁} 𝒥 I_{μ₁-εα₁}`

`kcomp_IJI_nine` writes the kernel of `I_{εα₁} 𝒥 I_{μ₁-εα₁}` (for a basic class `J` operator `𝒥`)
as the signed sum `aa + ab - ac + ba + bb - bc - ca - cb + cc` of the nine superpositions whose
coefficients are the symbols of `exists_piece_IJI_*` (DH21 L1047–L1053): it combines
`kcomp_IJI_eq` and `kcomp_sp_iker_split` with the layout changes `integral_prod_unitProd`,
`integral_assoc_prod` and the phase identity `J_{0; a + e, b - e} = J_{e; a, b}`. The variables
of the class `J` pieces are relabelled by `eIJI : (ι ⊕ Empty) ⊕ Unit ≃ Option ι`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

section Layout

variable {X Y Q : Type*} [MeasureSpace X] [MeasureSpace Y] [MeasureSpace Q]

theorem measurePreserving_unit_mk [SFinite (volume : Measure Q)] :
    MeasurePreserving (fun q : Q => ((), q)) := by
  refine ⟨measurable_prodMk_left, ?_⟩
  rw [Measure.volume_eq_prod (α := Unit), show (volume : Measure Unit) = Measure.dirac () from rfl,
    Measure.dirac_prod]

theorem integral_prod_unitProd [SFinite (volume : Measure X)] [SFinite (volume : Measure Q)]
    (F : X × (Unit × Q) → ℂ) : ∫ z, F z = ∫ p : X × Q, F (p.1, ((), p.2)) := by
  have h : MeasurePreserving (MeasurableEquiv.prodCongr (MeasurableEquiv.refl X)
      (MeasurableEquiv.punitProd (α := Q)).symm) :=
    (MeasurePreserving.id volume).prod measurePreserving_unit_mk
  exact (h.integral_comp' F).symm

theorem integral_assoc_prod [SFinite (volume : Measure Y)] [SFinite (volume : Measure Q)]
    (F : X × (Y × Q) → ℂ) : ∫ z, F z = ∫ p : (X × Y) × Q, F (p.1.1, (p.1.2, p.2)) :=
  ((volume_preserving_prodAssoc (α₁ := X) (β₁ := Y) (γ₁ := Q)).integral_comp' F).symm

end Layout

variable {ι : Type*}

/-- The relabelling `(ι ⊕ Empty) ⊕ Unit ≃ Option ι` (`α₁ = α none`). -/
@[expose] def eIJI : (ι ⊕ Empty) ⊕ Unit ≃ Option ι where
  toFun x := match x with
    | Sum.inl (Sum.inl i) => some i
    | Sum.inl (Sum.inr e) => e.elim
    | Sum.inr _ => none
  invFun y := match y with
    | some i => Sum.inl (Sum.inl i)
    | none => Sum.inr ()
  left_inv x := by rcases x with (i | e) | u <;> first | rfl | exact e.elim
  right_inv y := by rcases y with _ | i <;> rfl

theorem vA_eIJI (α : Option ι → ℝ) : vA (fun i => α (eIJI i)) = nsp α := rfl

theorem eIJI_inr (α : Option ι → ℝ) (u : Unit) : α (eIJI (Sum.inr u)) = α none := rfl

variable [Fintype ι]

theorem bundle_zero_fun {κ : Type*} [Fintype κ] (α : κ → ℝ) : bundle (0 : κ → ℤ) α = 0 := by
  simp [bundle]

section Terms

variable (R : JSym ι) (ε : ℤ) (α : Option ι → ℝ) (μ t s : ℝ)

theorem iji_aa_eq :
    (∫ z : (ℝ × ℝ) × (Unit × ((ℝ × ℝ) × (ℝ × ℝ))),
      tripleS R.m oneSym KIaa (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
        jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (fun i => α (eIJI i))) (z.2.2.1.1 + z.2.2.2.1)
          (z.1.1 + z.1.2 + μ - z.2.2.1.1 - z.2.2.2.1) t s) =
    ∫ p : ((ℝ × ℝ) × ℝ × ℝ) × ℝ × ℝ,
      R.m (nsp α) p.1.1 * kerM (formY (bundle R.y (nsp α)) (ε * α none) p.1.1) p.1.2 *
          kerM (formX (ε * α none) p.1.1 - p.1.2.1 - 0) p.2 *
        jker 0 (p.1.2.1 + p.2.1) (formX (ε * α none) p.1.1 - p.1.2.1 + (μ - ε * α none) - p.2.1)
          t s := by
  rw [integral_prod_unitProd, integral_assoc_prod]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KIaa, formsV_IJI_zero, formsV_IJI_one, vA_eIJI, eIJI_inr,
    bundle_zero_fun, formY, formX, sub_zero, jker]
  push_cast
  ring_nf

theorem iji_ab_eq :
    (∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
      tripleS R.m oneSym KIab (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
        jker (bundle (y3 (0 : ι → ℤ) (0 : Empty → ℤ) ε) (fun i => α (eIJI i))) (z.1.1 + z.1.2) μ
          t s) =
    ∫ z : (ℝ × ℝ) × ℝ × ℝ,
      R.m (nsp α) z.1 * kerM (formY (bundle R.y (nsp α)) (ε * α none) z.1) z.2 *
          phiR (formX (ε * α none) z.1 - z.2.1 - 0) *
        jker 0 (z.2.1 + (formX (ε * α none) z.1 - z.2.1)) (μ - ε * α none) t s := by
  rw [integral_prod_unitProd]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KIab, formsV_IJI_zero, formsV_IJI_one, vA_eIJI, eIJI_inr,
    bundle_y3, bundle_zero_fun, formY, formX, sub_zero, jker]
  push_cast
  ring_nf

theorem iji_ac_eq :
    (∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
      tripleS R.m oneSym KIab (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
        jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (fun i => α (eIJI i))) z.2.2.1
          (z.1.1 + z.1.2 + μ - z.2.2.1) t s) =
    ∫ z : (ℝ × ℝ) × ℝ × ℝ,
      R.m (nsp α) z.1 * kerM (formY (bundle R.y (nsp α)) (ε * α none) z.1) z.2 *
          phiR (formX (ε * α none) z.1 - z.2.1 - 0) *
        jker 0 z.2.1 (formX (ε * α none) z.1 - z.2.1 + (μ - ε * α none)) t s := by
  rw [integral_prod_unitProd]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KIab, formsV_IJI_zero, formsV_IJI_one, vA_eIJI, eIJI_inr,
    bundle_zero_fun, formY, formX, sub_zero, jker]
  push_cast
  ring_nf

theorem iji_ba_eq :
    (∫ z : ℝ × (ℝ × (ℝ × ℝ)), symR R.m R.y FV (nsp α) z *
      rker (bundle R.y (nsp α) + ε * α none) (bundle R.y (nsp α) + ε * α none)
        (z.1 + z.2.2.1) (z.2.1 + μ - z.2.2.1) z.1 t s) =
    ∫ p : (ℝ × ℝ) × ℝ × ℝ,
      R.m (nsp α) p.1 * phiR (formY (bundle R.y (nsp α)) (ε * α none) p.1) *
          kerM (p.1.2 - bundle R.y (nsp α)) p.2 *
        jker (bundle R.y (nsp α)) (ε * α none + p.1.1 + p.2.1) (p.1.2 + (μ - ε * α none) - p.2.1)
          t s := by
  rw [integral_assoc_prod]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [symR, FV, rker, phiR, formY, Prod.mk.eta, jker]
  push_cast
  ring_nf

theorem iji_bb_eq :
    (∫ z : ℝ × (ℝ × Unit), symR R.m R.y FVI (nsp α) z *
      rker (bundle R.y (nsp α) + ε * α none) (bundle (0 : ι → ℤ) (nsp α) + ε * α none)
        (z.1 + z.2.1) μ z.1 t s) =
    ∫ z : ℝ × ℝ,
      R.m (nsp α) z * phiR (formY (bundle R.y (nsp α)) (ε * α none) z) *
          phiR (z.2 - bundle R.y (nsp α)) *
        jker 0 (ε * α none + z.1 + z.2) (μ - ε * α none) t s := by
  rw [integral_assoc_prod, integral_prodUnit']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [symR, FVI, rker, phiR, formY, Prod.mk.eta, bundle_zero_fun, jker]
  push_cast
  ring_nf

theorem iji_bc_eq :
    (∫ z : ℝ × (ℝ × Unit), symR R.m R.y FVI (nsp α) z *
      rker (bundle R.y (nsp α) + ε * α none) (bundle R.y (nsp α) + ε * α none)
        z.1 (z.2.1 + μ) z.1 t s) =
    ∫ z : ℝ × ℝ,
      R.m (nsp α) z * phiR (formY (bundle R.y (nsp α)) (ε * α none) z) *
          phiR (z.2 - bundle R.y (nsp α)) *
        jker (bundle R.y (nsp α)) (ε * α none + z.1) (z.2 + (μ - ε * α none)) t s := by
  rw [integral_assoc_prod, integral_prodUnit']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [symR, FVI, rker, phiR, formY, Prod.mk.eta, jker]
  push_cast
  ring_nf

theorem iji_ca_eq :
    (∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
      tripleS R.m oneSym KIca (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
        jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (fun i => α (eIJI i))) z.2.2.1
          (z.1.1 + z.1.2 + μ - z.2.2.1) t s) =
    ∫ p : (ℝ × ℝ) × ℝ × ℝ,
      R.m (nsp α) p.1 * phiR (formY (bundle R.y (nsp α)) (ε * α none) p.1) *
          kerM (formX (ε * α none) p.1 - 0) p.2 *
        jker 0 (0 + p.2.1) (formX (ε * α none) p.1 + (μ - ε * α none) - p.2.1) t s := by
  rw [integral_prod_unitProd]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KIca, formsV_IJI_zero, formsV_IJI_one, vA_eIJI, eIJI_inr,
    bundle_zero_fun, formY, formX, sub_zero, zero_add, jker]
  push_cast
  ring_nf

theorem iji_cb_eq :
    (∫ z : (ℝ × ℝ) × (Unit × Unit),
      tripleS R.m oneSym KIcb (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
        jker (bundle (y3 (0 : ι → ℤ) (0 : Empty → ℤ) ε) (fun i => α (eIJI i))) (z.1.1 + z.1.2) μ
          t s) =
    ∫ z : ℝ × ℝ,
      R.m (nsp α) z * phiR (formY (bundle R.y (nsp α)) (ε * α none) z) *
          phiR (formX (ε * α none) z - 0) *
        jker 0 (0 + formX (ε * α none) z) (μ - ε * α none) t s := by
  rw [integral_prod_unitProd, integral_prodUnit']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KIcb, formsV_IJI_zero, formsV_IJI_one, vA_eIJI, eIJI_inr,
    bundle_y3, bundle_zero_fun, formY, formX, sub_zero, zero_add, jker]
  push_cast
  ring_nf

theorem iji_cc_eq :
    (∫ z : (ℝ × ℝ) × (Unit × Unit),
      tripleS R.m oneSym KIcb (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
        jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (fun i => α (eIJI i))) 0 (z.1.1 + z.1.2 + μ)
          t s) =
    ∫ z : ℝ × ℝ,
      R.m (nsp α) z * phiR (formY (bundle R.y (nsp α)) (ε * α none) z) *
          phiR (formX (ε * α none) z - 0) *
        jker 0 0 (formX (ε * α none) z + (μ - ε * α none)) t s := by
  rw [integral_prod_unitProd, integral_prodUnit']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KIcb, formsV_IJI_zero, formsV_IJI_one, vA_eIJI, eIJI_inr,
    bundle_zero_fun, formY, formX, sub_zero, jker]
  push_cast
  ring_nf

end Terms

/-- **The kernel of `I_{εα₁} 𝒥 I_{μ₁-εα₁}` as nine superpositions** (DH21 L1047–L1053), for a
basic class `J` operator `𝒥` in the variables `α ∘ some`; the class `J` terms are written in the
variables `α ∘ eIJI` of the pieces `exists_piece_IJI_*`. -/
theorem kcomp_IJI_nine {θ A N : ℝ} (R : JSym ι) (hR : R.Bound θ A N) (ε : ℤ)
    (α : Option ι → ℝ) (μ : ℝ) {t s : ℝ} (h0 : 0 ≤ t - s) (h1 : t - s ≤ 1) :
    kcomp (kcomp (iker (ε * α none)) (R.kernel (nsp α))) (iker (μ - ε * α none)) t s =
      (∫ z : (ℝ × ℝ) × (Unit × ((ℝ × ℝ) × (ℝ × ℝ))),
        tripleS R.m oneSym KIaa (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
          jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (fun i => α (eIJI i))) (z.2.2.1.1 + z.2.2.2.1)
            (z.1.1 + z.1.2 + μ - z.2.2.1.1 - z.2.2.2.1) t s) +
      (∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
        tripleS R.m oneSym KIab (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
          jker (bundle (y3 (0 : ι → ℤ) (0 : Empty → ℤ) ε) (fun i => α (eIJI i))) (z.1.1 + z.1.2) μ
            t s) -
      (∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
        tripleS R.m oneSym KIab (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
          jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (fun i => α (eIJI i))) z.2.2.1
            (z.1.1 + z.1.2 + μ - z.2.2.1) t s) +
      (∫ z : ℝ × (ℝ × (ℝ × ℝ)), symR R.m R.y FV (nsp α) z *
        rker (bundle R.y (nsp α) + ε * α none) (bundle R.y (nsp α) + ε * α none)
          (z.1 + z.2.2.1) (z.2.1 + μ - z.2.2.1) z.1 t s) +
      (∫ z : ℝ × (ℝ × Unit), symR R.m R.y FVI (nsp α) z *
        rker (bundle R.y (nsp α) + ε * α none) (bundle (0 : ι → ℤ) (nsp α) + ε * α none)
          (z.1 + z.2.1) μ z.1 t s) -
      (∫ z : ℝ × (ℝ × Unit), symR R.m R.y FVI (nsp α) z *
        rker (bundle R.y (nsp α) + ε * α none) (bundle R.y (nsp α) + ε * α none)
          z.1 (z.2.1 + μ) z.1 t s) -
      (∫ z : (ℝ × ℝ) × (Unit × (ℝ × ℝ)),
        tripleS R.m oneSym KIca (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
          jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (fun i => α (eIJI i))) z.2.2.1
            (z.1.1 + z.1.2 + μ - z.2.2.1) t s) -
      (∫ z : (ℝ × ℝ) × (Unit × Unit),
        tripleS R.m oneSym KIcb (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
          jker (bundle (y3 (0 : ι → ℤ) (0 : Empty → ℤ) ε) (fun i => α (eIJI i))) (z.1.1 + z.1.2) μ
            t s) +
      (∫ z : (ℝ × ℝ) × (Unit × Unit),
        tripleS R.m oneSym KIcb (LsIJI R ε) (csIJI _) (fun i => α (eIJI i)) z *
          jker (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (fun i => α (eIJI i))) 0 (z.1.1 + z.1.2 + μ)
            t s) := by
  have hva : Measurable fun w : (ℝ × ℝ) × (ℝ × ℝ) => formX (ε * α none) w.1 - w.2.1 :=
    ((measurable_formX _).comp measurable_fst).sub (measurable_fst.comp measurable_snd)
  have hub : Measurable fun γ : ℝ × ℝ => ε * α none + γ.1 := measurable_const.add measurable_fst
  have K := kcomp_IJI_eq R hR (ε * α none) (μ - ε * α none) (nsp α) h0 h1
  have T1 := kcomp_sp_iker_split (integrable_fa hR (nsp α) (bundle R.y (nsp α)) (ε * α none)) 0
    (u := fun w => w.2.1) (measurable_fst.comp measurable_snd) hva (μ - ε * α none) h0 h1
  have T2 := kcomp_sp_iker_split (integrable_fb hR (nsp α) (bundle R.y (nsp α)) (ε * α none))
    (bundle R.y (nsp α)) (v := fun γ => γ.2) hub measurable_snd (μ - ε * α none) h0 h1
  have T3 := kcomp_sp_iker_split (integrable_fb hR (nsp α) (bundle R.y (nsp α)) (ε * α none)) 0
    (u := fun _ => 0) (v := fun γ => formX (ε * α none) γ) measurable_const (measurable_formX _)
    (μ - ε * α none) h0 h1
  rw [K, T1, T2, T3, iji_aa_eq, iji_ab_eq, iji_ac_eq, iji_ba_eq, iji_bb_eq, iji_bc_eq, iji_ca_eq,
    iji_cb_eq, iji_cc_eq]
  ring

end WaveTurbulence.ClassJR
