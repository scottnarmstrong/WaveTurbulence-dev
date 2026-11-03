/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.IRI7

/-!
# DH21 Lemma 5.7: the nine terms of `I_{εα₁} ℛ I_{μ₁-εα₁}`

`kcomp_IRI_nine` writes the kernel of `I_{εα₁} ℛ I_{μ₁-εα₁}` (for a basic class `R` operator `ℛ`
with special variable `α₂`) as `aa + ab - ac + ba + bb - bc - ca - cb + cc`, with the symbols of
`exists_piece_IRI_*` (variables `α ∘ eIRI`) and `exists_piece_IRIR_*` (variables
`α ∘ some ∘ eIJI`). The variables are `α : Option (Option ι) → ℝ` with `α₁ = α none`,
`α₂ = α (some none)`.
-/

public section

open MeasureTheory Set Filter Finset Complex
open scoped ContDiff ENNReal Real

namespace WaveTurbulence.ClassJR

open WaveTurbulence.Fourier

attribute [local instance] isFiniteMeasure_volume_unit

variable {ι : Type*}

/-- The relabelling `(ι ⊕ Empty) ⊕ Fin 2 ≃ Option (Option ι)` (`inr 0 ↦ α₁`, `inr 1 ↦ α₂`). -/
@[expose] def eIRI : (ι ⊕ Empty) ⊕ Fin 2 ≃ Option (Option ι) where
  toFun x := Sum.elim (Sum.elim (fun i => some (some i)) fun e => e.elim) ![none, some none] x
  invFun y := match y with
    | none => Sum.inr 0
    | some none => Sum.inr 1
    | some (some i) => Sum.inl (Sum.inl i)
  left_inv x := by
    rcases x with (i | e) | r
    · rfl
    · exact e.elim
    · fin_cases r <;> rfl
  right_inv y := by rcases y with _ | _ | i <;> rfl

theorem vA_eIRI (α : Option (Option ι) → ℝ) : vA (fun i => α (eIRI i)) = nsp (nsp α) := rfl

theorem eIRI_zero (α : Option (Option ι) → ℝ) : α (eIRI (Sum.inr 0)) = α none := rfl

theorem eIRI_one (α : Option (Option ι) → ℝ) : α (eIRI (Sum.inr 1)) = nsp α none := rfl

theorem vA_nsp_eIJI (α : Option (Option ι) → ℝ) :
    vA (nsp fun o => α (Option.map eIJI o)) = nsp (nsp α) := rfl

theorem nsp_eIJI_inr (α : Option (Option ι) → ℝ) :
    (nsp fun o => α (Option.map eIJI o)) (Sum.inr ()) = nsp α none := rfl

variable [Fintype ι]

section Terms

variable (R : RSym ι) (ε : ℤ) (α : Option (Option ι) → ℝ) (μ t s : ℝ)

theorem iri_aa_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × ((ℝ × ℝ) × (ℝ × ℝ))),
      tripleS R.m oneSym KRaa (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
        jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) (fun i => α (eIRI i))) (z.2.2.1.1 + z.2.2.2.1)
          (z.1.1 + z.1.2.1 + μ - z.2.2.1.1 - z.2.2.2.1) t s) =
    ∫ p : ((ℝ × ℝ × ℝ) × ℝ × ℝ) × ℝ × ℝ,
      rcoef R (nsp α) p.1.1 * kerM ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + p.1.1.1 + (ε * α none)) p.1.2 *
          kerM (p.1.1.1 + p.1.1.2.1 + (ε * α none) - p.1.2.1 - 0) p.2 *
        jker 0 (p.1.2.1 + p.2.1) (p.1.1.1 + p.1.1.2.1 + (ε * α none) - p.1.2.1 + (μ - (ε * α none)) - p.2.1) t s := by
  rw [integral_prod_unitProd, integral_assoc_prod]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, prod3, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, vA_eIRI, eIRI_zero,
    eIRI_one, bundle_zero_fun, rcoef, sub_zero, jker, KRaa]
  push_cast
  ring_nf

theorem iri_ab_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
      tripleS R.m oneSym KRab (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
        jker (bundle (y4 (0 : ι → ℤ) (0 : Empty → ℤ) ε 0) (fun i => α (eIRI i))) (z.1.1 + z.1.2.1) μ t s) =
    ∫ z : (ℝ × ℝ × ℝ) × ℝ × ℝ,
      rcoef R (nsp α) z.1 * kerM ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + z.1.1 + (ε * α none)) z.2 *
          phiR (z.1.1 + z.1.2.1 + (ε * α none) - z.2.1 - 0) *
        jker 0 (z.2.1 + (z.1.1 + z.1.2.1 + (ε * α none) - z.2.1)) (μ - (ε * α none)) t s := by
  rw [integral_prod_unitProd]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, prod3, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, vA_eIRI, eIRI_zero,
    eIRI_one, bundle_zero_fun, bundle_y4, rcoef, sub_zero, zero_add, jker, KRab]
  push_cast
  ring_nf

theorem iri_ac_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
      tripleS R.m oneSym KRab (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
        jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) (fun i => α (eIRI i))) z.2.2.1
          (z.1.1 + z.1.2.1 + μ - z.2.2.1) t s) =
    ∫ z : (ℝ × ℝ × ℝ) × ℝ × ℝ,
      rcoef R (nsp α) z.1 * kerM ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + z.1.1 + (ε * α none)) z.2 *
          phiR (z.1.1 + z.1.2.1 + (ε * α none) - z.2.1 - 0) *
        jker 0 z.2.1 (z.1.1 + z.1.2.1 + (ε * α none) - z.2.1 + (μ - (ε * α none))) t s := by
  rw [integral_prod_unitProd]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, prod3, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, vA_eIRI, eIRI_zero,
    eIRI_one, bundle_zero_fun, rcoef, sub_zero, jker, KRab]
  push_cast
  ring_nf

theorem iri_ba_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
      tripleS R.m oneSym KRV (LsIRIR R) (csIRIR _) (nsp fun o => α (Option.map eIJI o)) z *
        rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
          (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
          (z.1.1 + z.2.2.1) (z.1.2.1 + μ - z.2.2.1) z.1.1 t s) =
    ∫ p : (ℝ × ℝ × ℝ) × ℝ × ℝ,
      rcoef R (nsp α) p.1 * phiR ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + p.1.1 + (ε * α none)) *
          kerM (p.1.2.1 - (bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none)) p.2 *
        jker (bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) ((ε * α none) + p.1.1 + p.2.1) (p.1.2.1 + (μ - (ε * α none)) - p.2.1) t s := by
  rw [integral_prod_unitProd]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KMR, formsV_IRIR_zero, formsV_IRIR_one, vA_nsp_eIJI,
    nsp_eIJI_inr, bundle_zero_fun, bundle_y3, rcoef, rker, phiR, jker, KRV]
  push_cast
  ring_nf

theorem iri_bb_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
      tripleS R.m oneSym KRVI (LsIRIR R) (csIRIR _) (nsp fun o => α (Option.map eIJI o)) z *
        rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
          (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
          (z.1.1 + z.1.2.1) μ z.1.1 t s) =
    ∫ z : ℝ × ℝ × ℝ,
      rcoef R (nsp α) z * phiR ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + z.1 + (ε * α none)) * phiR (z.2.1 - (bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none)) *
        jker 0 ((ε * α none) + z.1 + z.2.1) (μ - (ε * α none)) t s := by
  rw [integral_prod_unitProd, integral_prodUnit']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KPR, formsV_IRIR_zero, formsV_IRIR_one, vA_nsp_eIJI,
    nsp_eIJI_inr, bundle_zero_fun, bundle_y3, rcoef, rker, phiR, jker, KRVI]
  push_cast
  ring_nf

theorem iri_bc_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
      tripleS R.m oneSym KRVI (LsIRIR R) (csIRIR _) (nsp fun o => α (Option.map eIJI o)) z *
        rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
          (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
          z.1.1 (z.1.2.1 + μ) z.1.1 t s) =
    ∫ z : ℝ × ℝ × ℝ,
      rcoef R (nsp α) z * phiR ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + z.1 + (ε * α none)) * phiR (z.2.1 - (bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none)) *
        jker (bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) ((ε * α none) + z.1) (z.2.1 + (μ - (ε * α none))) t s := by
  rw [integral_prod_unitProd, integral_prodUnit']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, KPR, formsV_IRIR_zero, formsV_IRIR_one, vA_nsp_eIJI,
    nsp_eIJI_inr, bundle_zero_fun, bundle_y3, rcoef, rker, phiR, jker, KRVI]
  push_cast
  ring_nf

theorem iri_ca_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
      tripleS R.m oneSym KRca (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
        jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) (fun i => α (eIRI i))) z.2.2.1
          (z.1.1 + z.1.2.1 + μ - z.2.2.1) t s) =
    ∫ p : (ℝ × ℝ × ℝ) × ℝ × ℝ,
      rcoef R (nsp α) p.1 * phiR ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + p.1.1 + (ε * α none)) *
          kerM (p.1.1 + p.1.2.1 + (ε * α none) - 0) p.2 *
        jker 0 (0 + p.2.1) (p.1.1 + p.1.2.1 + (ε * α none) + (μ - (ε * α none)) - p.2.1) t s := by
  rw [integral_prod_unitProd]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, prod3, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, vA_eIRI, eIRI_zero,
    eIRI_one, bundle_zero_fun, rcoef, sub_zero, zero_add, jker, KRca]
  push_cast
  ring_nf

theorem iri_cb_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
      tripleS R.m oneSym KRcb (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
        jker (bundle (y4 (0 : ι → ℤ) (0 : Empty → ℤ) ε 0) (fun i => α (eIRI i))) (z.1.1 + z.1.2.1) μ t s) =
    ∫ z : ℝ × ℝ × ℝ,
      rcoef R (nsp α) z * phiR ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + z.1 + (ε * α none)) * phiR (z.1 + z.2.1 + (ε * α none) - 0) *
        jker 0 (0 + (z.1 + z.2.1 + (ε * α none))) (μ - (ε * α none)) t s := by
  rw [integral_prod_unitProd, integral_prodUnit']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, prod3, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, vA_eIRI, eIRI_zero,
    eIRI_one, bundle_zero_fun, bundle_y4, rcoef, sub_zero, zero_add, jker, KRcb]
  push_cast
  ring_nf

theorem iri_cc_eq :
    (∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
      tripleS R.m oneSym KRcb (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
        jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) (fun i => α (eIRI i))) 0 (z.1.1 + z.1.2.1 + μ) t s) =
    ∫ z : ℝ × ℝ × ℝ,
      rcoef R (nsp α) z * phiR ((bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none) + z.1 + (ε * α none)) * phiR (z.1 + z.2.1 + (ε * α none) - 0) *
        jker 0 0 (z.1 + z.2.1 + (ε * α none) + (μ - (ε * α none))) t s := by
  rw [integral_prod_unitProd, integral_prodUnit']
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [tripleS, oneSym, prod3, formsV_IRI_zero, formsV_IRI_one, formsV_IRI_two, vA_eIRI, eIRI_zero,
    eIRI_one, bundle_zero_fun, rcoef, sub_zero, jker, KRcb]
  push_cast
  ring_nf

end Terms

/-- **The kernel of `I_{εα₁} ℛ I_{μ₁-εα₁}` as nine superpositions** (DH21 L1063–L1072), for a
basic class `R` operator `ℛ` with special variable `α₂ = α (some none)`. -/
theorem kcomp_IRI_nine {θ A N : ℝ} (R : RSym ι) (hR : R.Bound θ A N) (ε : ℤ)
    (α : Option (Option ι) → ℝ) (μ : ℝ) {t s : ℝ} (h0 : 0 ≤ t - s) (h1 : t - s ≤ 1) :
    kcomp (kcomp (iker (ε * α none)) (R.kernel (nsp α))) (iker (μ - ε * α none)) t s =
      (∫ z : (ℝ × ℝ × ℝ) × (Unit × ((ℝ × ℝ) × (ℝ × ℝ))),
        tripleS R.m oneSym KRaa (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
          jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) (fun i => α (eIRI i))) (z.2.2.1.1 + z.2.2.2.1)
            (z.1.1 + z.1.2.1 + μ - z.2.2.1.1 - z.2.2.2.1) t s) + (∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
        tripleS R.m oneSym KRab (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
          jker (bundle (y4 (0 : ι → ℤ) (0 : Empty → ℤ) ε 0) (fun i => α (eIRI i))) (z.1.1 + z.1.2.1) μ t s) - (∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
        tripleS R.m oneSym KRab (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
          jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) (fun i => α (eIRI i))) z.2.2.1
            (z.1.1 + z.1.2.1 + μ - z.2.2.1) t s) + (∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
        tripleS R.m oneSym KRV (LsIRIR R) (csIRIR _) (nsp fun o => α (Option.map eIJI o)) z *
          rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
            (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
            (z.1.1 + z.2.2.1) (z.1.2.1 + μ - z.2.2.1) z.1.1 t s) + (∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
        tripleS R.m oneSym KRVI (LsIRIR R) (csIRIR _) (nsp fun o => α (Option.map eIJI o)) z *
          rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
            (bundle (0 : (ι ⊕ Empty) ⊕ Unit → ℤ) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
            (z.1.1 + z.1.2.1) μ z.1.1 t s) - (∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
        tripleS R.m oneSym KRVI (LsIRIR R) (csIRIR _) (nsp fun o => α (Option.map eIJI o)) z *
          rker (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
            (bundle (y3 R.y₂ (0 : Empty → ℤ) R.ε) (nsp fun o => α (Option.map eIJI o)) + ε * α none)
            z.1.1 (z.1.2.1 + μ) z.1.1 t s) - (∫ z : (ℝ × ℝ × ℝ) × (Unit × (ℝ × ℝ)),
        tripleS R.m oneSym KRca (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
          jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) (fun i => α (eIRI i))) z.2.2.1
            (z.1.1 + z.1.2.1 + μ - z.2.2.1) t s) -
      (∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
        tripleS R.m oneSym KRcb (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
          jker (bundle (y4 (0 : ι → ℤ) (0 : Empty → ℤ) ε 0) (fun i => α (eIRI i))) (z.1.1 + z.1.2.1) μ t s) + (∫ z : (ℝ × ℝ × ℝ) × (Unit × Unit),
        tripleS R.m oneSym KRcb (LsIRI R ε) (csIRI _) (fun i => α (eIRI i)) z *
          jker (bundle (0 : (ι ⊕ Empty) ⊕ Fin 2 → ℤ) (fun i => α (eIRI i))) 0 (z.1.1 + z.1.2.1 + μ) t s) := by
  have hg := integrable_rcoef hR (nsp α)
  have hX : Measurable fun γ : ℝ × ℝ × ℝ =>
      bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none + γ.1 + ε * α none :=
    (measurable_const.add measurable_fst).add measurable_const
  have hfa := integrable_mul_kerM hg hX (J := fun _ => (1 : ℂ)) aestronglyMeasurable_const
    (fun _ => by simp)
  have hfb := integrable_mul_phiR_gen hg hX (J := fun _ => (1 : ℂ)) aestronglyMeasurable_const
    (fun _ => by simp)
  simp only [mul_one] at hfa hfb
  have hva : Measurable fun p : (ℝ × ℝ × ℝ) × (ℝ × ℝ) => p.1.1 + p.1.2.1 + ε * α none - p.2.1 :=
    (((measurable_fst.comp measurable_fst).add
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).add measurable_const).sub
      (measurable_fst.comp measurable_snd)
  have K := kcomp_IRI_eq R hR (ε * α none) (μ - ε * α none) (nsp α) h0 h1
  have T1 := kcomp_sp_iker_split hfa 0 (u := fun p => p.2.1)
    (measurable_fst.comp measurable_snd) hva (μ - ε * α none) h0 h1
  have T2 := kcomp_sp_iker_split hfb (bundle R.y₂ (nsp (nsp α)) + R.ε * nsp α none)
    (u := fun γ => ε * α none + γ.1) (v := fun γ => γ.2.1)
    (measurable_const.add measurable_fst) (measurable_fst.comp measurable_snd)
    (μ - ε * α none) h0 h1
  have T3 := kcomp_sp_iker_split hfb 0 (u := fun _ => 0)
    (v := fun γ => γ.1 + γ.2.1 + ε * α none) measurable_const
    ((measurable_fst.add (measurable_fst.comp measurable_snd)).add measurable_const)
    (μ - ε * α none) h0 h1
  rw [K, T1, T2, T3, iri_aa_eq, iri_ab_eq, iri_ac_eq, iri_ba_eq, iri_bb_eq, iri_bc_eq, iri_ca_eq,
    iri_cb_eq, iri_cc_eq]
  ring

end WaveTurbulence.ClassJR
