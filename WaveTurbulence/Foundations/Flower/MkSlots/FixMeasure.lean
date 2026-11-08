/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! # B3s MK-SLOTS: pinned time integrals as product measures

A pinned time integral `∫ τ : {i // fix i = none} → ℝ, f (extendFix fix τ)` (the frozen `kDomainFix` kernels and the
world's `splicedTimeIntegralMK`) is the integral of `f` against the product measure `fixMeasure fix` with Lebesgue
factors at the free coordinates and Dirac factors at the pinned values. Every time split of the Stage-1 chain is a
coordinate relabeling (`piCongrLeft`, `sumPiEquivProdPi`, `piCurry`), and these preserve `fixMeasure` exactly as they
preserve `volume`. So main's pointwise integrand identities transfer to pinned integrals with one change of measure.

* `fixFactor`, `fixMeasure`, `extendFixI`;
* `integral_fixMeasure`: `∫ f ∂(fixMeasure fix) = ∫ τ, f (extendFixI fix τ)`;
* `fixMeasure_none`: no pins gives `volume`;
* `measurePreserving_piCongrLeft_fix`, `measurePreserving_sumPiEquivProdPi_fix`: relabelings. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace WaveTurbulence.Flower.MkSlots

/-- One time coordinate: Lebesgue measure when free, the Dirac mass at the pinned value otherwise. -/
def fixFactor (o : Option ℝ) : Measure ℝ := o.elim volume fun v => Measure.dirac v

instance fixFactor_sigmaFinite (o : Option ℝ) : SigmaFinite (fixFactor o) := by
  cases o <;> simp only [fixFactor, Option.elim] <;> infer_instance

variable {ι : Type*} [Fintype ι]


/-- The pinned product measure on time vectors. -/
def fixMeasure (fix : ι → Option ℝ) : Measure (ι → ℝ) := Measure.pi fun i => fixFactor (fix i)

instance fixMeasure_sigmaFinite (fix : ι → Option ℝ) : SigmaFinite (fixMeasure fix) := by
  unfold fixMeasure; infer_instance

/-- The full time vector of free times `τ` and pinned values `fix` (the index-generic `Garden.extendFix`). -/
def extendFixI (fix : ι → Option ℝ) (τ : {i // fix i = none} → ℝ) : ι → ℝ :=
  fun i => match h : fix i with
    | some v => v
    | none => τ ⟨i, h⟩

omit [Fintype ι] in
theorem extendFixI_some (fix : ι → Option ℝ) (τ : {i // fix i = none} → ℝ) {i : ι} {v : ℝ} (h : fix i = some v) :
    extendFixI fix τ i = v := by
  unfold extendFixI
  split
  · next v' h' => rw [h] at h'; exact (Option.some.inj h').symm
  · next h' => rw [h] at h'; exact absurd h' (by simp)

omit [Fintype ι] in
theorem extendFixI_none (fix : ι → Option ℝ) (τ : {i // fix i = none} → ℝ) {i : ι} (h : fix i = none) :
    extendFixI fix τ i = τ ⟨i, h⟩ := by
  unfold extendFixI
  split
  · next v' h' => rw [h] at h'; exact absurd h' (by simp)
  · rfl

theorem fixMeasure_none : fixMeasure (fun _ : ι => (none : Option ℝ)) = volume := by
  unfold fixMeasure fixFactor
  rfl

/-- The pinned values as a function on the pinned coordinates. -/
def pinVal (fix : ι → Option ℝ) : {i // ¬ fix i = none} → ℝ := fun i => (fix i.1).getD 0

/-- A product of Dirac masses is the Dirac mass of the product point. -/
theorem pi_dirac {κ : Type*} [Fintype κ] (x : κ → ℝ) :
    Measure.pi (fun i : κ => (Measure.dirac (x i) : Measure ℝ)) = Measure.dirac x := by
  classical
  refine (Measure.pi_eq (μ := fun i : κ => (Measure.dirac (x i) : Measure ℝ)) fun s hs => ?_)
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [Measure.dirac_apply' _ (hs _)]
  by_cases hx : x ∈ Set.pi Set.univ s
  · rw [Set.indicator_of_mem hx]
    simp only [Pi.one_apply]
    refine (Finset.prod_eq_one fun i _ => ?_).symm
    rw [Set.indicator_of_mem (hx i (Set.mem_univ i))]
    rfl
  · rw [Set.indicator_of_notMem hx]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hx
    obtain ⟨i, hi⟩ := hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem fixMeasure_pinned_eq (fix : ι → Option ℝ) :
    (Measure.pi fun i : {i // ¬ fix i = none} => fixFactor (fix i.1)) = Measure.dirac (pinVal fix) := by
  rw [← pi_dirac]
  congr 1
  funext i
  obtain ⟨i, hi⟩ := i
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hi
  simp [fixFactor, pinVal, hv]

theorem fixMeasure_free_eq (fix : ι → Option ℝ) :
    (Measure.pi fun i : {i // fix i = none} => fixFactor (fix i.1)) = volume := by
  have : (fun i : {i // fix i = none} => fixFactor (fix i.1)) = fun _ => (volume : Measure ℝ) := by
    funext i
    simp [fixFactor, i.2]
  rw [this]
  rfl

/-- **The pinned integral is the `fixMeasure` integral.** -/
theorem integral_fixMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (fix : ι → Option ℝ)
    (f : (ι → ℝ) → E) :
    ∫ τ, f τ ∂(fixMeasure fix) = ∫ τ : {i // fix i = none} → ℝ, f (extendFixI fix τ) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun i => fix i = none)
  have hmp : MeasurePreserving e (fixMeasure fix)
      ((Measure.pi fun i : {i // fix i = none} => fixFactor (fix i.1)).prod
        (Measure.pi fun i : {i // ¬ fix i = none} => fixFactor (fix i.1))) :=
    measurePreserving_piEquivPiSubtypeProd (fun i => fixFactor (fix i)) (fun i => fix i = none)
  rw [fixMeasure_free_eq, fixMeasure_pinned_eq, Measure.prod_dirac] at hmp
  rw [← hmp.symm.integral_comp' f]
  have hemb : MeasurableEmbedding (fun x : {i // fix i = none} → ℝ => (x, pinVal fix)) :=
    measurableEmbedding_prod_mk_right (pinVal fix)
  rw [hemb.integral_map]
  refine integral_congr_ae (ae_of_all _ fun τ => ?_)
  show f (e.symm (τ, pinVal fix)) = f (extendFixI fix τ)
  congr 1
  funext i
  by_cases hi : fix i = none
  · rw [extendFixI_none fix τ hi]
    show (if h : fix i = none then τ ⟨i, h⟩ else pinVal fix ⟨i, h⟩) = τ ⟨i, hi⟩
    rw [dif_pos hi]
  · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hi
    rw [extendFixI_some fix τ hv]
    show (if h : fix i = none then τ ⟨i, h⟩ else pinVal fix ⟨i, h⟩) = v
    rw [dif_neg hi]
    simp [pinVal, hv]

/-- Relabeling the coordinates transports the pins. -/
theorem measurePreserving_piCongrLeft_fix {ι' : Type*} [Fintype ι'] (e : ι' ≃ ι) (fix : ι → Option ℝ) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) (fixMeasure (fix ∘ e)) (fixMeasure fix) :=
  measurePreserving_piCongrLeft (fun i => fixFactor (fix i)) e

/-- Splitting the coordinates along a sum transports the pins. -/
theorem measurePreserving_sumPiEquivProdPi_fix {ι' : Type*} [Fintype ι'] (fix : ι ⊕ ι' → Option ℝ) :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι' => ℝ)) (fixMeasure fix)
      ((fixMeasure (fix ∘ Sum.inl)).prod (fixMeasure (fix ∘ Sum.inr))) :=
  measurePreserving_sumPiEquivProdPi (fun i => fixFactor (fix i))

omit [Fintype ι] in
/-- Currying a sigma-indexed family of times transports the pins blockwise. -/
theorem measurePreserving_piCurry_fix {α : Type*} [Fintype α] (κ : α → Type*) [∀ i, Fintype (κ i)]
    (fix : (Σ i, κ i) → Option ℝ) :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (i : α) (_ : κ i) => ℝ)) (fixMeasure fix)
      (Measure.pi fun i => fixMeasure (fun j : κ i => fix ⟨i, j⟩)) := by
  let e := MeasurableEquiv.piCurry (fun (i : α) (_ : κ i) => ℝ)
  apply MeasurePreserving.symm e.symm
  refine ⟨e.symm.measurable, ?_⟩
  apply (Measure.pi_eq (μ := fun z : (Σ i, κ i) => fixFactor (fix z)) ?_).symm
  intro s _hs
  have hp : e.symm ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => s ⟨i, j⟩)) := by
    ext x
    change (∀ z : (Σ i, κ i), z ∈ Set.univ → x z.1 z.2 ∈ s z) ↔
      ∀ i, i ∈ Set.univ → ∀ j, j ∈ Set.univ → x i j ∈ s ⟨i, j⟩
    simp only [Set.mem_univ, forall_const]
    exact ⟨fun h i j => h ⟨i, j⟩, fun h ⟨i, j⟩ => h i j⟩
  rw [e.symm.map_apply, hp, Measure.pi_pi]
  simp_rw [fixMeasure, Measure.pi_pi]
  exact (Fintype.prod_sigma (fun z : (Σ i, κ i) => fixFactor (fix z) (s z))).symm

end WaveTurbulence.Flower.MkSlots
