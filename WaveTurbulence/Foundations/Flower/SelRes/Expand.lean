/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.SelRes.Face
public import WaveTurbulence.Foundations.Flower.FinalMKFine.Kernel

/-! # D7 SEL-RES / Expand: the selected-atom gain at the kernel level (o73 Prop 20.1, low part)

- `kernel_eq_sum`: the marked kernel of modified data (`modData`: new pins, indicator times `g`) as a finite sum of
  amplitudes times pinned time transforms (C4b's `splicedKernelMK_eq`).
- `inv_selFreq_split`: on `|θ| ≥ λ`, `(iθ)⁻¹ = (−i/λ)(g₊ − g₋)` with `g± ∈ [0,1]` local to the selected atom.
- `expand_one`: if the selected frequency is at least `λ` on the support, the kernel is at most `12/λ` times any
  bound for the one-step pinned modifications (FL-FACE's faces in pinned form, `face_expand`).
- `ModOK`, `expand_bound_atom`, `expand_bound`: several selected atoms, one per tree, by induction: `∏_{v∈S} 12/λ_v`
  (`(12/λ)^{#S}` at a constant `λ`) times any bound for the modifications `ModOK S` (pins at `S` and `≤ #S`
  recipients, indicator times a `[0,1]` function local to `S`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence.Flower.FlFace (fixSel children parents IsChildOf.ne card_parents_le_one card_children_le_three)

variable {w d : ℕ} {G : Garden w}

/-- Modified data: new pins `fix'`, indicator multiplied by `g`. -/
def modData (D : SplicedKernelDataMK G d) (fix' : GBranch G.tree → Option ℝ) (g : (GNode G.tree → Mom d) → ℝ) :
    SplicedKernelDataMK G d :=
  { D with fix := fix', ind := fun k => D.ind k * g k }

theorem ampMK_modData (D : SplicedKernelDataMK G d) (fix' : GBranch G.tree → Option ℝ)
    (g : (GNode G.tree → Mom d) → ℝ) (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    ampMK G (modData D fix' g) L γ η base z = ampMK G D L γ η base z * (g (cosetDecoration G L base z) : ℂ) := by
  unfold ampMK SplicedKernelDataMK.atomW modData
  push_cast
  ring

/-- The marked kernel as a finite sum of amplitudes times pinned time transforms (C4b's `splicedKernelMK_eq`). -/
theorem kernel_eq_sum (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (fix' : GBranch G.tree → Option ℝ) (g : (GNode G.tree → Mom d) → ℝ) :
    splicedKernelMK G (modData D fix' g) L γ η δ base roots =
      (coupling d L γ δ : ℂ) ^ G.order *
        ∑ z ∈ (CoarseSpliced.finite_momAmp_support G hP D.toSplicedKernelData hD hL γ η base roots).toFinset,
          ampMK G D L γ η base z.1 * (g (cosetDecoration G L base z.1) : ℂ) *
            splicedFourierBMK G D.layer D.rootTime fix' (splicedFrequency G D.toSplicedKernelData L γ δ base z.1) := by
  rw [splicedKernelMK_eq]
  congr 1
  rw [tsum_eq_sum]
  · refine Finset.sum_congr rfl fun z _ => ?_
    rw [ampMK_modData]; rfl
  · intro z hz
    have : splicedMomentumAmplitude G D.toSplicedKernelData L γ η base z.1 = 0 := by
      by_contra h; exact hz ((Set.Finite.mem_toFinset _).2 h)
    have h0 : ampMK G (modData D fix' g) L γ η base z.1 = 0 := by
      unfold ampMK; rw [show (modData D fix' g).toSplicedKernelData = D.toSplicedKernelData from rfl, this, mul_zero]
    rw [h0, zero_mul]

theorem modData_self (D : SplicedKernelDataMK G d) : modData D D.fix (fun _ => 1) = D := by
  cases D; simp [modData]

/-- The selected frequency as a function of the decoration (local at `v`). -/
def selFreq (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) (k : GNode G.tree → Mom d) : ℝ :=
  Real.pi * ((((G.sign v.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) * omegaNode G k v + D.frequency v)

theorem selFreq_coset (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (base : Mom d) (v : GBranch G.tree)
    (z : GNode G.tree → (Fin d → ℤ)) :
    selFreq D L γ δ v (cosetDecoration G L base z) =
      Real.pi * splicedFrequency G D.toSplicedKernelData L γ δ base z v := rfl

/-- The sign-split normalized reciprocal of the selected frequency. -/
def gPlus (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) (lam : ℝ) (k : GNode G.tree → Mom d) : ℝ :=
  if 0 < selFreq D L γ δ v k then min 1 (lam / |selFreq D L γ δ v k|) else 0
def gMinus (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) (lam : ℝ) (k : GNode G.tree → Mom d) : ℝ :=
  if selFreq D L γ δ v k < 0 then min 1 (lam / |selFreq D L γ δ v k|) else 0

theorem gPlus_mem (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) {lam : ℝ} (hlam : 0 ≤ lam)
    (k : GNode G.tree → Mom d) : 0 ≤ gPlus D L γ δ v lam k ∧ gPlus D L γ δ v lam k ≤ 1 := by
  unfold gPlus; split_ifs
  · exact ⟨le_min zero_le_one (div_nonneg hlam (abs_nonneg _)), min_le_left _ _⟩
  · exact ⟨le_rfl, zero_le_one⟩
theorem gMinus_mem (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) {lam : ℝ} (hlam : 0 ≤ lam)
    (k : GNode G.tree → Mom d) : 0 ≤ gMinus D L γ δ v lam k ∧ gMinus D L γ δ v lam k ≤ 1 := by
  unfold gMinus; split_ifs
  · exact ⟨le_min zero_le_one (div_nonneg hlam (abs_nonneg _)), min_le_left _ _⟩
  · exact ⟨le_rfl, zero_le_one⟩

/-- `selFreq` reads the decoration only at `v` and its children. -/
theorem selFreq_local (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) (k k' : GNode G.tree → Mom d)
    (h : (∀ i : Fin 3, k (v.child i) = k' (v.child i)) ∧ k v.toNode = k' v.toNode) :
    selFreq D L γ δ v k = selFreq D L γ δ v k' := by
  unfold selFreq omegaNode
  rw [h.1 0, h.1 1, h.1 2, h.2]

theorem gPlus_local (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) (lam : ℝ)
    (k k' : GNode G.tree → Mom d) (h : (∀ i : Fin 3, k (v.child i) = k' (v.child i)) ∧ k v.toNode = k' v.toNode) :
    gPlus D L γ δ v lam k = gPlus D L γ δ v lam k' := by
  unfold gPlus; rw [selFreq_local D L γ δ v k k' h]
theorem gMinus_local (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) (lam : ℝ)
    (k k' : GNode G.tree → Mom d) (h : (∀ i : Fin 3, k (v.child i) = k' (v.child i)) ∧ k v.toNode = k' v.toNode) :
    gMinus D L γ δ v lam k = gMinus D L γ δ v lam k' := by
  unfold gMinus; rw [selFreq_local D L γ δ v k k' h]

/-- On `|θ| ≥ λ > 0`, `(iθ)⁻¹ = (−i/λ)(g₊ − g₋)`. -/
theorem inv_selFreq_split (D : SplicedKernelDataMK G d) (L γ δ : ℝ) (v : GBranch G.tree) {lam : ℝ}
    (hlam : 0 < lam) (k : GNode G.tree → Mom d) (h : lam ≤ |selFreq D L γ δ v k|) :
    (((selFreq D L γ δ v k : ℝ) : ℂ) * Complex.I)⁻¹ =
      (-Complex.I / (lam : ℂ)) * ((gPlus D L γ δ v lam k : ℂ) - (gMinus D L γ δ v lam k : ℂ)) := by
  set θ := selFreq D L γ δ v k with hθ
  have hθ0 : θ ≠ 0 := fun h0 => by rw [h0, abs_zero] at h; linarith
  have hmin : min 1 (lam / |θ|) = lam / |θ| := min_eq_right ((div_le_one (abs_pos.2 hθ0)).2 h)
  have hdiff : (gPlus D L γ δ v lam k : ℝ) - gMinus D L γ δ v lam k = lam / θ := by
    unfold gPlus gMinus
    rw [← hθ]
    rcases lt_or_gt_of_ne hθ0 with hn | hp
    · rw [ite_eq_right (not_lt.2 hn.le), ite_eq_left hn, hmin, abs_of_neg hn]
      have : -θ ≠ 0 := by linarith
      field_simp
      ring
    · rw [ite_eq_left hp, ite_eq_right (not_lt.2 hp.le), hmin, abs_of_pos hp]; ring
  have hc : ((gPlus D L γ δ v lam k : ℂ) - (gMinus D L γ δ v lam k : ℂ)) = ((lam / θ : ℝ) : ℂ) := by
    rw [← hdiff]; push_cast; ring
  rw [hc]
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have ht : (θ : ℂ) ≠ 0 := by exact_mod_cast hθ0
  rw [mul_inv, Complex.inv_I]
  push_cast
  field_simp

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence.Flower.FlFace (fixSel children parents IsChildOf.ne card_parents_le_one card_children_le_three)

variable {w d : ℕ} {G : Garden w}

theorem pin_pin_self (fix : GBranch G.tree → Option ℝ) (v : GBranch G.tree) (r : ℝ) :
    pin (pin fix v r) v r = pin fix v r := Function.update_idem _ _ _

/-- An integral over a subset of a unit interval of a function bounded by `B` there. -/
theorem norm_integral_indicator_le (I : Set ℝ) (a : ℝ) (hI : I ⊆ Icc a (a + 1)) (F : ℝ → ℂ) (B : ℝ)
    (hB0 : 0 ≤ B) (hF : ∀ r ∈ I, ‖F r‖ ≤ B) : ‖∫ r, I.indicator F r‖ ≤ B := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have hint : Integrable ((Icc a (a + 1)).indicator fun _ : ℝ => B) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun r => norm_nonneg _) hint
    (Filter.Eventually.of_forall fun r => ?_)).trans ?_
  · show ‖I.indicator F r‖ ≤ _
    by_cases hr : r ∈ I
    · rw [indicator_of_mem hr, indicator_of_mem (hI hr)]; exact hF r hr
    · rw [indicator_of_notMem hr, norm_zero]; exact indicator_nonneg (fun _ _ => hB0) r
  · rw [integral_indicator_const _ measurableSet_Icc]
    simp

theorem Iup_subset (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (v u : GBranch G.tree) : Iup layer rootTime fix v u ⊆ Icc (layer u : ℝ) (layer u + 1) :=
  fun _ hr => ⟨hr.2.2.1, hr.2.2.2.1⟩
theorem Ilo_subset (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (v c : GBranch G.tree) : Ilo layer rootTime fix v c ⊆ Icc (layer c : ℝ) (layer c + 1) :=
  fun _ hr => ⟨hr.2.2.1, hr.2.2.2.1⟩

/-- A face integral, summed against amplitudes: the sum and the face integral commute. -/
theorem sum_face_integral {Z : Type*} (s : Finset Z) (a : Z → ℂ) (I : Set ℝ) (B : Z → ℝ → ℂ)
    (hB : ∀ z ∈ s, Integrable fun r => I.indicator (B z) r) (c : ℂ) :
    c * ∑ z ∈ s, a z * ∫ r, I.indicator (B z) r = ∫ r, I.indicator (fun r => c * ∑ z ∈ s, a z * B z r) r := by
  have h1 : ∑ z ∈ s, a z * ∫ r, I.indicator (B z) r = ∫ r, ∑ z ∈ s, a z * I.indicator (B z) r := by
    rw [integral_finsetSum _ fun z hz => (hB z hz).const_mul (a z)]
    exact Finset.sum_congr rfl fun z _ => (integral_const_mul _ _).symm
  rw [h1, ← integral_const_mul]
  congr 1; funext r
  by_cases hr : r ∈ I
  · simp only [indicator_of_mem hr]
  · simp only [indicator_of_notMem hr, mul_zero, Finset.sum_const_zero]

theorem alg_faces {Z U C : Type*} (s : Finset Z) (Us : Finset U) (Cs : Finset C) (c : ℂ) (A T Fl : Z → ℂ)
    (P : U → Z → ℂ) (Q : C → Z → ℂ) :
    c * ∑ z ∈ s, A z * ((T z + ∑ u ∈ Us, P u z) - (Fl z + ∑ x ∈ Cs, Q x z)) =
      (c * ∑ z ∈ s, A z * T z + ∑ u ∈ Us, c * ∑ z ∈ s, A z * P u z) -
        (c * ∑ z ∈ s, A z * Fl z + ∑ x ∈ Cs, c * ∑ z ∈ s, A z * Q x z) := by
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  rw [Finset.sum_comm (s := s) (t := Us), Finset.sum_comm (s := s) (t := Cs)]

/-- The face bracket of `face_expand` at the frequency `α`. -/
def facesB (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (v : GBranch G.tree) (α : GBranch G.tree → ℝ) : ℂ :=
  ((if cfl layer fix v < ctop layer rootTime fix v then
        splicedFourierBMK G layer rootTime (pin fix v (ctop layer rootTime fix v)) α else 0) +
      ∑ u ∈ Uf fix v, ∫ r, (Iup layer rootTime fix v u).indicator
        (fun r => splicedFourierBMK G layer rootTime (pin (pin fix v r) u r) α) r) -
    ((if cfl layer fix v < ctop layer rootTime fix v then
        splicedFourierBMK G layer rootTime (pin fix v (cfl layer fix v)) α else 0) +
      ∑ c ∈ Cf fix v, ∫ r, (Ilo layer rootTime fix v c).indicator
        (fun r => splicedFourierBMK G layer rootTime (pin (pin fix v r) c r) α) r)

/-- The same bracket for the modified kernels. -/
def facesK (D : SplicedKernelDataMK G d) (v : GBranch G.tree) (g : (GNode G.tree → Mom d) → ℝ) (L γ η δ : ℝ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) : ℂ :=
  ((if cfl D.layer D.fix v < ctop D.layer D.rootTime D.fix v then
        splicedKernelMK G (modData D (pin D.fix v (ctop D.layer D.rootTime D.fix v)) g) L γ η δ base roots else 0) +
      ∑ u ∈ Uf D.fix v, ∫ r, (Iup D.layer D.rootTime D.fix v u).indicator
        (fun r => splicedKernelMK G (modData D (pin (pin D.fix v r) u r) g) L γ η δ base roots) r) -
    ((if cfl D.layer D.fix v < ctop D.layer D.rootTime D.fix v then
        splicedKernelMK G (modData D (pin D.fix v (cfl D.layer D.fix v)) g) L γ η δ base roots else 0) +
      ∑ c ∈ Cf D.fix v, ∫ r, (Ilo D.layer D.rootTime D.fix v c).indicator
        (fun r => splicedKernelMK G (modData D (pin (pin D.fix v r) c r) g) L γ η δ base roots) r)

theorem face_expand' (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ) (fix : GBranch G.tree → Option ℝ)
    (v : GBranch G.tree) (hv : fix v = none) (α : GBranch G.tree → ℝ) (hα : Real.pi * α v ≠ 0) :
    splicedFourierBMK G layer rootTime fix α =
      (((Real.pi * α v : ℝ) : ℂ) * Complex.I)⁻¹ * facesB layer rootTime fix v α :=
  face_expand fix v hv α hα

/-- Summing the faces against the modified amplitudes gives the modified kernels. -/
theorem faces_sum (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (v : GBranch G.tree) (hv : D.fix v = none) (g : (GNode G.tree → Mom d) → ℝ) :
    (coupling d L γ δ : ℂ) ^ G.order *
        ∑ z ∈ (CoarseSpliced.finite_momAmp_support G hP D.toSplicedKernelData hD hL γ η base roots).toFinset,
          (ampMK G D L γ η base z.1 * (g (cosetDecoration G L base z.1) : ℂ)) *
            facesB D.layer D.rootTime D.fix v (splicedFrequency G D.toSplicedKernelData L γ δ base z.1) =
      facesK D v g L γ η δ base roots := by
  unfold facesB facesK
  rw [alg_faces]
  simp only [kernel_eq_sum hP D hD hL γ η δ base roots]
  congr 1
  · congr 1
    · split_ifs <;> simp [mul_assoc]
    · refine Finset.sum_congr rfl fun u hu => ?_
      rw [sum_face_integral _ _ _ _ (fun z _ => integrable_parFace (layer := D.layer) (rootTime := D.rootTime)
        D.fix v hv _ hu)]
  · congr 1
    · split_ifs <;> simp [mul_assoc]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [sum_face_integral _ _ _ _ (fun z _ => integrable_chFace (layer := D.layer) (rootTime := D.rootTime)
        D.fix v hv _ hx)]

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence.Flower.FlFace (fixSel children parents IsChildOf.ne card_parents_le_one card_children_le_three)

variable {w d : ℕ} {G : Garden w}

/-- The hypothesis of `expand_one`: a bound for every one-step pinned modification. -/
def OneStepBound (D : SplicedKernelDataMK G d) (v : GBranch G.tree) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (Bnd : ℝ) : Prop :=
  ∀ (y : GBranch G.tree) (r : ℝ) (g : (GNode G.tree → Mom d) → ℝ), (∀ k, 0 ≤ g k ∧ g k ≤ 1) →
    (∀ k k', ((∀ i : Fin 3, k (v.child i) = k' (v.child i)) ∧ k v.toNode = k' v.toNode) → g k = g k') →
    (y = v ∨ (D.fix y = none ∧ (y.IsChildOf v ∨ v.IsChildOf y))) →
    ((D.layer v : ℝ) ≤ r ∧ r ≤ D.layer v + 1) → ((D.layer y : ℝ) ≤ r ∧ r ≤ D.layer y + 1) →
    ‖splicedKernelMK G (modData D (pin (pin D.fix v r) y r) g) L γ η δ base roots‖ ≤ Bnd

theorem norm_facesK_le (D : SplicedKernelDataMK G d) (v : GBranch G.tree) (g : (GNode G.tree → Mom d) → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hgl : ∀ k k', ((∀ i : Fin 3, k (v.child i) = k' (v.child i)) ∧ k v.toNode = k' v.toNode) → g k = g k')
    {L : ℝ} (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (Bnd : ℝ) (hB0 : 0 ≤ Bnd)
    (hB : OneStepBound D v L γ η δ base roots Bnd) : ‖facesK D v g L γ η δ base roots‖ ≤ 6 * Bnd := by
  have htop : ‖(if cfl D.layer D.fix v < ctop D.layer D.rootTime D.fix v then
      splicedKernelMK G (modData D (pin D.fix v (ctop D.layer D.rootTime D.fix v)) g) L γ η δ base roots
      else 0)‖ ≤ Bnd := by
    split_ifs with h
    · have := hB v (ctop D.layer D.rootTime D.fix v) g hg hgl (Or.inl rfl)
        ⟨(layer_le_cfl).trans h.le, ctop_le_ceil⟩ ⟨(layer_le_cfl).trans h.le, ctop_le_ceil⟩
      rwa [pin_pin_self] at this
    · simpa using hB0
  have hfl : ‖(if cfl D.layer D.fix v < ctop D.layer D.rootTime D.fix v then
      splicedKernelMK G (modData D (pin D.fix v (cfl D.layer D.fix v)) g) L γ η δ base roots
      else 0)‖ ≤ Bnd := by
    split_ifs with h
    · have := hB v (cfl D.layer D.fix v) g hg hgl (Or.inl rfl)
        ⟨layer_le_cfl, h.le.trans ctop_le_ceil⟩ ⟨layer_le_cfl, h.le.trans ctop_le_ceil⟩
      rwa [pin_pin_self] at this
    · simpa using hB0
  have hpar : ∀ u ∈ Uf D.fix v, ‖∫ r, (Iup D.layer D.rootTime D.fix v u).indicator
      (fun r => splicedKernelMK G (modData D (pin (pin D.fix v r) u r) g) L γ η δ base roots) r‖ ≤ Bnd := by
    intro u hu
    obtain ⟨hvu, hfu⟩ := mem_Uf.1 hu
    refine norm_integral_indicator_le _ _ (Iup_subset _ _ _ v u) _ Bnd hB0 fun r hr => ?_
    exact hB u r g hg hgl (Or.inr ⟨hfu, Or.inr hvu⟩) ⟨layer_le_cfl.trans hr.1.le, hr.2.1.le.trans ctop_le_ceil⟩
      ⟨hr.2.2.1, hr.2.2.2.1⟩
  have hch : ∀ c ∈ Cf D.fix v, ‖∫ r, (Ilo D.layer D.rootTime D.fix v c).indicator
      (fun r => splicedKernelMK G (modData D (pin (pin D.fix v r) c r) g) L γ η δ base roots) r‖ ≤ Bnd := by
    intro c hc
    obtain ⟨hcv, hfc⟩ := mem_Cf.1 hc
    refine norm_integral_indicator_le _ _ (Ilo_subset _ _ _ v c) _ Bnd hB0 fun r hr => ?_
    exact hB c r g hg hgl (Or.inr ⟨hfc, Or.inl hcv⟩) ⟨layer_le_cfl.trans hr.1.le, hr.2.1.le.trans ctop_le_ceil⟩
      ⟨hr.2.2.1, hr.2.2.2.1⟩
  have hU : (Uf D.fix v).card ≤ 1 := (Finset.card_filter_le _ _).trans (card_parents_le_one v)
  have hC : (Cf D.fix v).card ≤ 3 := (Finset.card_filter_le _ _).trans (card_children_le_three v)
  have hsU : ‖∑ u ∈ Uf D.fix v, ∫ r, (Iup D.layer D.rootTime D.fix v u).indicator
      (fun r => splicedKernelMK G (modData D (pin (pin D.fix v r) u r) g) L γ η δ base roots) r‖ ≤ 1 * Bnd := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hpar).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hU) hB0
  have hsC : ‖∑ c ∈ Cf D.fix v, ∫ r, (Ilo D.layer D.rootTime D.fix v c).indicator
      (fun r => splicedKernelMK G (modData D (pin (pin D.fix v r) c r) g) L γ η δ base roots) r‖ ≤ 3 * Bnd := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hch).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hC) hB0
  unfold facesK
  calc _ ≤ ‖_ + _‖ + ‖_ + _‖ := norm_sub_le _ _
    _ ≤ (‖_‖ + ‖_‖) + (‖_‖ + ‖_‖) := add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ (Bnd + 1 * Bnd) + (Bnd + 3 * Bnd) := add_le_add (add_le_add htop hsU) (add_le_add hfl hsC)
    _ = 6 * Bnd := by ring

/-- **One selected atom** (o73 (20.5)): if the selected frequency is at least `λ` on the support, the kernel is at
most `12/λ` times any bound for the one-step pinned modifications. -/
theorem expand_one (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (hD : SplicedAmplitudeBounds G D.toSplicedKernelData) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (v : GBranch G.tree) (hv : D.fix v = none) {lam : ℝ} (hlam : 0 < lam)
    (hα : ∀ z : GenDecoration G d roots 0, ampMK G D L γ η base z.1 ≠ 0 →
      lam ≤ |selFreq D L γ δ v (cosetDecoration G L base z.1)|)
    (Bnd : ℝ) (hB0 : 0 ≤ Bnd) (hB : OneStepBound D v L γ η δ base roots Bnd) :
    ‖splicedKernelMK G D L γ η δ base roots‖ ≤ (12 / lam) * Bnd := by
  have hK := kernel_eq_sum hP D hD hL γ η δ base roots D.fix (fun _ => 1)
  rw [modData_self] at hK
  have hz : ∀ z : GenDecoration G d roots 0,
      ampMK G D L γ η base z.1 * ((fun _ => (1 : ℝ)) (cosetDecoration G L base z.1) : ℂ) *
        splicedFourierBMK G D.layer D.rootTime D.fix (splicedFrequency G D.toSplicedKernelData L γ δ base z.1) =
      (-Complex.I / (lam : ℂ)) *
        ((ampMK G D L γ η base z.1 * (gPlus D L γ δ v lam (cosetDecoration G L base z.1) : ℂ)) *
            facesB D.layer D.rootTime D.fix v (splicedFrequency G D.toSplicedKernelData L γ δ base z.1) -
          (ampMK G D L γ η base z.1 * (gMinus D L γ δ v lam (cosetDecoration G L base z.1) : ℂ)) *
            facesB D.layer D.rootTime D.fix v (splicedFrequency G D.toSplicedKernelData L γ δ base z.1)) := by
    intro z
    simp only [Complex.ofReal_one, mul_one]
    by_cases h0 : ampMK G D L γ η base z.1 = 0
    · simp [h0]
    have hθ := hα z h0
    have hθ0 : Real.pi * splicedFrequency G D.toSplicedKernelData L γ δ base z.1 v ≠ 0 := fun h => by
      rw [selFreq_coset, h, abs_zero] at hθ; linarith
    rw [face_expand' _ _ _ v hv _ hθ0]
    have hsplit := inv_selFreq_split D L γ δ v hlam (cosetDecoration G L base z.1) hθ
    rw [selFreq_coset] at hsplit
    rw [hsplit]
    ring
  have key : splicedKernelMK G D L γ η δ base roots = (-Complex.I / (lam : ℂ)) *
      (facesK D v (gPlus D L γ δ v lam) L γ η δ base roots - facesK D v (gMinus D L γ δ v lam) L γ η δ base roots) := by
    rw [hK, ← faces_sum hP D hD hL γ η δ base roots v hv, ← faces_sum hP D hD hL γ η δ base roots v hv,
      ← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [hz z]; ring
  rw [key]
  have hP' := norm_facesK_le D v (gPlus D L γ δ v lam) (gPlus_mem D L γ δ v hlam.le)
    (gPlus_local D L γ δ v lam) γ η δ base roots Bnd hB0 hB
  have hM' := norm_facesK_le D v (gMinus D L γ δ v lam) (gMinus_mem D L γ δ v hlam.le)
    (gMinus_local D L γ δ v lam) γ η δ base roots Bnd hB0 hB
  have hn : ‖(-Complex.I / (lam : ℂ))‖ = 1 / lam := by
    rw [norm_div, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hlam.le]
  rw [norm_mul, hn]
  calc 1 / lam * ‖_ - _‖ ≤ 1 / lam * (6 * Bnd + 6 * Bnd) :=
        mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hP' hM')) (by positivity)
    _ = 12 / lam * Bnd := by ring

end WaveTurbulence.Flower.SelRes

namespace WaveTurbulence.Flower.SelRes
open MeasureTheory Set Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.FinalMKDefs
  WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKFine
open WaveTurbulence.Flower.FlFace (fixSel children parents IsChildOf.ne)

variable {w d : ℕ} {G : Garden w}

/-- The modifications produced by expanding the selected atoms of `S`: same amplitude data and filters, the
indicator multiplied by a `[0,1]`-valued function local to `S`, and pins changed only at `S` and at most `#S`
recipients, inside the layer boxes. -/
structure ModOK (S : Finset (GBranch G.tree)) (D D' : SplicedKernelDataMK G d) : Prop where
  data : D'.toSplicedKernelData = D.toSplicedKernelData
  filt : D'.filt = D.filt
  ind : ∃ g : (GNode G.tree → Mom d) → ℝ, (∀ k, 0 ≤ g k ∧ g k ≤ 1) ∧
    (∀ k k', (∀ a ∈ S, ∀ i : Fin 3, k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → g k = g k') ∧
    ∀ k, D'.ind k = D.ind k * g k
  recip : ∃ Rc : Finset (GBranch G.tree), Rc.card ≤ S.card ∧ (∀ b, D'.fix b ≠ D.fix b → b ∈ S ∪ Rc) ∧
    ∀ b, D'.fix b ≠ D.fix b → ∃ t, D'.fix b = some t ∧ (D.layer b : ℝ) ≤ t ∧ t ≤ D.layer b + 1

theorem ModOK.refl (D : SplicedKernelDataMK G d) : ModOK ∅ D D :=
  ⟨rfl, rfl, ⟨fun _ => 1, fun _ => ⟨zero_le_one, le_rfl⟩, fun _ _ _ => rfl, fun _ => (mul_one _).symm⟩,
    ⟨∅, le_rfl, fun _ h => absurd rfl h, fun _ h => absurd rfl h⟩⟩

theorem ModOK.one (D : SplicedKernelDataMK G d) (v y : GBranch G.tree) (r : ℝ) (g : (GNode G.tree → Mom d) → ℝ)
    (hg : ∀ k, 0 ≤ g k ∧ g k ≤ 1)
    (hgl : ∀ k k', ((∀ i : Fin 3, k (v.child i) = k' (v.child i)) ∧ k v.toNode = k' v.toNode) → g k = g k')
    (hv : (D.layer v : ℝ) ≤ r ∧ r ≤ D.layer v + 1) (hy : (D.layer y : ℝ) ≤ r ∧ r ≤ D.layer y + 1) :
    ModOK {v} D (modData D (pin (pin D.fix v r) y r) g) := by
  refine ⟨rfl, rfl, ⟨g, hg, fun k k' h => hgl k k' ⟨fun i => (h v (mem_singleton_self v) i).1,
    (h v (mem_singleton_self v) 0).2⟩, fun k => rfl⟩, ⟨{y}, by simp, fun b hb => ?_, fun b hb => ?_⟩⟩
  · by_contra hn
    simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hn
    exact hb (by simp [modData, pin, Function.update_of_ne hn.1, Function.update_of_ne hn.2])
  · by_cases hby : b = y
    · subst hby; exact ⟨r, by simp [modData, pin], hy⟩
    · by_cases hbv : b = v
      · subst hbv; exact ⟨r, by simp [modData, pin, Function.update_of_ne hby], hv⟩
      · exact absurd (by simp [modData, pin, Function.update_of_ne hby, Function.update_of_ne hbv]) hb

theorem ModOK.trans {S₁ S₂ : Finset (GBranch G.tree)} {D D₁ D₂ : SplicedKernelDataMK G d} (h₁ : ModOK S₁ D D₁)
    (h₂ : ModOK S₂ D₁ D₂) (hd : Disjoint S₁ S₂) : ModOK (S₁ ∪ S₂) D D₂ := by
  obtain ⟨hd₁, hf₁, ⟨g₁, hg₁, hl₁, hi₁⟩, ⟨R₁, hR₁, hc₁, hb₁⟩⟩ := h₁
  obtain ⟨hd₂, hf₂, ⟨g₂, hg₂, hl₂, hi₂⟩, ⟨R₂, hR₂, hc₂, hb₂⟩⟩ := h₂
  refine ⟨hd₂.trans hd₁, hf₂.trans hf₁, ⟨fun k => g₁ k * g₂ k, fun k => ⟨mul_nonneg (hg₁ k).1 (hg₂ k).1,
    (mul_le_mul (hg₁ k).2 (hg₂ k).2 (hg₂ k).1 zero_le_one).trans_eq (one_mul 1)⟩, fun k k' h => ?_, fun k => by rw [hi₂, hi₁, mul_assoc]⟩,
    ⟨R₁ ∪ R₂, ?_, fun b hb => ?_, fun b hb => ?_⟩⟩
  · show g₁ k * g₂ k = g₁ k' * g₂ k'
    rw [hl₁ k k' fun a ha => h a (mem_union_left _ ha), hl₂ k k' fun a ha => h a (mem_union_right _ ha)]
  · calc (R₁ ∪ R₂).card ≤ R₁.card + R₂.card := card_union_le _ _
      _ ≤ S₁.card + S₂.card := add_le_add hR₁ hR₂
      _ = (S₁ ∪ S₂).card := (card_union_of_disjoint hd).symm
  · by_cases h2 : D₂.fix b = D₁.fix b
    · have := hc₁ b (by rwa [h2] at hb)
      simp only [Finset.mem_union] at this ⊢; tauto
    · have := hc₂ b h2
      simp only [Finset.mem_union] at this ⊢; tauto
  · by_cases h2 : D₂.fix b = D₁.fix b
    · rw [h2]; exact hb₁ b (by rwa [h2] at hb)
    · obtain ⟨t, ht, hbox⟩ := hb₂ b h2
      have hl : D₁.layer = D.layer := by rw [show D₁.layer = D₁.toSplicedKernelData.layer from rfl, hd₁]
      exact ⟨t, ht, by rwa [hl] at hbox⟩

theorem selFreq_congr {D D' : SplicedKernelDataMK G d} (h : D'.toSplicedKernelData = D.toSplicedKernelData)
    (L γ δ : ℝ) (v : GBranch G.tree) : selFreq D' L γ δ v = selFreq D L γ δ v := by
  funext k; unfold selFreq
  rw [show D'.frequency = D'.toSplicedKernelData.frequency from rfl, h]

/-- **Several selected atoms, one per tree, each at its own `λ_v`** (induction on `expand_one`; finding F-C5b-1). -/
theorem expand_bound_atom (hP : G.IsPlain) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (lam : GBranch G.tree → ℝ) (Bnd : ℝ) (hB0 : 0 ≤ Bnd) :
    ∀ (S : Finset (GBranch G.tree)) (D : SplicedKernelDataMK G d), (∀ v ∈ S, 0 < lam v) →
      SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a = b) →
      (∀ v ∈ S, D.fix v = none) →
      (∀ v ∈ S, ∀ z : GenDecoration G d roots 0, ampMK G D L γ η base z.1 ≠ 0 →
        lam v ≤ |selFreq D L γ δ v (cosetDecoration G L base z.1)|) →
      (∀ D', ModOK S D D' → ‖splicedKernelMK G D' L γ η δ base roots‖ ≤ Bnd) →
      ‖splicedKernelMK G D L γ η δ base roots‖ ≤ (∏ v ∈ S, 12 / lam v) * Bnd := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro D _ _ _ _ _ hB
    simpa using hB D (ModOK.refl D)
  | insert v S hvS ih =>
    intro D hlam hD hS1 hfree hα hB
    rw [prod_insert hvS, mul_assoc]
    have hlamS : ∀ v' ∈ S, 0 < lam v' := fun v' hv' => hlam v' (mem_insert_of_mem hv')
    have hBnd' : 0 ≤ (∏ v' ∈ S, 12 / lam v') * Bnd :=
      mul_nonneg (prod_nonneg fun v' hv' => by have := hlamS v' hv'; positivity) hB0
    refine expand_one hP D hD hL γ η δ base roots v (hfree v (mem_insert_self v S)) (hlam v (mem_insert_self v S))
      (hα v (mem_insert_self v S)) _ hBnd' ?_
    intro y r g hg hgl hy hbv hby
    set D₁ := modData D (pin (pin D.fix v r) y r) g with hD₁
    have hyt : y.1.1 = v.1.1 := by
      rcases hy with rfl | ⟨_, h | h⟩
      · rfl
      · exact h.1
      · exact h.1.symm
    refine ih D₁ hlamS hD (fun a ha b hb => hS1 a (mem_insert_of_mem ha) b (mem_insert_of_mem hb))
      (fun v' hv' => ?_) (fun v' hv' z hz => ?_) (fun D' hD' => ?_)
    · have hv'v : v' ≠ v := fun h => hvS (h ▸ hv')
      have hv'y : v' ≠ y := fun h => hv'v (hS1 v' (mem_insert_of_mem hv') v (mem_insert_self v S) (h ▸ hyt))
      show pin (pin D.fix v r) y r v' = none
      rw [pin_apply_of_ne hv'y, pin_apply_of_ne hv'v]; exact hfree v' (mem_insert_of_mem hv')
    · have hz' : ampMK G D L γ η base z.1 ≠ 0 := by
        intro h0; apply hz; rw [hD₁, ampMK_modData, h0, zero_mul]
      rw [selFreq_congr (D := D) (D' := D₁) rfl]
      exact hα v' (mem_insert_of_mem hv') z hz'
    · have h1 := ModOK.one D v y r g hg hgl hbv hby
      have h2 := h1.trans hD' (disjoint_singleton_left.2 hvS)
      rw [show ({v} : Finset _) ∪ S = insert v S from rfl] at h2
      exact hB D' h2

/-- **Several selected atoms, one per tree** (`expand_bound_atom` at a constant `λ`). -/
theorem expand_bound (hP : G.IsPlain) {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) {lam : ℝ} (hlam : 0 < lam) (Bnd : ℝ) (hB0 : 0 ≤ Bnd) :
    ∀ (S : Finset (GBranch G.tree)) (D : SplicedKernelDataMK G d),
      SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ a ∈ S, ∀ b ∈ S, a.1.1 = b.1.1 → a = b) →
      (∀ v ∈ S, D.fix v = none) →
      (∀ v ∈ S, ∀ z : GenDecoration G d roots 0, ampMK G D L γ η base z.1 ≠ 0 →
        lam ≤ |selFreq D L γ δ v (cosetDecoration G L base z.1)|) →
      (∀ D', ModOK S D D' → ‖splicedKernelMK G D' L γ η δ base roots‖ ≤ Bnd) →
      ‖splicedKernelMK G D L γ η δ base roots‖ ≤ (12 / lam) ^ S.card * Bnd := by
  intro S D hD hS1 hfree hα hB
  have h := expand_bound_atom hP hL γ η δ base roots (fun _ => lam) Bnd hB0 S D (fun _ _ => hlam) hD hS1 hfree hα hB
  rwa [prod_const] at h

end WaveTurbulence.Flower.SelRes

