/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtWhole.FoldBox
public import WaveTurbulence.Foundations.IncohInst.Regref.NormShift

/-! # D6b: fold interpolation on the protected time boxes, for kernels that read the port time

`fold_free`: let `F(·, k)` be continuous on `ℝ²` and, when `q' < p`, independent of the port time on the box
(`F ts k = F (ts 0, p) k` on `timeBoxGt p q'`: the free lone parents sit in layer `p`, above the port). Then

`‖F(·,k)‖_{X^η(timeBoxGt p q')} ≤ C · (sup |F(·,k)|)^τ · ‖F(·,k)‖_{X^{1/4}(timeBoxGt p q')}^{1-τ}`,  `τ = (1-8η)/9`.

* `q' = p`: the box lies in the closed triangle, where D1b-F's `foldInterpolation` applies to `F(·,k)` itself; the
  `X^{1/4}` input is moved from the open triangle to the closed one by the continuous representative;
* `q' < p`: `F = G ∘ (· 0)` on the box; `box_transfer` gives the triangle for `G ∘ (· 0)`, and the `X^{1/4}` input
  on the triangle comes from the box by the time translation `ts 1 ↦ ts 1 - (p - q')` (main `XNorm00_shift`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology WaveTurbulence.Fourier
open scoped ENNReal Classical

namespace WaveTurbulence.Flower.ProtWhole

open WaveTurbulence.Flower.ProtDefs

/-- `rep_agrees` for a general continuous function. -/
theorem rep_agrees_gen {θ : ℝ} (hθ : 0 ≤ θ) {p : ℝ} {h : (Fin 2 → ℝ) → ℂ} (hh : timeFourierNorm θ h < ⊤)
    {g : (Fin 2 → ℝ) → ℂ} (hg : Continuous g) (hU : ∀ x ∈ triU p, h x = g x) :
    ∀ x ∈ triP p, timeFourier (timeFourier h) (-x) = g x := by
  obtain ⟨hc, hae⟩ := Regref.timeFourier_continuous_representative hθ h hh
  have hint : EqOn (fun t => timeFourier (timeFourier h) (-t)) g (triU p) := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ (isOpen_triU p) hc.continuousOn hg.continuousOn
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem (isOpen_triU p).measurableSet] with t h1 h2
    exact h1.trans (hU t h2)
  exact hint.of_subset_closure hc.continuousOn hg.continuousOn (fun x hx => ⟨hx.1.le, hx.2.1.le, hx.2.2.le⟩)
    (triP_subset_closure p)

/-- The `X^{1/4}` input for a continuous function: the closed triangle from the open box `timeBoxGt p p`. -/
theorem quarter_gen {d : ℕ} (θ : ℝ) (hθ : 0 ≤ θ) (p : ℝ) (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d)
    (hc : Continuous fun ts => F ts k) :
    XNorm00Restr θ (triP p) univ (fun ts (_ : Unit) => F ts k) ≤ XNorm00Restr θ (timeBoxGt p p) {k} F := by
  unfold XNorm00Restr
  refine le_iInf₂ fun E hE => ?_
  by_cases htop : XNorm00 θ E = ⊤
  · rw [htop]; exact le_top
  set h : (Fin 2 → ℝ) → ℂ := fun t => E t k
  have hle : timeFourierNorm θ h ≤ XNorm00 θ E := by
    rw [← NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm]; exact XNorm00_comp_le θ E k
  have hh : timeFourierNorm θ h < ⊤ := lt_of_le_of_lt hle (lt_top_iff_ne_top.2 htop)
  have hU : ∀ x ∈ triU p, h x = F x k := fun x hx => hE x (triU_subset_box p hx) k (Set.mem_singleton k)
  have hrep := rep_agrees_gen hθ hh hc hU
  obtain ⟨-, hae⟩ := Regref.timeFourier_continuous_representative hθ h hh
  refine iInf₂_le_of_le (fun t (_ : Unit) => timeFourier (timeFourier h) (-t)) (fun x hx _ _ => hrep x hx) ?_
  rw [NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm, ProtPin.timeFourierNorm_congr_ae hae]
  exact hle

/-- One output of a box restriction is bounded by a `Unit`-valued restriction to a larger set. -/
theorem restr_single_le {d : ℕ} (θ : ℝ) {B B' : Set (Fin 2 → ℝ)} (hBB : B ⊆ B') (F : (Fin 2 → ℝ) → Mom d → ℂ)
    (k : Mom d) (f : (Fin 2 → ℝ) → Unit → ℂ) (hf : ∀ ts ∈ B, F ts k = f ts ()) :
    XNorm00Restr θ B {k} F ≤ XNorm00Restr θ B' univ f := by
  unfold XNorm00Restr
  refine le_iInf₂ fun g hg => ?_
  refine iInf₂_le_of_le (fun t k' => if k' = k then g t () else 0) (fun ts hts v hv => ?_) ?_
  · rw [Set.mem_singleton_iff] at hv
    subst hv
    show (if v = v then g ts () else 0) = F ts v
    rw [if_pos rfl, hg ts (hBB hts) () (Set.mem_univ _), hf ts hts]
  · rw [XNorm00_single]
    exact (NormBridgeScratch.XNorm00_unit_eq_timeFourierNorm θ (fun t => g t ())).symm.le

/-- The restriction norm only sees the values on `B × K`. -/
theorem restr00_congr {r : ℕ} {V : Type*} (θ : ℝ) {B : Set (Fin r → ℝ)} {K : Set V} {F F' : (Fin r → ℝ) → V → ℂ}
    (h : ∀ t ∈ B, ∀ v ∈ K, F t v = F' t v) : XNorm00Restr θ B K F = XNorm00Restr θ B K F' := by
  unfold XNorm00Restr
  exact le_antisymm (le_iInf₂ fun G hG => iInf₂_le G fun t ht v hv => (hG t ht v hv).trans (h t ht v hv).symm)
    (le_iInf₂ fun G hG => iInf₂_le G fun t ht v hv => (hG t ht v hv).trans (h t ht v hv))

/-- The `X^θ` input on the triangle from the box `timeBoxGt p q'` (`q' < p`) by a translation of the port time. -/
theorem shift_tri_le {d : ℕ} (θ : ℝ) {p q' : ℕ} (hlt : q' < p) (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d)
    (G : ℝ → ℂ) (hport : ∀ ts ∈ timeBoxGt (p : ℝ) q', F ts k = G (ts 0)) :
    XNorm00Restr θ (triP p) univ (fun ts (_ : Unit) => G (ts 0)) ≤ XNorm00Restr θ (timeBoxGt p q') {k} F := by
  have hpq : (q' : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hlt
  unfold XNorm00Restr
  refine le_iInf₂ fun E hE => ?_
  set c : Fin 2 → ℝ := ![0, (p : ℝ) - q'] with hc
  refine iInf₂_le_of_le (fun t (_ : Unit) => E (t - c) k) (fun ts hts _ _ => ?_) ?_
  · obtain ⟨h1, h2, h3⟩ := hts
    have e0 : (ts - c) 0 = ts 0 := by simp [hc]
    have e1 : (ts - c) 1 = ts 1 - ((p : ℝ) - q') := by simp [hc]
    have hmem : ts - c ∈ timeBoxGt (p : ℝ) q' := by
      refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩
      · rw [e0]; linarith
      · rw [e0]; exact h3
      · rw [e1]; linarith
      · rw [e1]; linarith
      · rw [e0, e1]; linarith
    show E (ts - c) k = G (ts 0)
    rw [hE _ hmem k (Set.mem_singleton k), hport _ hmem, e0]
  · calc XNorm00 θ (fun t (_ : Unit) => E (t - c) k) = XNorm00 θ (fun t (_ : Unit) => E t k) :=
          Regref.XNorm00_shift θ (fun t (_ : Unit) => E t k) c
      _ ≤ XNorm00 θ E := XNorm00_comp_le θ E k

/-- **Fold interpolation on `timeBoxGt p q'`** for kernels that read the port time. -/
theorem fold_free (d : ℕ) {η : ℝ} (hη0 : 0 ≤ η) (hη8 : η < 1 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p q' : ℕ), q' ≤ p → ∀ (F : (Fin 2 → ℝ) → Mom d → ℂ) (k : Mom d),
      Continuous (fun ts => F ts k) →
      (q' < p → ∀ ts ∈ timeBoxGt (p : ℝ) q', F ts k = F ![ts 0, (p : ℝ)] k) →
      XNorm00Restr η (timeBoxGt p q') {k} F ≤
        ENNReal.ofReal C * (⨆ ts : Fin 2 → ℝ, ‖F ts k‖ₑ) ^ ((1 - 8 * η) / 9) *
          XNorm00Restr (1 / 4) (timeBoxGt p q') {k} F ^ (1 - (1 - 8 * η) / 9) := by
  obtain ⟨Cf, hCf0, hfold⟩ := ProtOpsFold.foldInterpolation η hη0 hη8
  obtain ⟨Cb, hCb0, hbox⟩ := box_transfer (d := d) η hη0
  refine ⟨max 1 Cb * Cf, mul_nonneg (le_max_of_le_left zero_le_one) hCf0, fun p q' hq F k hc hport => ?_⟩
  have hτ0 : 0 ≤ (1 - 8 * η) / 9 := by linarith
  have hτ1 : 0 ≤ 1 - (1 - 8 * η) / 9 := by linarith
  have hCC : ENNReal.ofReal Cf ≤ ENNReal.ofReal (max 1 Cb * Cf) :=
    ENNReal.ofReal_le_ofReal (le_mul_of_one_le_left hCf0 (le_max_left _ _))
  rcases Nat.eq_or_lt_of_le hq with hpq | hlt
  · -- q' = p: fold on the closed triangle for `F(·,k)` itself
    subst hpq
    set f : (Fin 2 → ℝ) → Unit → ℂ := fun ts _ => F ts k with hfdef
    have h1 : XNorm00Restr η (timeBoxGt q' q') {k} F ≤ XNorm00Restr η (triP q') univ f :=
      restr_single_le η (triP_subset_of_box _) F k f (fun _ _ => rfl)
    have h2 := hfold (q' : ℝ) f (fun _ => hc.continuousOn)
    have hsup : (⨆ (ts : Fin 2 → ℝ) (_ : (q' : ℝ) ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ q' + 1), ‖f ts ()‖ₑ) ≤
        ⨆ ts : Fin 2 → ℝ, ‖F ts k‖ₑ :=
      iSup₂_le fun ts _ => le_iSup (fun ts : Fin 2 → ℝ => ‖F ts k‖ₑ) ts
    have hq4 := quarter_gen (1 / 4) (by norm_num) (q' : ℝ) F k hc
    refine h1.trans (h2.trans ?_)
    gcongr
    · exact hq4
  · -- q' < p: `F = G ∘ (· 0)` on the box
    set G : ℝ → ℂ := fun T => F ![T, (p : ℝ)] k with hGdef
    have hG : Continuous G := hc.comp (continuous_pi fun i => by
      fin_cases i
      · exact continuous_id
      · exact continuous_const)
    have hbx : ∀ ts ∈ timeBoxGt (p : ℝ) q', F ts k = G (ts 0) := fun ts hts => hport hlt ts hts
    set F' : (Fin 2 → ℝ) → Mom d → ℂ := fun ts _ => G (ts 0) with hF'
    have e1 : XNorm00Restr η (timeBoxGt p q') {k} F = XNorm00Restr η (timeBoxGt p q') {k} F' :=
      restr00_congr η fun ts hts v hv => by
        rw [Set.mem_singleton_iff] at hv
        subst hv
        exact hbx ts hts
    have h1 := hbox p q' hq F' k G hG (fun _ => rfl)
    have h2 := hfold (p : ℝ) (fun ts (_ : Unit) => G (ts 0)) (fun _ => (hG.comp (continuous_apply 0)).continuousOn)
    have hsup : (⨆ (ts : Fin 2 → ℝ) (_ : (p : ℝ) ≤ ts 1 ∧ ts 1 ≤ ts 0 ∧ ts 0 ≤ p + 1),
        ‖(fun ts (_ : Unit) => G (ts 0)) ts ()‖ₑ) ≤ ⨆ ts : Fin 2 → ℝ, ‖F ts k‖ₑ :=
      iSup₂_le fun ts _ => le_iSup (fun ts : Fin 2 → ℝ => ‖F ts k‖ₑ) ![ts 0, (p : ℝ)]
    have hq4 := shift_tri_le (1 / 4) hlt F k G hbx
    rw [e1]
    refine h1.trans ?_
    calc ENNReal.ofReal Cb * XNorm00Restr η (triP p) univ (fun ts (_ : Unit) => G (ts 0))
        ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Cf * (⨆ ts : Fin 2 → ℝ, ‖F ts k‖ₑ) ^ ((1 - 8 * η) / 9) *
            XNorm00Restr (1 / 4) (timeBoxGt p q') {k} F ^ (1 - (1 - 8 * η) / 9)) := by
          refine mul_le_mul_of_nonneg_left (h2.trans ?_) zero_le
          gcongr
          · exact hq4
      _ = ENNReal.ofReal (Cb * Cf) * (⨆ ts : Fin 2 → ℝ, ‖F ts k‖ₑ) ^ ((1 - 8 * η) / 9) *
            XNorm00Restr (1 / 4) (timeBoxGt p q') {k} F ^ (1 - (1 - 8 * η) / 9) := by
          rw [ENNReal.ofReal_mul hCb0]; ring
      _ ≤ _ := by
          gcongr
          exact le_max_right _ _

end WaveTurbulence.Flower.ProtWhole
