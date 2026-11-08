/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.Rungs
public import WaveTurbulence.Foundations.Flower.FinalMKPin.Tree
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the frequency class on the clocks and the class bound

The exceptional frequencies `β` are fixed on the non-clock branches (pins and substituted branches). A clock carries
the frequency of its fibre (`shiftF`), which is its own frequency plus the fixed shift `cI β`. The class of a
presentation family, read on the clocks, is `clsI`. Its `1`-neighbourhood is integrated in the generic engine.

- Localization (o73 Prop 18.1: "all affine rung relations T2013 persist with changed constant terms, since `β_E` is
  fixed; retain their original anchor pairs"): `hXI` is main's center with the clock frequencies unshifted and the
  non-clock branches set to `β` (`extI`). The estimate is main's `loc_S`.
- The sets `S_v` translate by the shift (`SyI`). Main's `K`-lemma bound is translation invariant.
- `class_fourierI` is main's `class_bound`, applied on the clocks with the segments of `Rungs`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LadderDisjoint
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w d : ℕ} {G : Garden w}

/-- The shift of a clock: the fixed frequencies of the other branches of its fibre. -/
noncomputable def cI (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (β : GBranch G.tree → ℝ) (a : Iv fix face) : ℝ :=
  ∑ b ∈ (fib fix face a).erase a.1, β b

/-- Clock frequencies, unshifted, extended by `β` off the clocks. -/
noncomputable def extI (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (β : GBranch G.tree → ℝ) (α : Iv fix face → ℝ) (b : GBranch G.tree) : ℝ :=
  if h : fix b = none ∧ face b = none then α ⟨b, h⟩ - cI fix face β ⟨b, h⟩ else β b

/-- Frequencies equal to `β` off the clocks. -/
def AgreeE (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (β α : GBranch G.tree → ℝ) : Prop :=
  ∀ b, ¬ (fix b = none ∧ face b = none) → α b = β b

/-- The class of a presentation family, read on the clocks. -/
def clsI (D : SplicedKernelData G d) (scales : Finset (GBranch G.tree) → ℝ) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (π0 : PF G) (fix : GBranch G.tree → Option ℝ)
    (face : GBranch G.tree → Option (GBranch G.tree)) (β : GBranch G.tree → ℝ) : Set (Iv fix face → ℝ) :=
  {α' | ∃ α ∈ clsPF G D scales L γ η δ base roots π0, AgreeE fix face β α ∧ α' = shiftF fix face α}

variable {fix : GBranch G.tree → Option ℝ} {face : GBranch G.tree → Option (GBranch G.tree)}
  {β : GBranch G.tree → ℝ}

theorem shiftF_eq {α : GBranch G.tree → ℝ} (hα : AgreeE fix face β α) (a : Iv fix face) :
    shiftF fix face α a = α a.1 + cI fix face β a := by
  have ha : a.1 ∈ fib fix face a := by
    simp [fib, a.2.1, repV_of_none a.2.2]
  unfold shiftF cI
  rw [← Finset.add_sum_erase _ _ ha]
  congr 1
  refine Finset.sum_congr rfl fun b hb => ?_
  obtain ⟨hne, hbf⟩ := Finset.mem_erase.mp hb
  obtain ⟨hb1, hb2⟩ := (Finset.mem_filter.mp hbf).2
  refine hα b fun h => hne ?_
  rw [← hb2, repV_of_none h.2]

theorem extI_free (α : Iv fix face → ℝ) (a : Iv fix face) : extI fix face β α a.1 = α a - cI fix face β a := by
  simp [extI, a.2.1, a.2.2]

theorem extI_close {D : SplicedKernelData G d} {scales : Finset (GBranch G.tree) → ℝ} {L γ η δ : ℝ} {base : Mom d}
    {roots : Fin w → (Fin d → ℤ)} {π0 : PF G} {α' : Iv fix face → ℝ}
    (h : α' ∈ Wnb (clsI D scales L γ η δ base roots π0 fix face β)) :
    ∃ α ∈ clsPF G D scales L γ η δ base roots π0, ∀ b, |extI fix face β α' b - α b| ≤ 1 := by
  obtain ⟨α'', ⟨α, hα, hag, rfl⟩, hcl⟩ := h
  refine ⟨α, hα, fun b => ?_⟩
  by_cases hb : fix b = none ∧ face b = none
  · have := hcl ⟨b, hb⟩
    rw [shiftF_eq hag] at this
    simp only [extI, dif_pos hb]
    have e : α' ⟨b, hb⟩ - cI fix face β ⟨b, hb⟩ - α b = α' ⟨b, hb⟩ - (α b + cI fix face β ⟨b, hb⟩) := by ring
    rw [e]; exact this
  · simp only [extI, dif_neg hb, hag b hb, sub_self, abs_zero, zero_le_one]

theorem measurable_extI (b : GBranch G.tree) : Measurable (fun α : Iv fix face → ℝ => extI fix face β α b) := by
  unfold extI
  by_cases hb : fix b = none ∧ face b = none
  · simp only [dif_pos hb]; exact (measurable_pi_apply _).sub measurable_const
  · simp only [dif_neg hb]; exact measurable_const

theorem extI_congr {α α' : Iv fix face → ℝ} {b : GBranch G.tree}
    (h : ∀ hb : fix b = none ∧ face b = none, α ⟨b, hb⟩ = α' ⟨b, hb⟩) :
    extI fix face β α b = extI fix face β α' b := by
  unfold extI
  by_cases hb : fix b = none ∧ face b = none
  · simp only [dif_pos hb, h hb]
  · simp only [dif_neg hb]

/-! ### The sets `S_v`, translated -/

/-- The translated value set of a clock. -/
def SyI (Sy : GBranch G.tree → Set ℝ) (fix : GBranch G.tree → Option ℝ)
    (face : GBranch G.tree → Option (GBranch G.tree)) (β : GBranch G.tree → ℝ) (a : Iv fix face) : Set ℝ :=
  (fun z => z - cI fix face β a) ⁻¹' Sy a.1

theorem measurableSet_SyI {Sy : GBranch G.tree → Set ℝ} (hSy : ∀ b, MeasurableSet (Sy b)) (a : Iv fix face) :
    MeasurableSet (SyI Sy fix face β a) :=
  (measurable_id.sub measurable_const) (hSy a.1)

theorem lintegral_SyI {Sy : GBranch G.tree → Set ℝ} {Kc : ℝ≥0∞} (hSy : ∀ b, MeasurableSet (Sy b))
    (hKc : ∀ b (β' : ℝ), ∫⁻ a in Sy b, ENNReal.ofReal (br (a + β'))⁻¹ ≤ Kc) (a : Iv fix face) (β' : ℝ) :
    ∫⁻ z in SyI Sy fix face β a, ENNReal.ofReal (br (z + β'))⁻¹ ≤ Kc := by
  set c := cI fix face β a
  have hm := measurableSet_SyI (β := β) hSy a
  rw [← lintegral_indicator hm]
  have e : ∀ z, (SyI Sy fix face β a).indicator (fun z => ENNReal.ofReal (br (z + β'))⁻¹) z =
      (Sy a.1).indicator (fun y => ENNReal.ofReal (br (y + (c + β')))⁻¹) (z - c) := by
    intro z
    by_cases hz : z - c ∈ Sy a.1
    · have hz' : z ∈ SyI Sy fix face β a := hz
      rw [Set.indicator_of_mem hz', Set.indicator_of_mem hz]
      congr 3; ring
    · have hz' : z ∉ SyI Sy fix face β a := hz
      rw [Set.indicator_of_notMem hz', Set.indicator_of_notMem hz]
  simp_rw [e]
  rw [lintegral_sub_right_eq_self (fun y => (Sy a.1).indicator (fun y => ENNReal.ofReal (br (y + (c + β')))⁻¹) y) c,
    lintegral_indicator (hSy a.1)]
  exact hKc a.1 (c + β')

/-! ### The centers of the `X` clocks -/

section centers
variable {L γ δ : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)} {hp : G.IsPlain} {π0 : PF G}
  {D : SplicedKernelData G d} {εS : LQ G → ℝ}

/-- The center of an `X` clock: main's `hXf` on unshifted clock frequencies, plus the shift. -/
noncomputable def hXI (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree)) (β : GBranch G.tree → ℝ)
    (θ : Jr (Kq fix face π0 (cd.JS isSmall)) → Bool) (x : Iv fix face) (α : Iv fix face → ℝ) : ℝ :=
  if h : ∃ s, xθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ s = x then
    cI fix face β x +
      ((∑ l, cd.cc h.choose.1.1 (enumq fix face π0 (cd.JS isSmall) h.choose.1 h.choose.2) l *
          (extI fix face β α (atomAt π0 h.choose.1.1 true (cd.r' h.choose.1.1 l)) +
            extI fix face β α (atomAt π0 h.choose.1.1 false (cd.r' h.choose.1.1 l)))) +
        cd.dd h.choose.1.1 (enumq fix face π0 (cd.JS isSmall) h.choose.1 h.choose.2)) -
      extI fix face β α (yθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ h.choose).1
  else 0

theorem cd_hJS (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) :
    ∀ S j, j ∈ cd.JS isSmall S → 1 ≤ j ∧ j < π0.m S := fun S _ hj => (cd.JS_sub isSmall S hj).1

theorem hXI_measurable (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (θ : Jr (Kq fix face π0 (cd.JS isSmall)) → Bool) (x : Iv fix face) :
    Measurable (hXI cd isSmall fix face β θ x) := by
  unfold hXI
  by_cases h : ∃ s, xθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ s = x
  · simp only [dif_pos h]
    refine Measurable.sub (Measurable.const_add (Measurable.add (Finset.measurable_sum _ fun l _ => ?_)
      measurable_const) _) (measurable_extI _)
    exact measurable_const.mul ((measurable_extI _).add (measurable_extI _))
  · simp only [dif_neg h]; exact measurable_const

theorem xθ_val_I (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (θ : Jr (Kq fix face π0 (cd.JS isSmall)) → Bool) (s : Jr (Kq fix face π0 (cd.JS isSmall))) :
    (xθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ s).1 =
      atomAt π0 s.1.1 (θ s) (enumq fix face π0 (cd.JS isSmall) s.1 s.2) := by
  unfold xθ
  cases θ s
  · simp [vaI_val]
  · simp [uaI_val]

theorem sel_not_XI (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (θ : Jr (Kq fix face π0 (cd.JS isSmall)) → Bool) (S : LQ G) (l : Fin (cd.q S)) (b : Bool)
    (x : Iv fix face) (hx : x.1 = atomAt π0 S b (cd.r' S l)) :
    x ∉ Finset.univ.image (xθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ) := by
  intro hmem
  obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hmem
  have hrI := cd.hrI S l
  rw [Finset.mem_Icc] at hrI
  have e := congrArg Subtype.val hs
  rw [xθ_val_I, hx] at e
  obtain ⟨h1, _, h3⟩ := atomAt_inj π0 s.1.1 S (θ s) b (enumq_le (cd_hJS cd isSmall) s.1 s.2) (by omega) e
  subst h1
  have hJ := (enumq_spec (fix := fix) (face := face) s.1 s.2).1
  have := (cd.JS_sub isSmall s.1.1 hJ).2.1
  apply this
  rw [h3]
  exact Finset.mem_image_of_mem _ (Finset.mem_univ l)

theorem hXI_dep (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (θ : Jr (Kq fix face π0 (cd.JS isSmall)) → Bool) (x : Iv fix face) (α α' : Iv fix face → ℝ)
    (h : ∀ b, b ∉ Finset.univ.image (xθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ) →
      α b = α' b) :
    hXI cd isSmall fix face β θ x α = hXI cd isSmall fix face β θ x α' := by
  have hinj := elim_injective_I (fix := fix) (face := face) (cd_hJS cd isSmall)
  unfold hXI
  by_cases hx : ∃ s, xθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ s = x
  · rw [dif_pos hx, dif_pos hx]
    have h1 : ∀ l b, extI fix face β α (atomAt π0 hx.choose.1.1 b (cd.r' hx.choose.1.1 l)) =
        extI fix face β α' (atomAt π0 hx.choose.1.1 b (cd.r' hx.choose.1.1 l)) := fun l b =>
      extI_congr fun hb => h _ (sel_not_XI cd isSmall θ _ l b _ rfl)
    have h2 : extI fix face β α (yθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ hx.choose).1 =
        extI fix face β α' (yθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ hx.choose).1 := by
      refine extI_congr fun hb => h _ fun hmem => ?_
      obtain ⟨s', _, hs'⟩ := Finset.mem_image.mp hmem
      exact yθ_ne_xθ _ _ hinj θ _ _ (by rw [hs'])
    simp only [h1, h2]
  · rw [dif_neg hx, dif_neg hx]

end centers

/-! ### Localization and the class bound -/

theorem loc_atomI (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d)
    (hamp : SplicedAmplitudeBounds G D) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (hδ : 0 ≤ δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π0 : PF G)
    (cd : CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1))
    (isSmall : LQ G → Prop) (hsm : ∀ S, isSmall S → scales S.1 < 1)
    (θ : Jr (Kq fix face π0 (cd.JS isSmall)) → Bool) (s : Jr (Kq fix face π0 (cd.JS isSmall)))
    (α' : Iv fix face → ℝ) (hα' : α' ∈ Wnb (clsI D scales L γ η δ base roots π0 fix face β)) :
    |α' (xθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ s) -
      hXI cd isSmall fix face β θ (xθ (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) θ s) α'| ≤
      rhoS d L γ δ (scales s.1.1.1) := by
  have hinj := elim_injective_I (fix := fix) (face := face) (cd_hJS cd isSmall)
  obtain ⟨α₀, hα₀, hcl⟩ := extI_close hα'
  set ua := uaI fix face π0 (cd.JS isSmall)
  set va := vaI fix face π0 (cd.JS isSmall)
  set e := enumq fix face π0 (cd.JS isSmall) s.1 s.2 with he
  have hJ := (enumq_spec (fix := fix) (face := face) s.1 s.2).1
  have hjs := cd.JS_sub isSmall s.1.1 hJ
  have hI : e ∈ Finset.Icc 1 (π0.m s.1.1 - 1) := by rw [Finset.mem_Icc]; omega
  have hS := loc_S hp hL D hamp scales γ η δ hδ base roots π0 cd (extI fix face β α') α₀ hα₀ hcl s.1.1
    (hsm _ hjs.2.2) e hI
  have hex : ∃ s', xθ ua va θ s' = xθ ua va θ s := ⟨s, rfl⟩
  have hch : hex.choose = s := xθ_injective _ _ hinj θ hex.choose_spec
  unfold hXI
  rw [dif_pos hex, hch]
  have hx := extI_free (β := β) α' (xθ ua va θ s)
  have hsum : extI fix face β α' (xθ ua va θ s).1 + extI fix face β α' (yθ ua va θ s).1 =
      extI fix face β α' (rowN (π0.u s.1.1) e) + extI fix face β α' (rowN (π0.v s.1.1) e) := by
    unfold xθ yθ
    cases θ s
    · simp only [Bool.false_eq_true, if_false]
      rw [show (va s).1 = rowN (π0.v s.1.1) e from rfl, show (ua s).1 = rowN (π0.u s.1.1) e from rfl]; ring
    · simp only [if_true]
      rw [show (va s).1 = rowN (π0.v s.1.1) e from rfl, show (ua s).1 = rowN (π0.u s.1.1) e from rfl]
  have hat : ∀ l, extI fix face β α' (atomAt π0 s.1.1 true (cd.r' s.1.1 l)) +
      extI fix face β α' (atomAt π0 s.1.1 false (cd.r' s.1.1 l)) =
      extI fix face β α' (rowN (π0.u s.1.1) (cd.r' s.1.1 l)) + extI fix face β α' (rowN (π0.v s.1.1) (cd.r' s.1.1 l)) := by
    intro l; simp [atomAt]
  simp only [hat]
  have key : α' (xθ ua va θ s) - (cI fix face β (xθ ua va θ s) +
      ((∑ l, cd.cc s.1.1 e l * (extI fix face β α' (rowN (π0.u s.1.1) (cd.r' s.1.1 l)) +
        extI fix face β α' (rowN (π0.v s.1.1) (cd.r' s.1.1 l)))) + cd.dd s.1.1 e) -
      extI fix face β α' (yθ ua va θ s).1) =
      (extI fix face β α' (rowN (π0.u s.1.1) e) + extI fix face β α' (rowN (π0.v s.1.1) e)) -
        ∑ l, cd.cc s.1.1 e l * (extI fix face β α' (rowN (π0.u s.1.1) (cd.r' s.1.1 l)) +
          extI fix face β α' (rowN (π0.v s.1.1) (cd.r' s.1.1 l))) - cd.dd s.1.1 e := by
    rw [← hsum, hx]; ring
  rw [key]
  unfold rhoS
  exact hS

/-- **The class bound on the clocks** (main's `class_bound`, with the segments of `Rungs`). -/
theorem class_fourierI (hp : G.IsPlain) {L : ℝ} (hL : 0 < L) (D : SplicedKernelData G d)
    (hamp : SplicedAmplitudeBounds G D) (scales : Finset (GBranch G.tree) → ℝ) (γ η δ : ℝ) (hδ : 0 ≤ δ)
    (base : Mom d) (roots : Fin w → (Fin d → ℤ)) (π0 : PF G)
    (cd : CD G D L γ δ base roots hp π0 (fun S => 8 * δ * L ^ (2 * γ) * scales S.1))
    (isSmall : LQ G → Prop) (hsm : ∀ S, isSmall S → scales S.1 < 1)
    (hF : FaceOK fix face) (β : GBranch G.tree → ℝ) (layer : GBranch G.tree → ℕ) (rootTime : Fin w → ℝ)
    (Dt : ℝ) (hDt0 : 0 ≤ Dt) (hDt : ∀ v, (layer v : ℝ) + 2 ≤ Dt) (A : Finset (Iv fix face)) :
    ∫⁻ α in Wnb (clsI D scales L γ η δ base roots π0 fix face β),
        ‖Phi (Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)) (lsF layer fix face) A α‖ₑ ≤
      2 ^ Fintype.card (Jr (Kq fix face π0 (cd.JS isSmall))) *
        ((∏ s : Jr (Kq fix face π0 (cd.JS isSmall)), ENNReal.ofReal (2 * rhoS d L γ δ (scales s.1.1.1))) *
          ((∏ q : SegQ π0, ENNReal.ofReal (2 ^ (Kq fix face π0 (cd.JS isSmall) q) *
              Dt ^ (Kq fix face π0 (cd.JS isSmall) q) / (Nat.factorial (Kq fix face π0 (cd.JS isSmall) q) : ℝ))) *
            ENNReal.ofReal (Real.pi ^ Fintype.card (Iv fix face) *
              3 ^ (Fintype.card (Iv fix face) - Fintype.card (Jr (Kq fix face π0 (cd.JS isSmall))))) *
            (2 * ENNReal.ofReal (2 * Real.arsinh (Mv d L) + 1)) ^
              (Fintype.card (Iv fix face) - Fintype.card (Jr (Kq fix face π0 (cd.JS isSmall)))))) := by
  obtain ⟨Sy, hSy, hKc, hSyW⟩ := exists_Sy hp hL D hamp scales γ η δ base roots
  have hJS := cd_hJS cd isSmall
  have hinj := elim_injective_I (fix := fix) (face := face) hJS
  have hbox : ∀ a : Iv fix face, 0 ≤ lsF layer fix face a ∧ lsF layer fix face a + 1 ≤ Dt := by
    intro a
    have h1 := layer_le_lsF layer a
    have h2 := lsF_le layer a
    have h3 := hDt a.1
    have h0 : (0 : ℝ) ≤ layer a.1 := Nat.cast_nonneg _
    exact ⟨h0.trans h1, by linarith⟩
  refine class_bound (chF fix face) (depF fix face) (chF_hdep hF) (chF_huniq hF)
    (uaI fix face π0 (cd.JS isSmall)) (vaI fix face π0 (cd.JS isSmall)) hinj (lsF layer fix face)
    (capF layer rootTime fix face) Dt hDt0 hbox (fun t ht q => hval_seg hF hJS t ht q) A
    (SyI Sy fix face β) (fun a => measurableSet_SyI hSy a) (ENNReal.ofReal (2 * Real.arsinh (Mv d L) + 1))
    (fun a β' => lintegral_SyI hSy hKc a β') (fun s => rhoS d L γ δ (scales s.1.1.1))
    (Wnb (clsI D scales L γ η δ base roots π0 fix face β)) ?_
  intro θ
  refine ⟨hXI cd isSmall fix face β θ, hXI_measurable cd isSmall θ,
    fun x α α' h => hXI_dep cd isSmall θ x α α' h, fun α' hα' => ⟨fun b _ => ?_, fun s => ?_⟩⟩
  · obtain ⟨α₀, hα₀, hcl⟩ := extI_close hα'
    have := hSyW α₀ (clsPF_subset_spectrum D scales L γ η δ base roots π0 hα₀) (extI fix face β α') hcl b.1
    rw [extI_free] at this
    exact this
  · exact loc_atomI hp hL D hamp scales γ η δ hδ base roots π0 cd isSmall hsm θ s α' hα'

end WaveTurbulence.Flower.FinalMKPin
