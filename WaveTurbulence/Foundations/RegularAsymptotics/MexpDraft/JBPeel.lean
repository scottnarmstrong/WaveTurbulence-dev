/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.MexpDraft.EFinite
public import WaveTurbulence.Foundations.Cancel.TimeSplit

/-!
# The time factors `𝒥ℬ*_𝒬` split by their latest time

B2 defines `𝒥ℬ*_𝒬(t, s)` of a dominant couple by the recursion (regref2-0)–(regref2-2) (DH21 (recurtype1),
(recurtype2) with `Z`-independent values, DH21 Prop 7.5 corrected, CANCEL7). Here:

* `JB_continuous`, `JBchain_continuous`: joint continuity.
* `JBchain_integral_swap`: Fubini through a chain integral.
* `prepP`, `prepM`: put a new top pair on the `+` (resp. `-`) chain of an enhanced code;
  `JB_prepP`: `𝒥ℬ*(t, s) = ∫_r^t P(u) 𝒥ℬ*'(u, s) du`; `JB_prepM`: `𝒥ℬ*(t, s) = ∫_r^s P(u) 𝒥ℬ*'(t, u) du`.
* **`JB_diag`**: for a type 2 code, `𝒥ℬ*(t, t)` is the sum over the two chains of
  `∫_r^t P(u) 𝒥ℬ*_{peeled}(u, u) du`, the chain whose top pair carries the latest time being peeled. This is the
  ordering argument (`(A, B)` partitions) of DH21 Props 7.8 and 7.10, one time at a time.
-/

@[expose] public section

open MeasureTheory Set Filter intervalIntegral

namespace WaveTurbulence.Mexp

open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.Cancel

variable (r : ℝ)

/-! ### Continuity -/

mutual
theorem JB_continuous : (Q : RegCpl) → Continuous (fun p : ℝ × ℝ => Q.JB r p.1 p.2)
  | .triv => continuous_const
  | .type1 _ Q₁ Q₂ Q₃ => by
    have h : Continuous fun τ : ℝ => Q₁.JB r τ τ * Q₂.JB r τ τ * Q₃.JB r τ τ := by
      have d : Continuous fun τ : ℝ => (τ, τ) := continuous_id.prodMk continuous_id
      exact (((JB_continuous Q₁).comp d).mul ((JB_continuous Q₂).comp d)).mul
        ((JB_continuous Q₃).comp d)
    simp only [RegCpl.JB]
    exact continuous_const.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_ : ℝ × ℝ) τ => Q₁.JB r τ τ * Q₂.JB r τ τ * Q₃.JB r τ τ)
      (h.comp continuous_snd) (continuous_fst.min continuous_snd))
  | .type2 Xp Xm Qlp => by
    simp only [RegCpl.JB]
    have h1 : Continuous fun p : ℝ × ℝ => Xm.JBchain r r p.2 (fun sm => Qlp.JB r p.1 sm) :=
      JBchain_continuous Xm r (G := fun tm sm => Qlp.JB r tm sm) (JB_continuous Qlp)
    have h2 := JBchain_continuous Xp r (G := fun s tm => Xm.JBchain r r s (fun sm => Qlp.JB r tm sm))
      (h1.comp continuous_swap)
    exact h2.comp continuous_swap

theorem JBchain_continuous : (X : RegChain) → (lo : ℝ) → {G : ℝ → ℝ → ℝ} →
    Continuous (Function.uncurry G) →
    Continuous (fun p : ℝ × ℝ => X.JBchain r lo p.2 (G p.1))
  | .nil, _, _, hG => hG
  | .pair _ Qr Qg _ rest, lo, G, hG => by
    simp only [RegChain.JBchain]
    have d : Continuous fun τ : ℝ => (τ, τ) := continuous_id.prodMk continuous_id
    have hP : Continuous fun τ : ℝ => Qr.JB r τ τ * Qg.JB r τ τ :=
      ((JB_continuous Qr).comp d).mul ((JB_continuous Qg).comp d)
    have hR := JBchain_continuous rest lo hG
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : ℝ × ℝ) τ => Qr.JB r τ τ * Qg.JB r τ τ * rest.JBchain r lo τ (G p.1)) ?_
      continuous_snd
    exact (hP.comp continuous_snd).mul (hR.comp (continuous_fst.fst.prodMk continuous_snd))
end

theorem JB_diag_continuous (Q : RegCpl) : Continuous fun τ : ℝ => Q.JB r τ τ :=
  (JB_continuous r Q).comp (continuous_id.prodMk continuous_id)

/-! ### Chain integrals: scalars, Fubini, locality -/

theorem JBchain_const_mul : (X : RegChain) → (lo t c : ℝ) → (G : ℝ → ℝ) →
    X.JBchain r lo t (fun x => c * G x) = c * X.JBchain r lo t G
  | .nil, _, _, _, _ => rfl
  | .pair _ Qr Qg _ rest, lo, t, c, G => by
    simp only [RegChain.JBchain, JBchain_const_mul rest]
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext τ; ring

theorem JBchain_integral_swap : (X : RegChain) → (lo t a b : ℝ) → {g : ℝ → ℝ → ℝ} →
    Continuous (Function.uncurry g) →
    X.JBchain r lo t (fun tm => ∫ u in a..b, g u tm) = ∫ u in a..b, X.JBchain r lo t (g u)
  | .nil, _, _, _, _, _, _ => rfl
  | .pair _ Qr Qg _ rest, lo, t, a, b, g, hg => by
    simp only [RegChain.JBchain]
    rw [show (fun τ => Qr.JB r τ τ * Qg.JB r τ τ * rest.JBchain r lo τ (fun tm => ∫ u in a..b, g u tm)) =
        fun τ => ∫ u in a..b, Qr.JB r τ τ * Qg.JB r τ τ * rest.JBchain r lo τ (g u) by
      funext τ
      rw [JBchain_integral_swap rest lo τ a b hg, ← intervalIntegral.integral_const_mul]]
    refine integral_rect_swap ?_ lo t a b
    have hP : Continuous fun τ : ℝ => Qr.JB r τ τ * Qg.JB r τ τ :=
      (JB_diag_continuous r Qr).mul (JB_diag_continuous r Qg)
    exact (hP.comp continuous_fst).mul ((JBchain_continuous r rest lo hg).comp continuous_swap)

theorem JBchain_congr : (X : RegChain) → (lo t : ℝ) → {G G' : ℝ → ℝ} →
    (∀ x ∈ uIcc lo t, G x = G' x) → X.JBchain r lo t G = X.JBchain r lo t G'
  | .nil, lo, t, _, _, h => h t right_mem_uIcc
  | .pair _ Qr Qg _ rest, lo, t, G, G', h => by
    simp only [RegChain.JBchain]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [JBchain_congr rest lo τ fun x hx => h x (uIcc_subset_uIcc_left hτ hx)]

/-! ### Couples with one empty chain -/

/-- `𝒥ℬ*` of a trivial or type 1 code is a function of `min(t, s)`. -/
theorem JB_min {Q : RegCpl} (hQ : Q.isType2 = false) (t s : ℝ) :
    Q.JB r t s = Q.JB r (min t s) (min t s) := by
  cases Q with
  | triv => rfl
  | type1 c Q₁ Q₂ Q₃ => simp [RegCpl.JB]
  | type2 => simp [RegCpl.isType2] at hQ

/-! ### Enhanced codes: prepending a pair to a chain -/

/-- `𝒥ℬ*` of an enhanced code. -/
noncomputable def ECpl.JB (e : ECpl) (t s : ℝ) : ℝ := e.code.JB r t s

/-- Put a new top pair `(m, 𝙸, e_r, e_g)` on the `+` chain of `e'`. -/
def prepP (m : MiniTreeCode) (I : Bool) (er eg : ECpl) : ECpl → ECpl
  | .type2 X Y L => .type2 (.pair m I er eg X) Y L
  | .triv => .type2 (.pair m I er eg .nil) .nil .triv
  | .type1 c Q₁ Q₂ Q₃ => .type2 (.pair m I er eg .nil) .nil (.type1 c Q₁ Q₂ Q₃)

/-- Put a new top pair on the `-` chain of `e'`. -/
def prepM (m : MiniTreeCode) (I : Bool) (er eg : ECpl) : ECpl → ECpl
  | .type2 X Y L => .type2 X (.pair m I er eg Y) L
  | .triv => .type2 .nil (.pair m I er eg .nil) .triv
  | .type1 c Q₁ Q₂ Q₃ => .type2 .nil (.pair m I er eg .nil) (.type1 c Q₁ Q₂ Q₃)

/-- **Prepending to the `+` chain**: `𝒥ℬ*(t, s) = ∫_r^t 𝒥ℬ*_{e_r}(u,u) 𝒥ℬ*_{e_g}(u,u) 𝒥ℬ*_{e'}(u, s) du`. -/
theorem JB_prepP (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) (t s : ℝ) :
    (prepP m I er eg e').JB r t s =
      ∫ u in r..t, er.JB r u u * eg.JB r u u * e'.JB r u s := by
  cases e' <;> rfl

/-- **Prepending to the `-` chain**: `𝒥ℬ*(t, s) = ∫_r^s 𝒥ℬ*_{e_r}(u,u) 𝒥ℬ*_{e_g}(u,u) 𝒥ℬ*_{e'}(t, u) du`. -/
theorem JB_prepM (m : MiniTreeCode) (I : Bool) (er eg e' : ECpl) (t s : ℝ) :
    (prepM m I er eg e').JB r t s =
      ∫ u in r..s, er.JB r u u * eg.JB r u u * e'.JB r t u := by
  cases e' with
  | triv => rfl
  | type1 => rfl
  | type2 X Y L =>
    simp only [prepM, ECpl.JB, ECpl.code, EChain.code, RegCpl.JB, RegChain.JBchain]
    have hg : Continuous (Function.uncurry fun u tm =>
        er.code.JB r u u * eg.code.JB r u u * Y.code.JBchain r r u (fun sm => L.code.JB r tm sm)) := by
      have hP : Continuous fun u : ℝ => er.code.JB r u u * eg.code.JB r u u :=
        (JB_diag_continuous r _).mul (JB_diag_continuous r _)
      exact (hP.comp continuous_fst).mul
        ((JBchain_continuous r Y.code r (JB_continuous r L.code)).comp continuous_swap)
    rw [JBchain_integral_swap r X.code r t r s hg]
    congr 1; funext u
    rw [← JBchain_const_mul]

/-! ### The diagonal split -/

/-- Rebuild a couple from two chains and a tail (`Q_lp` itself if both chains are empty). -/
def mk2 (X Y : EChain) (L : ECpl) : ECpl := if X.isNil && Y.isNil then L else .type2 X Y L

theorem prepP_mk2 (m : MiniTreeCode) (I : Bool) (er eg : ECpl) (X Y : EChain) {L : ECpl}
    (hL : L.isType2 = false) : prepP m I er eg (mk2 X Y L) = .type2 (.pair m I er eg X) Y L := by
  unfold mk2
  cases X <;> cases Y <;> cases L <;> simp_all [EChain.isNil, ECpl.isType2, prepP]

theorem prepM_mk2 (m : MiniTreeCode) (I : Bool) (er eg : ECpl) (X Y : EChain) {L : ECpl}
    (hL : L.isType2 = false) : prepM m I er eg (mk2 X Y L) = .type2 X (.pair m I er eg Y) L := by
  unfold mk2
  cases X <;> cases Y <;> cases L <;> simp_all [EChain.isNil, ECpl.isType2, prepM]

/-- With an empty `-` chain, `𝒥ℬ*(t, s) = 𝒥ℬ*(t, t)` for `r ≤ t ≤ s`. -/
theorem JB_minusNil (X : EChain) {L : ECpl} (hL : L.isType2 = false) {t s : ℝ} (hrt : r ≤ t)
    (hts : t ≤ s) : (mk2 X .nil L).JB r t s = (mk2 X .nil L).JB r t t := by
  have hL' : L.code.isType2 = false := by rw [ECpl.isType2_code, hL]
  unfold mk2
  cases X with
  | nil =>
    simp only [EChain.isNil, Bool.and_self, ↓reduceIte, ECpl.JB]
    rw [JB_min r hL' t s, min_eq_left hts]
  | pair m I er eg X =>
    simp only [EChain.isNil, Bool.false_and, Bool.false_eq_true, ↓reduceIte, ECpl.JB, ECpl.code,
      EChain.code, RegCpl.JB]
    refine JBchain_congr r _ r t fun x hx => ?_
    rw [uIcc_of_le hrt] at hx
    simp only [RegChain.JBchain]
    rw [JB_min r hL', JB_min r hL' x t, min_eq_left (hx.2.trans hts), min_eq_left hx.2]

/-- With an empty `+` chain, `𝒥ℬ*(t, s) = 𝒥ℬ*(s, s)` for `r ≤ s ≤ t`. -/
theorem JB_plusNil (Y : EChain) {L : ECpl} (hL : L.isType2 = false) {t s : ℝ} (hrs : r ≤ s)
    (hst : s ≤ t) : (mk2 .nil Y L).JB r t s = (mk2 .nil Y L).JB r s s := by
  have hL' : L.code.isType2 = false := by rw [ECpl.isType2_code, hL]
  unfold mk2
  cases Y with
  | nil =>
    simp only [EChain.isNil, Bool.and_self, ↓reduceIte, ECpl.JB]
    rw [JB_min r hL' t s, min_eq_right hst]
  | pair m I er eg Y =>
    simp only [EChain.isNil, Bool.and_false, Bool.false_eq_true, ↓reduceIte, ECpl.JB, ECpl.code,
      EChain.code, RegCpl.JB]
    show (RegChain.pair m er.code eg.code .nil Y.code).JBchain r r s (fun sm => L.code.JB r t sm) =
      (RegChain.pair m er.code eg.code .nil Y.code).JBchain r r s (fun sm => L.code.JB r s sm)
    refine JBchain_congr r _ r s fun x hx => ?_
    rw [uIcc_of_le hrs] at hx
    rw [JB_min r hL', JB_min r hL' s x, min_eq_right (hx.2.trans hst), min_eq_right hx.2]

/-- The `+` peeling term of a code: `∫_r^t P(u) 𝒥ℬ*_{peeled}(u, u) du` if the `+` chain is not empty. -/
noncomputable def plusTerm (t : ℝ) : ECpl → ℝ
  | .triv => 0
  | .type1 .. => 0
  | .type2 .nil _ _ => 0
  | .type2 (.pair _ _ er eg X) Y L =>
    ∫ u in r..t, er.JB r u u * eg.JB r u u * (mk2 X Y L).JB r u u

/-- The `-` peeling term. -/
noncomputable def minusTerm (t : ℝ) : ECpl → ℝ
  | .triv => 0
  | .type1 .. => 0
  | .type2 _ .nil _ => 0
  | .type2 X (.pair _ _ er eg Y) L =>
    ∫ u in r..t, er.JB r u u * eg.JB r u u * (mk2 X Y L).JB r u u

/-- **The diagonal split** (DH21 Props 7.8, 7.10, the ordering of the times of the two chains): for a
well-formed type 2 code and `r ≤ t`, `𝒥ℬ*(t, t)` is the sum of the two peeling terms. -/
theorem JB_diag (X Y : EChain) (L : ECpl) (hw : (ECpl.type2 X Y L).wf = true) {t : ℝ} (hrt : r ≤ t) :
    (ECpl.type2 X Y L).JB r t t = plusTerm r t (.type2 X Y L) + minusTerm r t (.type2 X Y L) := by
  simp only [ECpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hw
  have hL := hw.1.2
  have hnil := hw.2
  cases X with
  | nil =>
    cases Y with
    | nil => simp [EChain.isNil] at hnil
    | pair m I er eg Y =>
      simp only [plusTerm, minusTerm, zero_add]
      rw [← prepM_mk2 m I er eg .nil Y hL, JB_prepM]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hrt] at hu
      rw [JB_plusNil r Y hL hu.1 hu.2]
  | pair m I er eg X =>
    cases Y with
    | nil =>
      simp only [plusTerm, minusTerm, add_zero]
      rw [← prepP_mk2 m I er eg X .nil hL, JB_prepP]
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hrt] at hu
      rw [JB_minusNil r X hL hu.1 hu.2]
    | pair m' I' er' eg' Y =>
      simp only [plusTerm, minusTerm]
      -- the `+` top first: `𝒥ℬ*(t, t) = ∫_r^t P⁺(u) 𝒥ℬ*_{e⁺}(u, t) du`
      have hmk : mk2 X (.pair m' I' er' eg' Y) L = .type2 X (.pair m' I' er' eg' Y) L := by
        simp [mk2, EChain.isNil]
      have hmk' : mk2 (.pair m I er eg X) Y L = .type2 (.pair m I er eg X) Y L := by
        simp [mk2, EChain.isNil]
      rw [hmk, hmk', ← prepP_mk2 m I er eg X (.pair m' I' er' eg' Y) hL, JB_prepP, hmk]
      set B : ℝ → ℝ → ℝ := fun u v => (mk2 X Y L).JB r u v with hB
      set Pp : ℝ → ℝ := fun u => er.JB r u u * eg.JB r u u with hPp
      set Pm : ℝ → ℝ := fun v => er'.JB r v v * eg'.JB r v v with hPm
      have cB : Continuous (Function.uncurry B) := JB_continuous r _
      have cPp : Continuous Pp := (JB_diag_continuous r _).mul (JB_diag_continuous r _)
      have cPm : Continuous Pm := (JB_diag_continuous r _).mul (JB_diag_continuous r _)
      -- `𝒥ℬ*_{e⁺}(u, s) = ∫_r^s P⁻(v) B(u, v) dv`
      have hplus : ∀ u s, (ECpl.type2 X (.pair m' I' er' eg' Y) L).JB r u s =
          ∫ v in r..s, Pm v * B u v := by
        intro u s
        rw [← prepM_mk2 m' I' er' eg' X Y hL, JB_prepM]
      -- `𝒥ℬ*_{e⁻}(v, v) = ∫_r^v P⁺(u) B(u, v) du`
      have hminus : ∀ v, (ECpl.type2 (.pair m I er eg X) Y L).JB r v v =
          ∫ u in r..v, Pp u * B u v := by
        intro v
        rw [← prepP_mk2 m I er eg X Y hL, JB_prepP]
      simp only [hplus, hminus]
      have split : ∀ u ∈ uIcc r t, ∫ v in r..t, Pm v * B u v =
          (∫ v in r..u, Pm v * B u v) + ∫ v in u..t, Pm v * B u v := by
        intro u _
        have hc : Continuous fun v => Pm v * B u v :=
          cPm.mul (cB.comp (continuous_const.prodMk continuous_id))
        exact (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
          (hc.intervalIntegrable _ _)).symm
      rw [intervalIntegral.integral_congr (g := fun u => Pp u * (∫ v in r..u, Pm v * B u v) +
          Pp u * ∫ v in u..t, Pm v * B u v) fun u hu => by
        simp only
        rw [split u hu, mul_add]]
      have c1 : Continuous fun u => Pp u * ∫ v in r..u, Pm v * B u v :=
        cPp.mul (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun u v => Pm v * B u v) ((cPm.comp continuous_snd).mul cB) continuous_id)
      have c2 : Continuous fun u => Pp u * ∫ v in u..t, Pm v * B u v := by
        refine cPp.mul ?_
        have : (fun u => ∫ v in u..t, Pm v * B u v) =
            fun u => -∫ v in t..u, Pm v * B u v := by
          funext u; rw [intervalIntegral.integral_symm]
        rw [this]
        exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun u v => Pm v * B u v) ((cPm.comp continuous_snd).mul cB) continuous_id).neg
      rw [intervalIntegral.integral_add (c1.intervalIntegrable _ _) (c2.intervalIntegrable _ _)]
      congr 1
      have htri := integral_triangle_swap' (f := fun u v => Pp u * (Pm v * B u v))
        ((cPp.comp continuous_fst).mul ((cPm.comp continuous_snd).mul cB)) hrt
      rw [intervalIntegral.integral_congr (g := fun u => ∫ v in u..t, Pp u * (Pm v * B u v))
        fun u _ => by simp only; rw [intervalIntegral.integral_const_mul], htri]
      refine intervalIntegral.integral_congr fun v _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext u; ring

end WaveTurbulence.Mexp
