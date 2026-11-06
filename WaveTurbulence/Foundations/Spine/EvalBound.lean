/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.EvalOps
public import WaveTurbulence.Foundations.Spine.SNormOps
/-! AMEND6' (design P*, F1, F2): per-type norm bookkeeping for the operation recursion.

At the pair type `(j, j')` only the derivatives and the forms `M^{(j0)}` with exactly one of `j, j'` equal to `j0` act
(`TOp.acts`); the others are the identity. `Inv` is the invariant "regular at the levels of the remaining acting
operations": each acting operation costs one derivative or one decay power, and enlarges the high bound `u` by the
factor `1 + x kappa` and the low bound `c` by `x kappa u` (`x` bounds the step `|mu|`). -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset CentralDiff
open scoped ENNReal

theorem SNormR_mono_bound {d A B A' B' : ℕ} (hA : A' ≤ A) (hB : B' ≤ B) (f : Mom d → ℝ) (hf : ContDiff ℝ A f)
    (C : ℝ) (hC : 0 ≤ C) (h : SNormR A B f ≤ ENNReal.ofReal C) : SNormR A' B' f ≤ ENNReal.ofReal C :=
  SNorm_mono_bound hA hB _ (Complex.ofRealCLM.contDiff.comp hf) C hC h

/-- The coefficient of the root form `M^{(j0)}` at the pair type `(j, j')`. -/
@[expose] def TOp.coef {d w : ℕ} (j j' : Fin w) : TOp d w → ℝ
  | .der _ => 0
  | .form j0 _ => (if j = j0 then (1 : ℝ) else 0) - (if j' = j0 then (1 : ℝ) else 0)

/-- Derivatives always cost one derivative level; a form costs one decay power where it acts. -/
@[expose] def TOp.dc {d w : ℕ} : TOp d w → ℕ
  | .der _ => 1
  | .form _ _ => 0

@[expose] noncomputable def TOp.fc {d w : ℕ} (j j' : Fin w) : TOp d w → ℕ
  | .der _ => 0
  | .form j0 i => if TOp.coef (d := d) j j' (.form j0 i) = 0 then 0 else 1

@[expose] def dcnt {d w : ℕ} (os : List (TOp d w)) : ℕ := (os.map TOp.dc).sum
@[expose] noncomputable def fcnt {d w : ℕ} (j j' : Fin w) (os : List (TOp d w)) : ℕ := (os.map (TOp.fc j j')).sum

/-- The per-type norm invariant of a profile `h` before the operations `os`. -/
@[expose] def Inv {d w : ℕ} (p A B : ℕ) (os : List (TOp d w)) (u c : ℝ) (h : TProf d w) : Prop :=
  ∀ q ≤ p, ∀ j j', ContDiff ℝ (A + dcnt os : ℕ) (h q j j') ∧
    SNormR (A + dcnt os) (B + fcnt j j' os) (h q j j') ≤ ENNReal.ofReal u ∧
    SNormR A B (h q j j') ≤ ENNReal.ofReal c

theorem dcnt_der {d w : ℕ} (i : Fin d) (rest : List (TOp d w)) :
    dcnt (TOp.der i :: rest) = dcnt rest + 1 := by
  simp [dcnt, TOp.dc, add_comm]

theorem dcnt_form {d w : ℕ} (j0 : Fin w) (i : Fin d) (rest : List (TOp d w)) :
    dcnt (TOp.form j0 i :: rest) = dcnt rest := by
  simp [dcnt, TOp.dc]

theorem fcnt_der {d w : ℕ} (j j' : Fin w) (i : Fin d) (rest : List (TOp d w)) :
    fcnt j j' (TOp.der i :: rest) = fcnt j j' rest := by
  simp [fcnt, TOp.fc]

theorem fcnt_form {d w : ℕ} (j j' j0 : Fin w) (i : Fin d) (rest : List (TOp d w)) :
    fcnt j j' (TOp.form j0 i :: rest) =
      fcnt j j' rest + (if TOp.coef (d := d) j j' (.form j0 i) = 0 then 0 else 1) := by
  simp only [fcnt, TOp.fc, List.map_cons, List.sum_cons]
  omega

theorem contDiff_coord {d : ℕ} (i : Fin d) (A : ℕ) : ContDiff ℝ A (fun y : Mom d => y i) :=
  (EuclideanSpace.proj i : Mom d →L[ℝ] ℝ).contDiff

theorem abs_coef_le {d w : ℕ} (j j' j0 : Fin w) (i : Fin d) : |TOp.coef (d := d) j j' (.form j0 i)| ≤ 1 := by
  unfold TOp.coef
  by_cases h1 : j = j0 <;> by_cases h2 : j' = j0 <;> simp [h1, h2]

theorem Inv.step {d w : ℕ} (hd : 1 ≤ d) {p A B : ℕ} {O : TOp d w} {rest : List (TOp d w)} {u c x κ : ℝ}
    (hu : 0 ≤ u) (hc : 0 ≤ c) (hx : 0 ≤ x) (μ : ℝ) (hμ : |μ| ≤ x)
    (hκ1 : (d : ℝ) ^ (A + dcnt (O :: rest)) ≤ κ)
    (hκ2 : (2 : ℝ) ^ (A + dcnt rest) * (d : ℝ) ^ (A + dcnt rest) ≤ κ)
    {h : TProf d w} (hh : Inv p A B (O :: rest) u c h) :
    Inv p A B rest ((1 + x * κ) * u) (c + x * κ * u) (TProf.perturb h (O.apply h) μ) := by
  intro q hq j j'
  obtain ⟨hcd, hu', hc'⟩ := hh q hq j j'
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hκ0 : 0 ≤ κ := le_trans (by positivity) hκ1
  have hxκ : 0 ≤ x * κ := mul_nonneg hx hκ0
  have hμ0 : 0 ≤ |μ| := abs_nonneg μ
  have hcc : 0 ≤ c + x * κ * u := by positivity
  have hmono1 : ∀ n m : ℕ, n ≤ m → (d : ℝ) ^ n ≤ (d : ℝ) ^ m := fun n m h => pow_le_pow_right₀ hd1 h
  have hmono2 : ∀ n m : ℕ, n ≤ m → (2 : ℝ) ^ n * (d : ℝ) ^ n ≤ (2 : ℝ) ^ m * (d : ℝ) ^ m := fun n m h =>
    mul_le_mul (pow_le_pow_right₀ (by norm_num) h) (pow_le_pow_right₀ hd1 h) (by positivity) (by positivity)
  set f := h q j j' with hf
  cases O with
  | der i =>
    have e : A + dcnt (TOp.der i :: rest) = (A + dcnt rest) + 1 := by rw [dcnt_der]; ring
    rw [e] at hcd hu' hκ1
    rw [fcnt_der] at hu'
    have hcdA : ContDiff ℝ (A + dcnt rest : ℕ) f := hcd.of_le (by exact_mod_cast Nat.le_succ _)
    have hder : ContDiff ℝ (A + dcnt rest : ℕ) (realPartialMom i f) := contDiff_realPartialMom i f hcd
    have hlowf : SNormR (A + dcnt rest) (B + fcnt j j' rest) f ≤ ENNReal.ofReal u :=
      SNormR_mono_bound (Nat.le_succ _) le_rfl f hcd u hu hu'
    have hD := SNormR_realPartialMom_bound hd i f hcd u hu hu'
    have hsum := SNormR_add_smul_le f (realPartialMom i f) μ hcdA hder u _ hu (by positivity) hlowf hD
    refine ⟨hcdA.add (contDiff_const.mul hder), hsum.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
    · have : |μ| * ((d : ℝ) ^ (A + dcnt rest + 1) * u) ≤ x * κ * u := by
        calc _ ≤ x * ((d : ℝ) ^ (A + dcnt rest + 1) * u) :=
              mul_le_mul_of_nonneg_right hμ (by positivity)
          _ ≤ x * (κ * u) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκ1 hu) hx
          _ = _ := by ring
      nlinarith
    · -- low level (A, B)
      have hcdA0 : ContDiff ℝ A f := hcdA.of_le (by exact_mod_cast Nat.le_add_right _ _)
      have hcd1 : ContDiff ℝ (A + 1) f := hcd.of_le (by exact_mod_cast Nat.add_le_add_right (Nat.le_add_right _ _) 1)
      have hu1 : SNormR (A + 1) B f ≤ ENNReal.ofReal u :=
        SNormR_mono_bound (Nat.add_le_add_right (Nat.le_add_right _ _) 1) (Nat.le_add_right _ _) f hcd u hu hu'
      have hD0 := SNormR_realPartialMom_bound hd i f hcd1 u hu hu1
      have hder0 : ContDiff ℝ A (realPartialMom i f) := contDiff_realPartialMom i f hcd1
      have hsum0 := SNormR_add_smul_le f (realPartialMom i f) μ hcdA0 hder0 c _ hc (by positivity) hc' hD0
      refine hsum0.trans (ENNReal.ofReal_le_ofReal ?_)
      have h1 : (d : ℝ) ^ (A + 1) ≤ κ := (hmono1 _ _ (Nat.add_le_add_left (Nat.le_add_left 1 _) A)).trans hκ1
      have : |μ| * ((d : ℝ) ^ (A + 1) * u) ≤ x * κ * u := by
        calc _ ≤ x * ((d : ℝ) ^ (A + 1) * u) := mul_le_mul_of_nonneg_right hμ (by positivity)
          _ ≤ x * (κ * u) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hu) hx
          _ = _ := by ring
      linarith
  | form j0 i =>
    rw [dcnt_form] at hcd hu' hκ1
    rw [fcnt_form] at hu'
    by_cases hz : TOp.coef (d := d) j j' (.form j0 i) = 0
    · have hz' : ((if j = j0 then (1 : ℝ) else 0) - (if j' = j0 then (1 : ℝ) else 0)) = 0 := hz
      have hpert : (TProf.perturb h ((TOp.form j0 i).apply h) μ) q j j' = f := by
        funext y
        show f y + μ * (((if j = j0 then (1 : ℝ) else 0) - (if j' = j0 then (1 : ℝ) else 0)) * y i * f y) = f y
        rw [hz']
        ring
      rw [hpert]
      rw [if_pos hz, Nat.add_zero] at hu'
      refine ⟨hcd, hu'.trans (ENNReal.ofReal_le_ofReal ?_), hc'.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      · nlinarith [mul_nonneg hxκ hu]
      · nlinarith [mul_nonneg hxκ hu]
    · rw [if_neg hz, ← Nat.add_assoc] at hu'
      have hcdA0 : ContDiff ℝ A f := hcd.of_le (by exact_mod_cast Nat.le_add_right _ _)
      have hdop : ContDiff ℝ (A + dcnt rest : ℕ)
          (fun y : Mom d => TOp.coef (d := d) j j' (.form j0 i) * y i * f y) :=
        (contDiff_const.mul (contDiff_coord i _)).mul hcd
      have hm1 := SNormR_coord_mul_le (B := B + fcnt j j' rest) hd i (TOp.coef (d := d) j j' (.form j0 i))
        (abs_coef_le j j' j0 i) f hcd u hu hu'
      have hlowf : SNormR (A + dcnt rest) (B + fcnt j j' rest) f ≤ ENNReal.ofReal u :=
        SNormR_mono_bound le_rfl (Nat.le_succ _) f hcd u hu hu'
      have hsum := SNormR_add_smul_le f _ μ hcd hdop u _ hu (by positivity) hlowf hm1
      refine ⟨hcd.add (contDiff_const.mul hdop), hsum.trans (ENNReal.ofReal_le_ofReal ?_), ?_⟩
      · have : |μ| * ((2 : ℝ) ^ (A + dcnt rest) * (d : ℝ) ^ (A + dcnt rest) * u) ≤ x * κ * u := by
          calc _ ≤ x * ((2 : ℝ) ^ (A + dcnt rest) * (d : ℝ) ^ (A + dcnt rest) * u) :=
                mul_le_mul_of_nonneg_right hμ (by positivity)
            _ ≤ x * (κ * u) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hκ2 hu) hx
            _ = _ := by ring
        nlinarith
      · have hu1 : SNormR A (B + 1) f ≤ ENNReal.ofReal u :=
          SNormR_mono_bound (Nat.le_add_right _ _)
            (Nat.add_le_add_right (Nat.le_add_right B _) 1) f hcd u hu hu'
        have hop := SNormR_coord_mul_le (A := A) (B := B) hd i (TOp.coef (d := d) j j' (.form j0 i))
          (abs_coef_le j j' j0 i) f hcdA0 u hu hu1
        have hdop0 : ContDiff ℝ A (fun y : Mom d => TOp.coef (d := d) j j' (.form j0 i) * y i * f y) :=
          (contDiff_const.mul (contDiff_coord i _)).mul hcdA0
        have hsum0 := SNormR_add_smul_le f _ μ hcdA0 hdop0 c _ hc (by positivity) hc' hop
        refine hsum0.trans (ENNReal.ofReal_le_ofReal ?_)
        have h1 : (2 : ℝ) ^ A * (d : ℝ) ^ A ≤ κ :=
          (hmono2 _ _ (Nat.le_add_right _ _)).trans hκ2
        have : |μ| * ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) ≤ x * κ * u := by
          calc _ ≤ x * ((2 : ℝ) ^ A * (d : ℝ) ^ A * u) := mul_le_mul_of_nonneg_right hμ (by positivity)
            _ ≤ x * (κ * u) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hu) hx
            _ = _ := by ring
        linarith

/-- Bound of the recursion: if the leaf evaluations of every profile bounded by `B₀` at level `(A,B)` are at most `G`,
the recursion is at most `(sum_m |w_m/lam|)^{#ops} G`. -/
theorem evalOps_norm_le {d w : ℕ} (hd : 1 ≤ d) {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (V : TProf d w → Y) (M : ℕ) (lam : ℝ) {p A B : ℕ} (x κ B₀ G : ℝ) (hx : 0 ≤ x)
    (hxM : ∀ m ∈ Finset.range (2 * M + 1), |lam * ((m : ℝ) - M)| ≤ x)
    (Lmax : ℕ) (hL : ∀ a ≤ Lmax, (d : ℝ) ^ a ≤ κ ∧ (2 : ℝ) ^ a * (d : ℝ) ^ a ≤ κ)
    (hG : ∀ g : TProf d w, (∀ q ≤ p, ∀ j j', SNormR A B (g q j j') ≤ ENNReal.ofReal B₀) → ‖V g‖ ≤ G) :
    ∀ (os : List (TOp d w)) (h : TProf d w) (u c : ℝ), 0 ≤ u → 0 ≤ c → A + dcnt os ≤ Lmax →
      Inv p A B os u c h → c + u * ((1 + x * κ) ^ os.length - 1) ≤ B₀ →
      ‖evalOps V M lam os h‖ ≤ (∑ m ∈ Finset.range (2 * M + 1), |cw M m / lam|) ^ os.length * G := by
  intro os
  induction os with
  | nil =>
    intro h u c hu hc _ hI hB
    simp only [evalOps_nil, List.length_nil, pow_zero, one_mul]
    refine hG h fun q hq j j' => ?_
    have := (hI q hq j j').2.2
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    simpa using hB
  | cons O rest ih =>
    intro h u c hu hc hLm hI hB
    rw [evalOps_cons]
    have hx0 := hx
    have hκ0 : 0 ≤ κ := by
      have := (hL 0 (Nat.zero_le _)).1
      simpa using this.trans' (by norm_num : (0:ℝ) ≤ 1)
    have hdc : dcnt rest ≤ dcnt (O :: rest) := by
      cases O <;> simp [dcnt_der, dcnt_form]
    refine (norm_sum_le _ _).trans ?_
    rw [List.length_cons, pow_succ, mul_comm _ (∑ m ∈ Finset.range (2 * M + 1), |cw M m / lam|), mul_assoc,
      Finset.sum_mul]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [norm_smul, Real.norm_eq_abs]
    have hstep := Inv.step hd (O := O) (rest := rest) (u := u) (c := c) (x := x) (κ := κ) hu hc hx
      (lam * ((m : ℝ) - M)) (hxM m hm) (hL _ hLm).1
      (hL _ (by omega)).2 hI
    have := ih _ ((1 + x * κ) * u) (c + x * κ * u) (by positivity) (by positivity)
      (by omega) hstep (by
        have e : (1 + x * κ) ^ (rest.length + 1) = (1 + x * κ) * (1 + x * κ) ^ rest.length := by ring
        rw [List.length_cons, e] at hB
        nlinarith [hB])
    rw [mul_comm ((∑ m ∈ Finset.range (2 * M + 1), |cw M m / lam|) ^ rest.length) G] at this ⊢
    exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using this) (abs_nonneg _)

end WaveTurbulence.LGSpine
