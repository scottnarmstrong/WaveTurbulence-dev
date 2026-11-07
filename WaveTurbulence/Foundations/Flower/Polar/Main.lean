/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Polar.Bound
public import WaveTurbulence.Foundations.Flower.Polar.Cost
public import WaveTurbulence.Foundations.Spine.GardenEval
/-! # FL-POLAR: external decay for flowers by the polarization device. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Polar
open Finset LGSpine

/-- The list of rounds: every tree `m` times. -/
def rep (w : ℕ) : ℕ → List (Fin w)
  | 0 => []
  | m + 1 => List.finRange w ++ rep w m

theorem rep_length (w m : ℕ) : (rep w m).length = m * w := by
  induction m with
  | zero => simp [rep]
  | succ m ih => simp [rep, ih, Nat.succ_mul]; ring

theorem count_rep {w : ℕ} (m : ℕ) (a : Fin w) : (rep w m).count a = m := by
  induction m with
  | zero => simp [rep]
  | succ m ih =>
    rw [rep, List.count_append, ih,
      List.count_eq_one_of_mem (List.nodup_finRange w) (List.mem_finRange a)]
    ring

theorem wcnt_le_count {w : ℕ} (js : List (Fin w)) (j1 j2 : Fin w) :
    wcnt js j1 j2 ≤ js.count j1 + js.count j2 := by
  induction js with
  | nil => simp [wcnt]
  | cons j js ih =>
    rw [wcnt_cons, List.count_cons, List.count_cons]
    have : tch j j1 j2 ≤ (if j == j1 then 1 else 0) + (if j == j2 then 1 else 0) := by
      unfold tch
      by_cases hi : (j1 = j ↔ j2 = j)
      · simp [hi]
      · simp only [hi, if_false]
        have : j1 = j ∨ j2 = j := by
          by_cases h1 : j1 = j
          · exact Or.inl h1
          · right; by_contra h2; exact hi ⟨fun h => absurd h h1, fun h => absurd h h2⟩
        rcases this with h1 | h2
        · simp [h1]
        · simp [h2]
    omega

theorem wcnt_apps {w : ℕ} (js : List (Fin w)) (j1 j2 : Fin w) :
    wcnt (apps js) j1 j2 = 2 * wcnt js j1 j2 := by
  induction js with
  | nil => simp [apps, wcnt]
  | cons j js ih =>
    simp only [apps, wcnt_cons, ih]; ring

theorem wcnt_apps_rep_le {w : ℕ} (m : ℕ) (j1 j2 : Fin w) : wcnt (apps (rep w m)) j1 j2 ≤ 4 * m := by
  rw [wcnt_apps]
  have := wcnt_le_count (rep w m) j1 j2
  rw [count_rep, count_rep] at this
  omega

theorem jbr_pow_eq {d : ℕ} (x : Mom d) (R : ℕ) : jbr x ^ (2 * R) = (1 + ‖x‖ ^ 2) ^ R := by
  rw [pow_mul, jbr, Real.sq_sqrt (by positivity)]

/-- **Transfer (conditional helper): a profile-uniform bound gives the root decay.**
Deviations from the plan statement (see `HANDOFF.md`): the hypothesis `hh` bounds the weight index at
`40 d + 4 m` (the plan's `+ 2m` on the derivative index cannot give decay), and `|W| ≤ 1`, `1 ≤ P.L`,
`1 ≤ P.d`, `0 ≤ b` are added. -/
theorem flowerWeighted_root_decay_of_uniform {P : WTParams} {p N Pm : ℕ} (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
    (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (m : ℕ)
    (W : ∀ LG : LayeredGarden (2 * Pm), (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hW : ∀ LG k, |W LG k| ≤ 1)
    (h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) (b X : ℝ) (hb : 0 ≤ b)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d + 4 * m) (h q j j') ≤ ENNReal.ofReal b)
    (hcore : ∀ h' : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ,
      (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h' q j j') ≤ ENNReal.ofReal (2 * b)) →
      ‖FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
        (fun LG k => W LG k * leafProd LG h' k) ζ t s n n'‖ ≤ X) :
    jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (2 * m * (2 * Pm)) *
      ‖FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
        (fun LG k => W LG k * leafProd LG h k) ζ t s n n'‖ ≤ rootPolarCost P.d m Pm N * X := by
  set R : ℕ := m * (2 * Pm) with hR
  set E : ℝ := (2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d) with hE
  set M : ℕ := N + Pm + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMw : 2 * N + 2 * Pm ≤ 2 * M := by omega
  have hdpos : (0 : ℝ) < P.d := by exact_mod_cast hd
  have hE0 : 0 < E := by rw [hE]; positivity
  set ε : ℝ := 1 / (4 * ((R : ℝ) + 1)) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  set lam : ℝ := ε / (M * E) with hlam
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlamME : lam * M * E = ε := by rw [hlam]; field_simp
  have hB : P.d + 1 ≤ 40 * P.d := by omega
  have hcore' : ∀ g : TProf P.d (2 * Pm), Adm p (40 * P.d) (40 * P.d) [] (2 * b) g →
      ‖Phi P p N kind pat dagger W ζ t s n n' g‖ ≤ X := fun g hg =>
    hcore g (fun q hq j j' => by simpa [wcnt_nil] using (hg q hq j j').2)
  have hAdm : Adm p (40 * P.d) (40 * P.d) (apps (rep (2 * Pm) m)) b h := by
    intro q hq j1 j2
    have hlt : SNormR (40 * P.d) (40 * P.d + 4 * m) (h q j1 j2) < ⊤ :=
      lt_of_le_of_lt (hh q hq j1 j2) ENNReal.ofReal_lt_top
    have hcd : ContDiff ℝ (40 * P.d) (h q j1 j2) := contDiff_of_SNormR_lt_top (Λ₁ := 40 * P.d) (by omega) hlt
    refine ⟨hcd, SNormR_mono_bound le_rfl ?_ _ hcd b hb (hh q hq j1 j2)⟩
    have := wcnt_apps_rep_le (w := 2 * Pm) m j1 j2
    omega
  have hT1 : ∑ m' ∈ range (2 * M + 1), |CentralDiff.cw M m' / lam| ≤ rootPolarT P.d m Pm N := by
    refine (sum_abs_cw_div_le M lam hlam0).trans (le_of_eq ?_)
    unfold rootPolarT
    rw [← hM, ← hE, ← hR, hlam, hε]
    field_simp
  have hpow : (1 + lam * M * ((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d))) ^ (2 * (rep (2 * Pm) m).length)
      ≤ 2 := by
    rw [rep_length, ← hR, ← hE, hlamME]
    have hRnn : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have hny : ((2 * R : ℕ) : ℝ) * ε ≤ 1 / 2 := by
      rw [hε]
      push_cast
      rw [← mul_div_assoc, mul_one, div_le_iff₀ (by positivity)]
      nlinarith
    have h1 := pow_one_add_sub_one_le hε0.le (2 * R) hny
    linarith
  have hle : b * (1 + lam * M * ((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d))) ^
      (2 * (rep (2 * Pm) m).length) ≤ 2 * b := by
    nlinarith
  have key := round_bound P hL p N kind pat dagger W hW ζ t s n n' (40 * P.d) (40 * P.d) hB M hM1
    hMw lam hlam0 b X (rootPolarT P.d m Pm N) hT1 hcore' (rep (2 * Pm) m) h b hb hAdm hle
  rw [rep_length, ← hR] at key
  show _ * ‖Phi P p N kind pat dagger W ζ t s n n' h‖ ≤ _
  have hc0 : 0 ≤ (1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2) ^ R := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0] at key
  have hjb : jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (2 * m * (2 * Pm)) =
      (1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2) ^ R := by
    rw [mul_assoc, ← hR]; exact jbr_pow_eq _ R
  rw [hjb]
  exact key

end WaveTurbulence.Flower.Polar
