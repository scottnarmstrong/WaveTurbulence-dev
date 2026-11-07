/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.Fam.Graded2
/-! # FL-FAM: the graded external-decay transfer.  The `N`-dependent factor is `rootPolarCost`; the
only dependence on the high weight bound `hi` is the `N`-independent factor `(hi/lo)^(2 m (2 Pm))`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.Fam
open Finset LGSpine WaveTurbulence.Flower.Polar

/-- **Graded transfer.**  `lo` bounds the profiles at weight `40d`, `hi` at weight `40d + 4m`;
`hcore` is applied at `2 lo`. -/
theorem root_decay_graded {P : WTParams} {p N Pm : ℕ} (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
    (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (m : ℕ)
    (W : ∀ LG : LayeredGarden (2 * Pm), (GNode LG.garden.tree → Mom P.d) → ℝ)
    (hW : ∀ LG k, |W LG k| ≤ 1)
    (h : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) (lo hi X : ℝ) (hlo : 0 < lo) (hlh : lo ≤ hi)
    (Good : (ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ) → Prop) (hgood : Good h)
    (hGs : ∀ g, Good g → ∀ (j : Fin (2 * Pm)) (i : Fin P.d) (μ : ℝ),
      Good (TProf.perturb g (polForm ((-1 : ℝ) ^ (j : ℕ)) j i g) μ))
    (hh_lo : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal lo)
    (hh_hi : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d + 4 * m) (h q j j') ≤ ENNReal.ofReal hi)
    (hcore : ∀ h' : ℕ → Fin (2 * Pm) → Fin (2 * Pm) → Mom P.d → ℝ, Good h' →
      (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h' q j j') ≤ ENNReal.ofReal (2 * lo)) →
      ‖FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
        (fun LG k => W LG k * leafProd LG h' k) ζ t s n n'‖ ≤ X) :
    jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (2 * m * (2 * Pm)) *
      ‖FC23.flowerWeighted P (fun _ _ => 1) p N kind pat dagger
        (fun LG k => W LG k * leafProd LG h k) ζ t s n n'‖ ≤
      (hi / lo) ^ (2 * (m * (2 * Pm))) * (rootPolarCost P.d m Pm N * X) := by
  set R : ℕ := m * (2 * Pm) with hR
  set E : ℝ := (2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d) with hE
  set M : ℕ := N + Pm + 1 with hM
  have hM1 : 1 ≤ M := by omega
  have hMw : 2 * N + 2 * Pm ≤ 2 * M := by omega
  have hdpos : (0 : ℝ) < P.d := by exact_mod_cast hd
  have hE0 : 0 < E := by rw [hE]; positivity
  have hhi : 0 < hi := lt_of_lt_of_le hlo hlh
  set κ : ℝ := hi / lo with hκ
  have hκ1 : 1 ≤ κ := by rw [hκ, le_div_iff₀ hlo]; linarith
  set ε : ℝ := lo / (4 * ((R : ℝ) + 1) * hi) with hε
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM1
  set lam : ℝ := ε / (M * E) with hlam
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlamME : lam * M * E = ε := by rw [hlam]; field_simp
  have hB : P.d + 1 ≤ 40 * P.d := by omega
  have hXnn : 0 ≤ X := by
    refine (norm_nonneg _).trans (hcore h hgood fun q hq j j' => (hh_lo q hq j j').trans
      (ENNReal.ofReal_le_ofReal (by linarith)))
  have hcore' : ∀ g : TProf P.d (2 * Pm), Good g → Adm p (40 * P.d) (40 * P.d) [] (2 * lo) g →
      ‖Phi P p N kind pat dagger W ζ t s n n' g‖ ≤ X := fun g hG hg =>
    hcore g hG (fun q hq j j' => by simpa [wcnt_nil] using (hg q hq j j').2)
  have hAdm : Adm p (40 * P.d) (40 * P.d) (apps (rep (2 * Pm) m)) hi h := by
    intro q hq j1 j2
    have hlt : SNormR (40 * P.d) (40 * P.d + 4 * m) (h q j1 j2) < ⊤ :=
      lt_of_le_of_lt (hh_hi q hq j1 j2) ENNReal.ofReal_lt_top
    have hcd : ContDiff ℝ (40 * P.d) (h q j1 j2) := contDiff_of_SNormR_lt_top (Λ₁ := 40 * P.d) (by omega) hlt
    refine ⟨hcd, SNormR_mono_bound le_rfl ?_ _ hcd hi hhi.le (hh_hi q hq j1 j2)⟩
    have := wcnt_apps_rep_le (w := 2 * Pm) m j1 j2
    omega
  have hLo : Lo p (40 * P.d) (40 * P.d) lo h := hh_lo
  have hT0 : ∑ m' ∈ range (2 * M + 1), |CentralDiff.cw M m' / lam| ≤ κ * rootPolarT P.d m Pm N := by
    refine (sum_abs_cw_div_le M lam hlam0).trans (le_of_eq ?_)
    unfold rootPolarT
    rw [← hM, ← hE, ← hR, hlam, hε, hκ]
    field_simp
  have hpow : (1 + lam * M * ((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d))) ^ (2 * (rep (2 * Pm) m).length) - 1
      ≤ 2 * ((2 * R : ℕ) : ℝ) * ε := by
    rw [rep_length, ← hR, ← hE, hlamME]
    have hny : ((2 * R : ℕ) : ℝ) * ε ≤ 1 / 2 := by
      rw [hε]
      push_cast
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      have : lo ≤ hi := hlh
      nlinarith [mul_nonneg (Nat.cast_nonneg R : (0:ℝ) ≤ R) hlo.le, mul_nonneg (Nat.cast_nonneg R : (0:ℝ) ≤ R) (sub_nonneg.mpr this)]
    exact pow_one_add_sub_one_le hε0.le (2 * R) hny
  have hle : lo + hi * ((1 + lam * M * ((2 : ℝ) ^ (40 * P.d) * (P.d : ℝ) ^ (40 * P.d))) ^
      (2 * (rep (2 * Pm) m).length) - 1) ≤ 2 * lo := by
    have h1 := mul_le_mul_of_nonneg_left hpow hhi.le
    have h2 : hi * (2 * ((2 * R : ℕ) : ℝ) * ε) ≤ lo := by
      rw [hε]
      push_cast
      have : hi * (2 * (2 * (R : ℝ)) * (lo / (4 * ((R : ℝ) + 1) * hi))) = lo * ((R : ℝ) / ((R : ℝ) + 1)) := by
        field_simp
        ring
      rw [this]
      have : (R : ℝ) / ((R : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
    rw [mul_sub] at h1 ⊢
    nlinarith
  have key := round_bound_graded P hL p N kind pat dagger W hW ζ t s n n' (40 * P.d) (40 * P.d) hB M hM1
    hMw lam hlam0 lo X (κ * rootPolarT P.d m Pm N) Good hGs hT0 hcore' (rep (2 * Pm) m) h hi lo hgood hhi.le hlo.le hAdm hLo
    (by simpa using hle)
  rw [rep_length, ← hR] at key
  show _ * ‖Phi P p N kind pat dagger W ζ t s n n' h‖ ≤ _
  have hc0 : 0 ≤ (1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2) ^ R := by positivity
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0] at key
  have hjb : jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^ (2 * m * (2 * Pm)) =
      (1 + ‖latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n'‖ ^ 2) ^ R := by
    rw [mul_assoc, ← hR]; exact jbr_pow_eq _ R
  rw [hjb]
  refine key.trans ?_
  have hbase : 1 + (P.d : ℝ) * (κ * rootPolarT P.d m Pm N) ^ 2 ≤ κ ^ 2 * (1 + P.d * rootPolarT P.d m Pm N ^ 2) := by
    have hκ2 : 1 ≤ κ ^ 2 := one_le_pow₀ hκ1
    have : 0 ≤ (P.d : ℝ) * rootPolarT P.d m Pm N ^ 2 := by positivity
    nlinarith
  have hpow2 : (1 + (P.d : ℝ) * (κ * rootPolarT P.d m Pm N) ^ 2) ^ R ≤
      (κ ^ 2 * (1 + P.d * rootPolarT P.d m Pm N ^ 2)) ^ R :=
    pow_le_pow_left₀ (by positivity) hbase R
  calc (1 + (P.d : ℝ) * (κ * rootPolarT P.d m Pm N) ^ 2) ^ R * X
      ≤ (κ ^ 2 * (1 + P.d * rootPolarT P.d m Pm N ^ 2)) ^ R * X := mul_le_mul_of_nonneg_right hpow2 hXnn
    _ = κ ^ (2 * R) * (rootPolarCost P.d m Pm N * X) := by
        rw [mul_pow, ← pow_mul]
        unfold rootPolarCost
        rw [← hR]; ring

end WaveTurbulence.Flower.Fam
