/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClFam2
/-! **FINALCOUNT-ASSEMBLY: the sharper cluster lemma `AsmClSharp`** (ruling 2).  `clusterRHSs = clusterRHS · L^{-3η}`: a proof-level strengthening of
G3's `cluster_table` / `erase_cluster_deviation` / `erase_family_deviation` (the extra `L^{-3η}` per cluster is paid by the margin `(7/4)γ₀ m` of
the table, `γ₀ ≥ 1000 η`).  It repairs the `R = 1` deficit `2η` of the weak `clusterRHS` (HANDOFF finding): K = one degree-4 atom with 4 distinct
neighbours whose removal leaves 3 imperfect components.  Uniform threshold `L₀` (before `M`, `𝒦`) as in `AsmFamUnif`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u v

/-- The sharper bound of a cluster erasure. -/
noncomputable def clusterRHSs (L γ η C₀ : ℝ) (m e : ℕ) (j : ℤ) : ℝ :=
  L ^ (-η ^ 3 - 3 * η + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e))

theorem cluster_exponents_s {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (m e : ℕ) (j : ℤ) (hm : 1 ≤ m) (he : e ≤ 4 * m) :
    (0 ≤ j → -((d : ℝ) - γ) * (j : ℝ) + gam0 γ / 4 * m ≤
      -η ^ 3 - 3 * η + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e)) ∧
    ((m : ℤ) + 1 ≤ j → (d : ℝ) + 1 / 8 + gam0 γ / 4 * m + -((d : ℝ) - γ) * (j : ℝ) ≤
      -η ^ 3 - 3 * η + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e)) := by
  have hg0 : 0 < gam0 γ := lt_min hγ0 (by linarith)
  have hg1 : gam0 γ ≤ γ := min_le_left _ _
  have hg2 : gam0 γ ≤ 1 - γ := min_le_right _ _
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have heR : (e : ℝ) ≤ 4 * m := by exact_mod_cast he
  have he0 : (0 : ℝ) ≤ e := by positivity
  have hηs : η ≤ 1 / 2000 := by linarith
  have hη3 : η ^ 3 ≤ η := by nlinarith [sq_nonneg η, pow_pos hη 2]
  have hη2 : η ^ 2 ≤ η := by nlinarith
  have hC5 : C₀ * η ^ 5 ≤ η := by
    have : C₀ * η ^ 5 = (C₀ * η ^ 4) * η := by ring
    rw [this]; nlinarith
  have hC50 : 0 ≤ C₀ * η ^ 5 := by positivity
  have hsum : C₀ * η ^ 5 * ((m : ℝ) + e) ≤ η * (5 * m) := by
    have h1 : (m : ℝ) + e ≤ 5 * m := by linarith
    calc C₀ * η ^ 5 * ((m : ℝ) + e) ≤ η * ((m : ℝ) + e) := by
          exact mul_le_mul_of_nonneg_right hC5 (by positivity)
      _ ≤ η * (5 * m) := mul_le_mul_of_nonneg_left h1 hη.le
  have hηe : η * e ≤ η * (4 * m) := mul_le_mul_of_nonneg_left heR hη.le
  have hA : eraseA γ η = 2 * gam0 γ + 5 * η ^ 2 := rfl
  have hAle : eraseA γ η ≤ 2 * (1 - γ) + 5 * η ^ 2 := by rw [hA]; linarith
  have hu : 0 ≤ ((d : ℝ) - γ) - eraseA γ η := by rw [hA]; nlinarith
  have hcoef : 0 ≤ 2 * gam0 γ - 9 * η := by linarith
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · have hjR : (0 : ℝ) ≤ j := by exact_mod_cast hj
    have h1 : 0 ≤ (((d : ℝ) - γ) - eraseA γ η) * j := mul_nonneg hu hjR
    have h2 : 0 ≤ (7 / 4 * gam0 γ - 9 * η) * ((m : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
    have h3 : 3 * η + η ^ 3 ≤ 7 / 4 * gam0 γ - 9 * η := by linarith
    have h4 : 2 * gam0 γ * (m : ℝ) ≤ eraseA γ η * m := mul_le_mul_of_nonneg_right (by rw [hA]; nlinarith [sq_nonneg η]) (by linarith)
    rw [hA] at h1 ⊢
    nlinarith
  · have hjR : ((m : ℝ) + 1) ≤ j := by exact_mod_cast hj
    have h1 : 0 ≤ (((d : ℝ) - γ) - eraseA γ η) * ((j : ℝ) - m - 1) := mul_nonneg hu (by linarith)
    have h2 : 0 ≤ (((d : ℝ) - γ) - 9 * η - gam0 γ / 4) * ((m : ℝ) - 1) := mul_nonneg (by linarith) (by linarith)
    have hh : gam0 γ ≤ 1 / 2 := by linarith
    have h3 : 3 * η + η ^ 3 ≤ 1 / 10 := by linarith
    rw [hA] at h1 hAle ⊢
    nlinarith

theorem cluster_table_s {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ (m e : ℕ) (j : ℤ),
      1 ≤ m → e ≤ 4 * m →
      (0 ≤ j → rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e)) ≤ clusterRHSs L γ η C₀ m e j) ∧
      ((m : ℤ) + 1 ≤ j →
        ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) * (rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e))) ≤
          clusterRHSs L γ η C₀ m e j) := by
  have hg0 : 0 < gam0 γ := lt_min hγ0 (by linarith)
  obtain ⟨L₁, hL₁, h₁⟩ := polylog_pow_le (E := gam0 γ / 4) (by positivity) (5 * c₀)
  obtain ⟨L₂, hL₂, h₂⟩ := polylog_pow_le (E := 1 / 8) (by norm_num) 0
  have h3 : ∃ L₃ : ℝ, 1 ≤ L₃ ∧ ∀ L : ℝ, L₃ ≤ L → (3 : ℝ) ^ d ≤ L ^ (1 / 8 : ℝ) := by
    refine ⟨max 1 ((3 ^ d : ℝ) ^ 8), le_max_left _ _, fun L hL => ?_⟩
    have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
    have h1 : ((3 ^ d : ℝ) ^ 8) ≤ L := (le_max_right _ _).trans hL
    have h2 : (((3 ^ d : ℝ) ^ 8) ^ (1 / 8 : ℝ)) ≤ L ^ (1 / 8 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), show ((8 : ℕ) : ℝ) * (1 / 8) = 1 by norm_num,
      Real.rpow_one] at h2
  obtain ⟨L₃, hL₃, h₃⟩ := h3
  refine ⟨max (max L₁ L₃) (Real.exp 1), (hL₁.trans (le_max_left _ _)).trans (le_max_left _ _), fun L hL C₁ δ hC hδ hδ1 m e j hm he => ?_⟩
  have hLL₁ : L₁ ≤ L := ((le_max_left _ _).trans (le_max_left _ _)).trans hL
  have hLL₃ : L₃ ≤ L := ((le_max_right _ _).trans (le_max_left _ _)).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hL1 : 1 ≤ L := hL₁.trans hLL₁
  have hL0 : 0 < L := by linarith
  have hlogge : 1 ≤ Real.log L := by
    rw [Real.le_log_iff_exp_le hL0]; exact hLe
  obtain ⟨hex1, hex2⟩ := cluster_exponents_s hd hγ0 hγ1 hη hη1 hC0 hC0η m e j hm he
  have hlog0 : 0 ≤ Real.log L ^ (c₀ * (m + e)) := by positivity
  -- the ladder polylog: (log L)^(c₀ (m+e)) ≤ L^(gam0/4 · m)
  have hpoly : Real.log L ^ (c₀ * (m + e)) ≤ L ^ (gam0 γ / 4 * m) := by
    have h1 : Real.log L ^ (c₀ * (m + e)) ≤ Real.log L ^ (5 * c₀ * m) :=
      pow_le_pow_right₀ hlogge (by nlinarith [he])
    have h2 : Real.log L ^ (5 * c₀ * m) = (Real.log L ^ (5 * c₀)) ^ m := by rw [← pow_mul]
    have h3 := pow_le_pow_left₀ (by positivity) (h₁ L hLL₁) m
    have h4 : ((L ^ (gam0 γ / 4)) ^ m : ℝ) = L ^ (gam0 γ / 4 * m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    rw [← h4]; exact h1.trans (h2 ▸ h3)
  have hpoly0 : 0 ≤ L ^ (gam0 γ / 4 * m) := Real.rpow_nonneg hL0.le _
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · have hrf := rankFactor_le (d := d) (γ := γ) hL0 hδ hδ1 hC hj
    have hrf0 : 0 ≤ L ^ (-((d : ℝ) - γ) * (j : ℝ)) := Real.rpow_nonneg hL0.le _
    unfold clusterRHSs
    calc rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e))
        ≤ L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m) :=
          mul_le_mul hrf hpoly hlog0 hrf0
      _ = L ^ (-((d : ℝ) - γ) * (j : ℝ) + gam0 γ / 4 * m) := (Real.rpow_add hL0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 (hex1 (by omega))
  · have hj0 : 0 ≤ j := by omega
    have hrf := rankFactor_le (d := d) (γ := γ) hL0 hδ hδ1 hC hj0
    have hN : ((⌊2 * L⌋₊ + 1 : ℕ) : ℝ) ≤ 3 * L := by
      have : (⌊2 * L⌋₊ : ℝ) ≤ 2 * L := Nat.floor_le (by linarith)
      push_cast; linarith
    have hNd : ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) ≤ 3 ^ d * L ^ d := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hN d
    have hLd : (L ^ d : ℝ) = L ^ (d : ℝ) := (Real.rpow_natCast L d).symm
    have key2 : L ^ (1 / 8 : ℝ) * L ^ (d : ℝ) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m)) ≤
        L ^ (-η ^ 3 - 3 * η + eraseA γ η * ((m : ℝ) - j) - η * e - C₀ * η ^ 5 * ((m : ℝ) + e)) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by have := hex2 hj; linarith)
    unfold clusterRHSs
    have hx0 : 0 ≤ rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e)) :=
      mul_nonneg (rankFactor_nonneg d (γ := γ) hL0.le hδ.le (by linarith) _) hlog0
    calc ((⌊2 * L⌋₊ + 1 : ℕ) ^ d : ℝ) * (rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e)))
        ≤ (3 ^ d * L ^ d) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m)) := by
          have h3' : rankFactor d L γ δ C₁ j * Real.log L ^ (c₀ * (m + e)) ≤
              L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m) := mul_le_mul hrf hpoly hlog0
            (Real.rpow_nonneg hL0.le _)
          exact mul_le_mul hNd h3' hx0 (by positivity)
      _ = (3 ^ d) * (L ^ (d : ℝ) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m))) := by
          rw [← hLd]; ring
      _ ≤ L ^ (1 / 8 : ℝ) * (L ^ (d : ℝ) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m))) :=
          mul_le_mul_of_nonneg_right (h₃ L hLL₃) (by positivity)
      _ = L ^ (1 / 8 : ℝ) * L ^ (d : ℝ) * (L ^ (-((d : ℝ) - γ) * (j : ℝ)) * L ^ (gam0 γ / 4 * m)) := by ring
      _ ≤ _ := key2


theorem erase_cluster_deviation_sharp {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hη : 0 < η) (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (V : Type u) [DecidableEq V] (D : Type v) [Fintype D] [DecidableEq D] (M : Molecule V D) (K : Finset V)
    (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hK : K ⊆ M.atoms)
    (k₀ : V) (hk₀ : k₀ ∈ K) (hKc : ∀ k ∈ K, M.SameComponent k k₀)
    (hKint : ∀ a ∈ K, ∀ b ∈ K, (eraseSet M (M.atoms \ K)).SameComponent a b)
    (hdpos : ∀ a ∈ K, 1 ≤ M.deg a) (x₀ : D) (hx₀ : M.atom x₀ ∈ K),
    ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ (w : Mom d)
      (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (EDartS M K → (Fin d → ℤ)) → Prop)
      (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDartS M K => κ x.1)) (P : Finset V → ℝ)
      (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)),
      (∀ κ, Adm κ → TameLabelsS M K κ) →
      (∀ a ∈ K, M.deg a < 4 → ∃ k, ∀ κ, Adm κ → ∀ x ∈ M.dartsAt a, κ x = k) →
      (∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S ≤
        Real.log L ^ (c₀ * (K.card + eDart M K)) * ∏ S ∈ (eraseSet M K).maximalLadders,
          Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) →
      IsDeviation (M.countA L γ δ C₁ w Adm P) ((eraseSet M K).countA L γ δ C₁ w Adm' P)
        (ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K)
          ((eDart M K : ℤ) + ((intDart M K / 2 : ℕ) : ℤ) - K.card + 1 - cEs M K))) := by
  obtain ⟨L₀, hL₀, htab⟩ := cluster_table_s hd hγ0 hγ1 hη hη1 hC0 hC0η c₀
  refine ⟨L₀, hL₀, fun V _ D _ _ M K hnl hM4 hK k₀ hk₀ hKc hKint hdpos x₀ hx₀ L hL C₁ δ hC hδ hδ1 w Adm Adm' hAdm' P hX htame hfix hlad => ?_⟩
  have hL0 : 0 < L := by linarith
  have hm : 1 ≤ K.card := Finset.card_pos.2 ⟨k₀, hk₀⟩
  have he := eDart_le hM4 hK
  obtain ⟨ib, hib, hrk⟩ := circuitRank_eraseSet hnl hK
  have hib2 : intDart M K / 2 = ib := by omega
  rw [hib2]
  have hconn := card_le_ib_add_one hK ⟨k₀, hk₀⟩ hib hKint
  have hj0 := rank_drop_nonneg hnl hK hk₀ hKc hconn
  have hlog : 0 ≤ Real.log L ^ (c₀ * (K.card + eDart M K)) := by
    have := Real.log_nonneg (by linarith : 1 ≤ L); positivity
  have hdev := fun (Nn : ℕ∞) (hE : M.countE L γ δ w Adm ≤ Nn * (eraseSet M K).countE L γ δ w Adm') =>
    eraseSet_isDeviation hL0 hδ (C₁ := C₁) (by linarith) Adm Adm' P hX Nn (Real.log L ^ (c₀ * (K.card + eDart M K))) hlog
      ((eDart M K : ℤ) + ib - K.card + 1 - cEs M K) (by rw [hrk]; ring) hE hlad
  have key : ∀ (N : ℕ) (x y : ℝ), 0 ≤ x → (N : ℝ) * x ≤ y →
      (((N : ℕ) : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal x ≤ ENNReal.ofReal y := by
    intro N x y hx hxy
    rw [ENat.toENNReal_coe, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hxy
  have hrf0 := rankFactor_nonneg d (γ := γ) hL0.le hδ.le (by linarith : (0 : ℝ) ≤ C₁)
    ((eDart M K : ℤ) + ib - K.card + 1 - cEs M K)
  have hx0 : 0 ≤ rankFactor d L γ δ C₁ ((eDart M K : ℤ) + ib - K.card + 1 - cEs M K) * Real.log L ^ (c₀ * (K.card + eDart M K)) :=
    mul_nonneg hrf0 hlog
  obtain ⟨hpin, hunp⟩ := htab L hL C₁ δ hC hδ hδ1 K.card (eDart M K) _ hm he
  by_cases hP : PinnedS M K
  · have hE := countE_eraseSet_le_pinned (γ := γ) (δ := δ) (w := w) hL0 Adm Adm' hAdm' hM4 hK hx₀ hdpos htame hfix hP
    have h := hdev _ hE
    exact le_trans h (mul_le_mul_of_nonneg_right (key 1 _ _ hx0 (by simpa using hpin hj0)) bot_le)
  · have hE := countE_eraseSet_le_box (γ := γ) (δ := δ) (w := w) hL0 Adm Adm' hAdm' hM4 hx₀ htame
    have h := hdev _ hE
    obtain ⟨ib', hib', -, hrank⟩ := unpinned_rank hnl hK hM4 hk₀ hKc hP
    have hibe : ib' = ib := by omega
    subst hibe
    refine le_trans h (mul_le_mul_of_nonneg_right (key _ _ _ hx0 ?_) bot_le)
    have := hunp hrank
    push_cast at this ⊢
    exact this

variable {V : Type u} [DecidableEq V]

end WaveTurbulence.FinalCountAsm
