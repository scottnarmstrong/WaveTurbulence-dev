/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain33
public import WaveTurbulence.Foundations.FinalCount.AsmClSharp
public import WaveTurbulence.Foundations.FinalCount.LowIface3
/-! **FINALCOUNT LOW-CHAIN, session 6 (8): the weighted cluster erasure** (R79, NOTES §3 "Terminal cluster estimate").

`B` is the set of recorded loop atoms (effective degree `deg + 2`).  `PinnedE` is `PinnedS` with the third alternative "some atom of `K` has
EFFECTIVE degree `< 4`".  If `K` is not effectively pinned, `e + 2 ib + 2 k_K = 4 m`, hence `m + 1 ≤ j + k_K`
(`j = e + ib - m + 1 - c`).  `erase_cluster_deviation_wt`: `rankFactor(k_K) · 𝔄(M) ≤ clusterRHSs(m, e, j + k_K) · 𝔄(M - K)`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u v

section pin
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ} {M : Molecule V D} {K : Finset V}

/-- The effective degree of an atom: its degree, plus `2` at a loop atom. -/
def effD (M : Molecule V D) (B : Finset V) (a : V) : ℕ := M.deg a + if a ∈ B then 2 else 0

/-- `K` is effectively pinned: unbalanced atom, nonzero flux, or an atom of effective degree `< 4`. -/
def PinnedE (M : Molecule V D) (K B : Finset V) : Prop :=
  (∃ a ∈ K, M.outdeg a ≠ M.indeg a) ∨ (∃ a ∈ nbrS M K, sgnCS M K (cmpS M K a) ≠ 0) ∨ (∃ a ∈ K, effD M B a < 4)

/-- **Pinned clusters, effective form**: `𝔈(M) ≤ 𝔈(M - K)`. -/
theorem countE_eraseSet_le_pinnedE {B : Finset V} {L γ δ : ℝ} (hL : 0 < L) {w : Mom d} (Adm : (D → (Fin d → ℤ)) → Prop)
    (Adm' : (EDartS M K → (Fin d → ℤ)) → Prop) (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDartS M K => κ x.1))
    (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hKM : K ⊆ M.atoms) {x₀ : D} (hx₀ : M.atom x₀ ∈ K)
    (hdpos : ∀ a ∈ K, 1 ≤ M.deg a) (htame : ∀ κ, Adm κ → TameLabelsS M K κ)
    (hfix : ∀ a ∈ K, effD M B a < 4 → ∃ k, ∀ κ, Adm κ → ∀ x ∈ M.dartsAt a, κ x = k)
    (hP : PinnedE M K B) :
    M.countE L γ δ w Adm ≤ ((1 : ℕ) : ℕ∞) * (eraseSet M K).countE L γ δ w Adm' := by
  refine countE_eraseSet_le_of_vals Adm Adm' hAdm' hM4 _ fun c β k0 hp => ?_
  by_cases hex : ∃ κ, κ ∈ decSet M L γ δ w Adm c β k0
  · obtain ⟨κ₀, hκ₀⟩ := hex
    have hkey : ∀ κ ∈ decSet M L γ δ w Adm c β k0, κ x₀ = κ₀ x₀ := by
      intro κ hκ
      have hk1 : ∀ x, M.atom x ∈ K → κ x = κ x₀ := fun x hx => htame κ hκ.2.2 x x₀ hx hx₀
      have hk2 : ∀ x, M.atom x ∈ K → κ₀ x = κ₀ x₀ := fun x hx => htame κ₀ hκ₀.2.2 x x₀ hx hx₀
      rcases hP with ⟨a, haK, hne⟩ | ⟨a, ha, hsg⟩ | ⟨a, haK, hlt⟩
      · have e1 := unbalanced_label hκ.1 hk1 (hKM haK) haK
        have e2 := unbalanced_label hκ₀.1 hk2 (hKM haK) haK
        rw [e1] at e2
        have hne' : ((M.outdeg a : ℝ) - M.indeg a) ≠ 0 := by
          intro h; apply hne; exact_mod_cast (sub_eq_zero.1 h)
        have e3 := smul_right_injective (Mom d) hne' e2
        exact latticePoint_injective L hL (add_left_cancel e3)
      · have e1 := flux_identityS hκ.1 hk1 a
        have e2 := flux_identityS hκ₀.1 hk2 a
        rw [e1] at e2
        have e3 := smul_right_injective (Mom d) hsg e2
        exact latticePoint_injective L hL (add_left_cancel e3)
      · obtain ⟨k, hkf⟩ := hfix a haK hlt
        obtain ⟨y, hy⟩ := Finset.card_pos.1 (hdpos a haK)
        have hya : M.atom y = a := by simpa [Molecule.dartsAt] using hy
        have h1 := hkf κ hκ.2.2 y hy
        have h2 := hkf κ₀ hκ₀.2.2 y hy
        rw [hk1 y (hya ▸ haK)] at h1
        rw [hk2 y (hya ▸ haK)] at h2
        rw [h1, h2]
    exact ⟨{κ₀ x₀}, by simp, fun κ hκ => ⟨κ x₀, by simp [hkey κ hκ],
      fun x hx => htame κ hκ.2.2 x x₀ hx hx₀⟩⟩
  · exact ⟨∅, by simp, fun κ hκ => absurd ⟨κ, hκ⟩ hex⟩

/-- **The rank drop of an effectively unpinned cluster**: `e + 2 ib + 2 k_K = 4 m` and `m + 1 ≤ j + k_K`. -/
theorem unpinned_rankE {B : Finset V} (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hK : K ⊆ M.atoms)
    (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hB : ∀ a ∈ K, a ∈ B → M.deg a ≤ 2)
    {k₀ : V} (hk₀ : k₀ ∈ K) (hKc : ∀ k ∈ K, M.SameComponent k k₀) (hP : ¬ PinnedE M K B) :
    ∃ ib : ℕ, intDart M K = 2 * ib ∧
      (K.card : ℤ) + 1 ≤ (eDart M K : ℤ) + ib - K.card + 1 - cEs M K + ((K.filter fun a => a ∈ B).card : ℤ) := by
  unfold PinnedE at hP
  push Not at hP
  obtain ⟨-, hflux, hdeg⟩ := hP
  obtain ⟨ib, hib, -⟩ := circuitRank_eraseSet hnl hK
  refine ⟨ib, hib, ?_⟩
  have hs := sum_deg_K hK
  have hsum : ∑ a ∈ K, effD M B a = ∑ _a ∈ K, 4 := by
    refine Finset.sum_congr rfl fun a ha => le_antisymm ?_ (hdeg a ha)
    unfold effD
    have := hM4 a (hK ha)
    by_cases haB : a ∈ B
    · have := hB a ha haB; simp [haB]; omega
    · simp [haB]; omega
  have hsplit : ∑ a ∈ K, effD M B a = ∑ a ∈ K, M.deg a + 2 * (K.filter fun a => a ∈ B).card := by
    unfold effD
    rw [Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_filter]
    simp [mul_comm]
  rw [hsplit] at hsum
  simp at hsum
  have h2 := two_csS_le hnl hflux
  have h3 := numComponents_eraseSet_le hK hk₀ hKc
  unfold cEs
  omega

end pin

/-- Weighted deviation from a deviation: multiplying by `rankFactor k` shifts the rank drop `j ↦ j + k`. -/
theorem wdev_of_dev {d : ℕ} {L γ δ C₁ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hC : 0 < C₁) {A A' Nn : ℝ≥0∞} {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (j : ℤ) (kk : ℕ) (h : IsDeviation A A' (Nn * ENNReal.ofReal (rankFactor d L γ δ C₁ j * Λ))) :
    ENNReal.ofReal (rankFactor d L γ δ C₁ (kk : ℤ)) * A ≤
      Nn * ENNReal.ofReal (rankFactor d L γ δ C₁ (j + kk) * Λ) * A' := by
  unfold IsDeviation at h
  have hr1 := rankFactor_nonneg d (γ := γ) hL.le hδ.le hC.le (kk : ℤ)
  have hr2 := rankFactor_nonneg d (γ := γ) hL.le hδ.le hC.le j
  calc ENNReal.ofReal (rankFactor d L γ δ C₁ (kk : ℤ)) * A
      ≤ ENNReal.ofReal (rankFactor d L γ δ C₁ (kk : ℤ)) * (Nn * ENNReal.ofReal (rankFactor d L γ δ C₁ j * Λ) * A') := by
        gcongr
    _ = Nn * (ENNReal.ofReal (rankFactor d L γ δ C₁ (kk : ℤ)) * ENNReal.ofReal (rankFactor d L γ δ C₁ j * Λ)) * A' := by
        ring
    _ = Nn * ENNReal.ofReal (rankFactor d L γ δ C₁ (j + kk) * Λ) * A' := by
        rw [← ENNReal.ofReal_mul hr1, rankFactor_add d hL hδ hC.ne' j (kk : ℤ)]
        congr 3
        ring

/-- **The weighted erasure of one cluster** (R79). -/
theorem erase_cluster_deviation_wt {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hη : 0 < η) (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (V : Type u) [DecidableEq V] (D : Type v) [Fintype D] [DecidableEq D] (M : Molecule V D) (B K : Finset V)
    (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hK : K ⊆ M.atoms)
    (hB : ∀ a ∈ K, a ∈ B → M.deg a ≤ 2)
    (k₀ : V) (hk₀ : k₀ ∈ K) (hKc : ∀ k ∈ K, M.SameComponent k k₀)
    (hKint : ∀ a ∈ K, ∀ b ∈ K, (eraseSet M (M.atoms \ K)).SameComponent a b)
    (hdpos : ∀ a ∈ K, 1 ≤ M.deg a) (x₀ : D) (hx₀ : M.atom x₀ ∈ K),
    ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ (w : Mom d)
      (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (EDartS M K → (Fin d → ℤ)) → Prop)
      (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDartS M K => κ x.1)) (P : Finset V → ℝ)
      (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)),
      (∀ κ, Adm κ → TameLabelsS M K κ) →
      (∀ a ∈ K, effD M B a < 4 → ∃ k, ∀ κ, Adm κ → ∀ x ∈ M.dartsAt a, κ x = k) →
      (∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S ≤
        Real.log L ^ (c₀ * (K.card + eDart M K)) * ∏ S ∈ (eraseSet M K).maximalLadders,
          Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) →
      ENNReal.ofReal (rankFactor d L γ δ C₁ ((K.filter fun a => a ∈ B).card : ℤ)) * M.countA L γ δ C₁ w Adm P ≤
        ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K)
          ((eDart M K : ℤ) + ((intDart M K / 2 : ℕ) : ℤ) - K.card + 1 - cEs M K + ((K.filter fun a => a ∈ B).card : ℤ))) *
          (eraseSet M K).countA L γ δ C₁ w Adm' P := by
  obtain ⟨L₀, hL₀, htab⟩ := cluster_table_s hd hγ0 hγ1 hη hη1 hC0 hC0η c₀
  refine ⟨L₀, hL₀, fun V _ D _ _ M B K hnl hM4 hK hB k₀ hk₀ hKc hKint hdpos x₀ hx₀ L hL C₁ δ hC hδ hδ1 w Adm Adm' hAdm' P hX htame
    hfix hlad => ?_⟩
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
  set kk : ℕ := (K.filter fun a => a ∈ B).card with hkk
  set j0 : ℤ := (eDart M K : ℤ) + ib - K.card + 1 - cEs M K with hj0def
  have hrf0 := rankFactor_nonneg d (γ := γ) hL0.le hδ.le (by linarith : (0 : ℝ) ≤ C₁) (j0 + kk)
  have hx0 : 0 ≤ rankFactor d L γ δ C₁ (j0 + kk) * Real.log L ^ (c₀ * (K.card + eDart M K)) := mul_nonneg hrf0 hlog
  have hwd := fun (Nn : ℕ∞) (hE : M.countE L γ δ w Adm ≤ Nn * (eraseSet M K).countE L γ δ w Adm') =>
    wdev_of_dev (d := d) (γ := γ) hL0 hδ (by linarith : (0 : ℝ) < C₁) (Nn := (Nn : ℝ≥0∞))
      (Λ := Real.log L ^ (c₀ * (K.card + eDart M K))) hlog j0 kk (hdev Nn hE)
  obtain ⟨hpin, hunp⟩ := htab L hL C₁ δ hC hδ hδ1 K.card (eDart M K) (j0 + kk) hm he
  by_cases hP : PinnedE M K B
  · have hE := countE_eraseSet_le_pinnedE (B := B) (γ := γ) (δ := δ) (w := w) hL0 Adm Adm' hAdm' hM4 hK hx₀ hdpos htame hfix hP
    have h := hwd _ hE
    have hj0' : 0 ≤ j0 + (kk : ℤ) := add_nonneg hj0 (Int.natCast_nonneg _)
    exact le_trans h (mul_le_mul_of_nonneg_right (key 1 _ _ hx0 (by rw [Nat.cast_one, one_mul]; exact hpin hj0')) bot_le)
  · have hE := countE_eraseSet_le_box (γ := γ) (δ := δ) (w := w) hL0 Adm Adm' hAdm' hM4 hx₀ htame
    have h := hwd _ hE
    obtain ⟨ib', hib', hrank⟩ := unpinned_rankE (B := B) hnl hK hM4 hB hk₀ hKc hP
    have hibe : ib' = ib := by omega
    subst hibe
    refine le_trans h (mul_le_mul_of_nonneg_right (key _ _ _ hx0 ?_) bot_le)
    have := hunp (by simpa [j0, kk] using hrank)
    push_cast at this ⊢
    exact this

end WaveTurbulence.FinalCountAsm
