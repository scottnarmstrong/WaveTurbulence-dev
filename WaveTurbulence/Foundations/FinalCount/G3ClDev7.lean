/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClDev6
public import WaveTurbulence.Foundations.FinalCount.G3ClConn
/-! **FINALCOUNT-G3 (R29 item 4): `erase_cluster_deviation`.**  For a connected tame cluster `K` (all darts at atoms of `K` carry one label),
`m = |K|`, `e = e_K`, `j = e + ib - m + 1 - c`:
`𝔄(M) ≤ L^{-η³ + a(m-j) - η e - C₀ η⁵ (m+e)} · 𝔄(M - K)` for `L` large, `d ≥ 3`, where `a = 2γ₀ + 5η²`; pinned `K` by `N = 1`, unpinned by the box
`N = (⌊2L⌋+1)^d` and `j ≥ m + 1`.  Named inputs: `hfix` (subpro (3): an atom of degree `< 4` has its label fixed) and `hlad`
(the ladder-weight ratio `≤ (log L)^{c₀ (m+e)}`, O3 of R29 item 6). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

theorem eDart_le {M : Molecule V D} {K : Finset V} (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hK : K ⊆ M.atoms) :
    eDart M K ≤ 4 * K.card := by
  have h1 := sum_deg_K hK
  have h2 : ∑ a ∈ K, M.deg a ≤ ∑ _a ∈ K, 4 := Finset.sum_le_sum fun a ha => hM4 a (hK ha)
  simp at h2
  omega

/-- **`erase_cluster_deviation`.** -/
theorem erase_cluster_deviation {M : Molecule V D} {K : Finset V} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hη : 0 < η) (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ)
    (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (hM4 : ∀ a ∈ M.atoms, M.deg a ≤ 4) (hK : K ⊆ M.atoms)
    {k₀ : V} (hk₀ : k₀ ∈ K) (hKc : ∀ k ∈ K, M.SameComponent k k₀)
    (hKint : ∀ a ∈ K, ∀ b ∈ K, (eraseSet M (M.atoms \ K)).SameComponent a b)
    (hdpos : ∀ a ∈ K, 1 ≤ M.deg a) {x₀ : D} (hx₀ : M.atom x₀ ∈ K) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ {w : Mom d}
      (Adm : (D → (Fin d → ℤ)) → Prop) (Adm' : (EDartS M K → (Fin d → ℤ)) → Prop)
      (hAdm' : ∀ κ, Adm κ → Adm' (fun x : EDartS M K => κ x.1)) (P : Finset V → ℝ)
      (hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)),
      (∀ κ, Adm κ → TameLabelsS M K κ) →
      (∀ a ∈ K, M.deg a < 4 → ∃ k, ∀ κ, Adm κ → ∀ x ∈ M.dartsAt a, κ x = k) →
      (∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S ≤
        Real.log L ^ (c₀ * (K.card + eDart M K)) * ∏ S ∈ (eraseSet M K).maximalLadders,
          Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S) →
      IsDeviation (M.countA L γ δ C₁ w Adm P) ((eraseSet M K).countA L γ δ C₁ w Adm' P)
        (ENNReal.ofReal (clusterRHS L γ η C₀ K.card (eDart M K)
          ((eDart M K : ℤ) + ((intDart M K / 2 : ℕ) : ℤ) - K.card + 1 - cEs M K))) := by
  obtain ⟨L₀, hL₀, htab⟩ := cluster_table hd hγ0 hγ1 hη hη1 hC0 hC0η c₀
  refine ⟨L₀, hL₀, fun L hL C₁ δ hC hδ hδ1 w Adm Adm' hAdm' P hX htame hfix hlad => ?_⟩
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

end WaveTurbulence.FinalCountG3
