/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClFam3
/-! **FINALCOUNT-ASSEMBLY: uniform-threshold versions of `erase_cluster_deviation` / `erase_family_deviation`.**
G3's statements put the threshold `L₀` after the molecule `M` (and the family); its proof takes `L₀` from `cluster_table`, which depends
only on the constants.  Here `L₀` is placed BEFORE `M`, `𝒦`, so that it is uniform over all terminal states of a run
(`WTPrefix` chooses `L₀` before the garden).  Proofs are copies of G3's with the quantifier moved. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u v

theorem erase_cluster_deviation_unif {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ)
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
        (ENNReal.ofReal (clusterRHS L γ η C₀ K.card (eDart M K)
          ((eDart M K : ℤ) + ((intDart M K / 2 : ℕ) : ℤ) - K.card + 1 - cEs M K))) := by
  obtain ⟨L₀, hL₀, htab⟩ := cluster_table hd hγ0 hγ1 hη hη1 hC0 hC0η c₀
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

/-- **`erase_family_deviation` with a uniform threshold `L₀`** (before `𝒦` and `M`). -/
theorem erase_family_deviation_unif {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (𝒦 : Finset (Finset V)),
    ∀ {D : Type v} [Fintype D] [DecidableEq D] (M : Molecule V D), FamData M 𝒦 →
    ∃ j : Finset V → ℤ,
      M.circuitRank = (eraseSet M (𝒦.biUnion id)).circuitRank + ∑ K ∈ 𝒦, j K ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ {w : Mom d}
        (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
        (_ : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)),
        FamTame M 𝒦 Adm → FamLad L γ δ P c₀ M 𝒦 →
        IsDeviation (M.countA L γ δ C₁ w Adm P)
          ((eraseSet M (𝒦.biUnion id)).countA L γ δ C₁ w (resAdm Adm M (𝒦.biUnion id)) P)
          (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHS L γ η C₀ K.card (eDart M K) (j K))) := by
  obtain ⟨L₀, hL₀, hcl⟩ := erase_cluster_deviation_unif.{u, v} hd hγ0 hγ1 hη hη1 hC0 hC0η c₀
  refine ⟨L₀, hL₀, fun 𝒦 => ?_⟩
  induction 𝒦 using Finset.induction_on with
  | empty =>
    intro D _ _ M _
    refine ⟨fun _ => 0, ?_, ?_⟩
    · rw [Finset.biUnion_empty, Finset.sum_empty, add_zero]
      exact (emptyIso M).circuitRank_eq.symm
    · intro L _ C₁ δ _ _ _ w Adm P _ _ _
      rw [Finset.biUnion_empty, Finset.prod_empty]
      unfold IsDeviation
      rw [one_mul]
      exact le_of_eq ((emptyIso M).countA_eq L γ δ C₁ w Adm _ (resAdm_empty Adm M) P)
  | insert K 𝒦' hK ih =>
    intro D _ _ M hM
    have hK' : FamData (eraseSet M K) 𝒦' := hM.step hK
    obtain ⟨j', hrk', hdev'⟩ := ih (eraseSet M K) hK'
    have hKm : K ∈ insert K 𝒦' := Finset.mem_insert_self _ _
    obtain ⟨k₀, hk₀⟩ := hM.ne K hKm
    have hKc : ∀ k ∈ K, M.SameComponent k k₀ := fun k hk => induced_sc (hM.int K hKm k hk k₀ hk₀)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : D, M.atom x₀ = k₀ := by
      have h1 := hM.dpos K hKm k₀ hk₀
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one h1)
      exact ⟨x, by simpa [Molecule.dartsAt] using hx⟩
    have hdev1 := hcl V D M K hM.nl hM.m4 (hM.sub K hKm) k₀ hk₀ hKc (hM.int K hKm) (hM.dpos K hKm) x₀ (by rw [hx₀]; exact hk₀)
    set jK : ℤ := (eDart M K : ℤ) + ((intDart M K / 2 : ℕ) : ℤ) - K.card + 1 - cEs M K with hjK
    obtain ⟨ib, hib, hrk⟩ := circuitRank_eraseSet hM.nl (hM.sub K hKm)
    have hib2 : intDart M K / 2 = ib := by omega
    have hrk1 : M.circuitRank = (eraseSet M K).circuitRank + jK := by
      rw [hjK, hib2, hrk]; ring
    have hcong : ∀ A ∈ 𝒦', eDart (eraseSet M K) A = eDart M A := by
      intro A hA
      have hne : K ≠ A := fun e => hK (e ▸ hA)
      exact eDart_erase_eq (hM.cl.nobond A (Finset.mem_insert_of_mem hA) K hKm hne.symm)
        (hM.cl.disj A (Finset.mem_insert_of_mem hA) K hKm hne.symm)
    have hne' : ∀ A ∈ 𝒦', A ≠ K := fun A hA e => hK (e ▸ hA)
    refine ⟨fun A => if A = K then jK else j' A, ?_, ?_⟩
    · rw [Finset.sum_insert hK, if_pos rfl]
      have hs : ∑ A ∈ 𝒦', (if A = K then jK else j' A) = ∑ A ∈ 𝒦', j' A :=
        Finset.sum_congr rfl fun A hA => if_neg (hne' A hA)
      rw [hs, Finset.biUnion_insert]
      have h2 := (iterIso M K (𝒦'.biUnion id)).circuitRank_eq
      have h3 : (eraseSet M (id K ∪ 𝒦'.biUnion id)).circuitRank = (eraseSet (eraseSet M K) (𝒦'.biUnion id)).circuitRank :=
        h2
      rw [h3, hrk1, hrk']; ring
    · intro L hL C₁ δ hC hδ hδ1 w Adm P hX htame hlad
      have hl : ladProd L γ δ P M.maximalLadders ≤
          Real.log L ^ (c₀ * (K.card + eDart M K)) * ladProd L γ δ P (eraseSet M K).maximalLadders := by
        have := hlad ∅ (Finset.empty_subset _) K hKm (Finset.notMem_empty _)
        rwa [Finset.biUnion_empty, maximalLadders_eraseSet_empty, Finset.empty_union] at this
      have h1 := hdev1 L hL C₁ δ hC hδ hδ1 w Adm (resAdm Adm M K) (fun κ hκ => resAdm_intro hκ) P hX
        (htame K hKm).1 (htame K hKm).2 hl
      have h2 := hdev' L hL C₁ δ hC hδ hδ1 (w := w) (resAdm Adm M K) P hX (FamTame.step hM hK htame)
        (FamLad.step hM hK hlad)
      have h3 := iter_countA L γ δ C₁ w Adm M K (𝒦'.biUnion id) P
      have hp : ∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHS L γ η C₀ A.card (eDart (eraseSet M K) A) (j' A)) =
          ∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHS L γ η C₀ A.card (eDart M A)
            (if A = K then jK else j' A)) :=
        Finset.prod_congr rfl fun A hA => by rw [hcong A hA, if_neg (hne' A hA)]
      rw [hp] at h2
      rw [Finset.prod_insert hK, Finset.biUnion_insert]
      beta_reduce
      rw [if_pos rfl]
      unfold IsDeviation at h1 h2 ⊢
      calc M.countA L γ δ C₁ w Adm P
          ≤ ENNReal.ofReal (clusterRHS L γ η C₀ K.card (eDart M K) jK) *
              (eraseSet M K).countA L γ δ C₁ w (resAdm Adm M K) P := h1
        _ ≤ ENNReal.ofReal (clusterRHS L γ η C₀ K.card (eDart M K) jK) *
              ((∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHS L γ η C₀ A.card (eDart M A)
                (if A = K then jK else j' A))) *
              (eraseSet (eraseSet M K) (𝒦'.biUnion id)).countA L γ δ C₁ w
                (resAdm (resAdm Adm M K) (eraseSet M K) (𝒦'.biUnion id)) P) :=
            by gcongr
        _ = _ := by rw [← mul_assoc, h3]; rfl

end WaveTurbulence.FinalCountAsm
