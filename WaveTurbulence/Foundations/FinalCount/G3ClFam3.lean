/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3ClFam2
/-! **FINALCOUNT-G3 (R29 item 4, step 1): `erase_family_deviation`.**  The chain combinator over a family `𝒦` of tame clusters
(`FamData`): `erase_cluster_deviation` is applied to the CURRENT molecule `M - K₁ - ... - K_{i-1}` for each cluster in turn (the pinned/unpinned
alternative is re-decided at each step; no bond joins two clusters, so `e_K`, degrees and internal connectivity are unchanged), the restricted
admissibility predicate is `resAdm Adm M T` (`T = ⋃ 𝒦`; `iterIso` + `DartIso.countA_eq` identify the nested erasure with `eraseSet M T`).
Conclusion: `𝔄(M) ≤ ∏_K ofReal(clusterRHS L γ η C₀ |K| e_K j_K) · 𝔄(M - T)` with `Σ_K j_K = χ(M) - χ(M - T)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u v
variable {V : Type u} [DecidableEq V]

/-- **`erase_family_deviation`** (R29 item 4, chain combinator). -/
theorem erase_family_deviation {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ) (𝒦 : Finset (Finset V)) :
    ∀ {D : Type v} [Fintype D] [DecidableEq D] (M : Molecule V D), FamData M 𝒦 →
    ∃ j : Finset V → ℤ,
      M.circuitRank = (eraseSet M (𝒦.biUnion id)).circuitRank + ∑ K ∈ 𝒦, j K ∧
      ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ {w : Mom d}
        (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
        (_ : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)),
        FamTame M 𝒦 Adm → FamLad L γ δ P c₀ M 𝒦 →
        IsDeviation (M.countA L γ δ C₁ w Adm P)
          ((eraseSet M (𝒦.biUnion id)).countA L γ δ C₁ w (resAdm Adm M (𝒦.biUnion id)) P)
          (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHS L γ η C₀ K.card (eDart M K) (j K))) := by
  induction 𝒦 using Finset.induction_on with
  | empty =>
    intro D _ _ M _
    refine ⟨fun _ => 0, ?_, 1, le_rfl, ?_⟩
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
    obtain ⟨j', hrk', L₁, hL₁, hdev'⟩ := ih (eraseSet M K) hK'
    have hKm : K ∈ insert K 𝒦' := Finset.mem_insert_self _ _
    obtain ⟨k₀, hk₀⟩ := hM.ne K hKm
    have hKc : ∀ k ∈ K, M.SameComponent k k₀ := fun k hk => induced_sc (hM.int K hKm k hk k₀ hk₀)
    obtain ⟨x₀, hx₀⟩ : ∃ x₀ : D, M.atom x₀ = k₀ := by
      have h1 := hM.dpos K hKm k₀ hk₀
      obtain ⟨x, hx⟩ := Finset.card_pos.1 (lt_of_lt_of_le Nat.zero_lt_one h1)
      exact ⟨x, by simpa [Molecule.dartsAt] using hx⟩
    obtain ⟨L₂, hL₂, hdev1⟩ := erase_cluster_deviation hd hγ0 hγ1 hη hη1 hC0 hC0η c₀ hM.nl hM.m4
      (hM.sub K hKm) hk₀ hKc (hM.int K hKm) (hM.dpos K hKm) (x₀ := x₀) (by rw [hx₀]; exact hk₀)
    set jK : ℤ := (eDart M K : ℤ) + ((intDart M K / 2 : ℕ) : ℤ) - K.card + 1 - cEs M K with hjK
    -- the rank identity
    obtain ⟨ib, hib, hrk⟩ := circuitRank_eraseSet hM.nl (hM.sub K hKm)
    have hib2 : intDart M K / 2 = ib := by omega
    have hrk1 : M.circuitRank = (eraseSet M K).circuitRank + jK := by
      rw [hjK, hib2, hrk]; ring
    -- the congruences for the other clusters
    have hcong : ∀ A ∈ 𝒦', eDart (eraseSet M K) A = eDart M A := by
      intro A hA
      have hne : K ≠ A := fun e => hK (e ▸ hA)
      exact eDart_erase_eq (hM.cl.nobond A (Finset.mem_insert_of_mem hA) K hKm hne.symm)
        (hM.cl.disj A (Finset.mem_insert_of_mem hA) K hKm hne.symm)
    have hne' : ∀ A ∈ 𝒦', A ≠ K := fun A hA e => hK (e ▸ hA)
    refine ⟨fun A => if A = K then jK else j' A, ?_, max L₁ L₂, le_trans hL₁ (le_max_left _ _), ?_⟩
    · rw [Finset.sum_insert hK, if_pos rfl]
      have hs : ∑ A ∈ 𝒦', (if A = K then jK else j' A) = ∑ A ∈ 𝒦', j' A :=
        Finset.sum_congr rfl fun A hA => if_neg (hne' A hA)
      rw [hs, Finset.biUnion_insert]
      have h2 := (iterIso M K (𝒦'.biUnion id)).circuitRank_eq
      have h3 : (eraseSet M (id K ∪ 𝒦'.biUnion id)).circuitRank = (eraseSet (eraseSet M K) (𝒦'.biUnion id)).circuitRank :=
        h2
      rw [h3, hrk1, hrk']; ring
    · intro L hL C₁ δ hC hδ hδ1 w Adm P hX htame hlad
      have hL1 : L₁ ≤ L := le_trans (le_max_left _ _) hL
      have hL2 : L₂ ≤ L := le_trans (le_max_right _ _) hL
      have hl : ladProd L γ δ P M.maximalLadders ≤
          Real.log L ^ (c₀ * (K.card + eDart M K)) * ladProd L γ δ P (eraseSet M K).maximalLadders := by
        have := hlad ∅ (Finset.empty_subset _) K hKm (Finset.notMem_empty _)
        rwa [Finset.biUnion_empty, maximalLadders_eraseSet_empty, Finset.empty_union] at this
      have h1 := hdev1 L hL2 C₁ δ hC hδ hδ1 (w := w) Adm (resAdm Adm M K) (fun κ hκ => resAdm_intro hκ) P hX
        (htame K hKm).1 (htame K hKm).2 hl
      have h2 := hdev' L hL1 C₁ δ hC hδ hδ1 (w := w) (resAdm Adm M K) P hX (FamTame.step hM hK htame)
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

end WaveTurbulence.FinalCountG3
