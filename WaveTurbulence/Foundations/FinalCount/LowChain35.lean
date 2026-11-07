/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain34
public import WaveTurbulence.Foundations.FinalCount.AsmFamU
/-! **FINALCOUNT LOW-CHAIN, session 6 (9): the weighted cluster family** (R79).  `FamTameE` is `FamTame` with effective degrees;
`erase_family_deviation_wtU`: for a family of clusters, `rankFactor(Σ_K k_K) · 𝔄(M) ≤ ∏_K clusterRHSs(m_K, e_K, j_K + k_K) · 𝔄(M - ⋃𝒦)`
(the loop credit is spent exactly once: `k_K = |K ∩ B|`).  Proof: the induction of `erase_family_deviation_sharpU` with the weighted cluster lemma. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u v

theorem rankFactor_zero' (d : ℕ) (L γ δ C₁ : ℝ) : rankFactor d L γ δ C₁ 0 = 1 := by
  unfold rankFactor; simp

section famE
variable {V : Type u} [DecidableEq V] {D : Type v} [Fintype D] [DecidableEq D] {d : ℕ}

/-- Tameness of the clusters, effective fixedness, and degree `≤ 2` at the loop atoms. -/
def FamTameE (M : Molecule V D) (B : Finset V) (𝒦 : Finset (Finset V)) (Adm : (D → (Fin d → ℤ)) → Prop) : Prop :=
  ∀ K ∈ 𝒦, (∀ κ, Adm κ → TameLabelsS M K κ) ∧
    (∀ a ∈ K, effD M B a < 4 → ∃ k, ∀ κ, Adm κ → ∀ x ∈ M.dartsAt a, κ x = k) ∧ (∀ a ∈ K, a ∈ B → M.deg a ≤ 2)

theorem FamTameE.step {M : Molecule V D} {B K : Finset V} {𝒦 : Finset (Finset V)} {Adm : (D → (Fin d → ℤ)) → Prop}
    (hd : FamData M (insert K 𝒦)) (hK : K ∉ 𝒦)
    (h : FamTameE M B (insert K 𝒦) Adm) : FamTameE (eraseSet M K) B 𝒦 (resAdm Adm M K) := by
  intro A hA
  have hne : K ≠ A := fun e => hK (e ▸ hA)
  have hnb : ∀ x, M.atom x ∈ A → M.atom (M.mate x) ∉ K :=
    hd.cl.nobond A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm
  have hdis := hd.cl.disj A (Finset.mem_insert_of_mem hA) K (Finset.mem_insert_self _ _) hne.symm
  obtain ⟨ht, hf, hb⟩ := h A (Finset.mem_insert_of_mem hA)
  refine ⟨?_, ?_, ?_⟩
  · rintro κ₁ ⟨κ, hκ, hk⟩ x y hx hy
    rw [hk, hk]
    exact ht κ hκ x.1 y.1 hx hy
  · intro a ha hlt
    unfold effD at hlt
    rw [deg_erase_eq hnb hdis ha] at hlt
    obtain ⟨k, hk⟩ := hf a ha hlt
    refine ⟨k, ?_⟩
    rintro κ₁ ⟨κ, hκ, hk1⟩ x hx
    rw [hk1]
    refine hk κ hκ x.1 ?_
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx
  · intro a ha haB
    rw [deg_erase_eq hnb hdis ha]
    exact hb a ha haB

end famE

theorem erase_family_deviation_wtU {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (V : Type u) [DecidableEq V], ∀ (B : Finset V) (𝒦 : Finset (Finset V)),
    ∀ {D : Type v} [Fintype D] [DecidableEq D] (M : Molecule V D), FamData M 𝒦 →
    ∃ j : Finset V → ℤ,
      M.circuitRank = (eraseSet M (𝒦.biUnion id)).circuitRank + ∑ K ∈ 𝒦, j K ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ {w : Mom d}
        (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
        (_ : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)),
        FamTameE M B 𝒦 Adm → FamLad L γ δ P c₀ M 𝒦 →
        ENNReal.ofReal (rankFactor d L γ δ C₁ ((∑ K ∈ 𝒦, (K.filter fun a => a ∈ B).card : ℕ) : ℤ)) *
            M.countA L γ δ C₁ w Adm P ≤
          (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K) (j K + ((K.filter fun a => a ∈ B).card : ℤ)))) *
          (eraseSet M (𝒦.biUnion id)).countA L γ δ C₁ w (resAdm Adm M (𝒦.biUnion id)) P := by
  obtain ⟨L₀, hL₀, hcl⟩ := erase_cluster_deviation_wt.{u, v} hd hγ0 hγ1 hη hη1 hC0 hC0η c₀
  refine ⟨L₀, hL₀, fun V _ B 𝒦 => ?_⟩
  induction 𝒦 using Finset.induction_on with
  | empty =>
    intro D _ _ M _
    refine ⟨fun _ => 0, ?_, ?_⟩
    · rw [Finset.biUnion_empty, Finset.sum_empty, add_zero]
      exact (emptyIso M).circuitRank_eq.symm
    · intro L _ C₁ δ _ _ _ w Adm P _ _ _
      rw [Finset.biUnion_empty, Finset.prod_empty, Finset.sum_empty]
      simp only [Nat.cast_zero, rankFactor_zero', ENNReal.ofReal_one, one_mul]
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
      obtain ⟨htame1, hfix1, hB1⟩ := htame K hKm
      have hdev1 := hcl V D M B K hM.nl hM.m4 (hM.sub K hKm) hB1 k₀ hk₀ hKc (hM.int K hKm) (hM.dpos K hKm) x₀
        (by rw [hx₀]; exact hk₀)
      have hl : ladProd L γ δ P M.maximalLadders ≤
          Real.log L ^ (c₀ * (K.card + eDart M K)) * ladProd L γ δ P (eraseSet M K).maximalLadders := by
        have := hlad ∅ (Finset.empty_subset _) K hKm (Finset.notMem_empty _)
        rwa [Finset.biUnion_empty, maximalLadders_eraseSet_empty, Finset.empty_union] at this
      have h1 := hdev1 L hL C₁ δ hC hδ hδ1 w Adm (resAdm Adm M K) (fun κ hκ => resAdm_intro hκ) P hX
        htame1 hfix1 hl
      have h2 := hdev' L hL C₁ δ hC hδ hδ1 (w := w) (resAdm Adm M K) P hX (FamTameE.step hM hK htame)
        (FamLad.step hM hK hlad)
      have h3 := iter_countA L γ δ C₁ w Adm M K (𝒦'.biUnion id) P
      have hp : ∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHSs L γ η C₀ A.card (eDart (eraseSet M K) A)
            (j' A + ((A.filter fun a => a ∈ B).card : ℤ))) =
          ∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHSs L γ η C₀ A.card (eDart M A)
            ((if A = K then jK else j' A) + ((A.filter fun a => a ∈ B).card : ℤ))) :=
        Finset.prod_congr rfl fun A hA => by rw [hcong A hA, if_neg (hne' A hA)]
      rw [hp] at h2
      rw [Finset.prod_insert hK, Finset.biUnion_insert, Finset.sum_insert hK]
      beta_reduce
      rw [if_pos rfl]
      have hrfn : ∀ n : ℤ, 0 ≤ rankFactor d L γ δ C₁ n := fun n =>
        rankFactor_nonneg d (γ := γ) (by linarith) hδ.le (by linarith) n
      have hsplit : ENNReal.ofReal (rankFactor d L γ δ C₁ (((K.filter fun a => a ∈ B).card + ∑ A ∈ 𝒦', (A.filter fun a => a ∈ B).card : ℕ) : ℤ)) =
          ENNReal.ofReal (rankFactor d L γ δ C₁ ((∑ A ∈ 𝒦', (A.filter fun a => a ∈ B).card : ℕ) : ℤ)) *
            ENNReal.ofReal (rankFactor d L γ δ C₁ (((K.filter fun a => a ∈ B).card : ℕ) : ℤ)) := by
        rw [Nat.cast_add, add_comm, rankFactor_add d (by linarith) hδ (by linarith : C₁ ≠ 0) _ _,
          ENNReal.ofReal_mul (hrfn _)]
      rw [hsplit]
      calc ENNReal.ofReal (rankFactor d L γ δ C₁ ((∑ A ∈ 𝒦', (A.filter fun a => a ∈ B).card : ℕ) : ℤ)) *
            ENNReal.ofReal (rankFactor d L γ δ C₁ (((K.filter fun a => a ∈ B).card : ℕ) : ℤ)) *
            M.countA L γ δ C₁ w Adm P
          = ENNReal.ofReal (rankFactor d L γ δ C₁ ((∑ A ∈ 𝒦', (A.filter fun a => a ∈ B).card : ℕ) : ℤ)) *
            (ENNReal.ofReal (rankFactor d L γ δ C₁ (((K.filter fun a => a ∈ B).card : ℕ) : ℤ)) *
              M.countA L γ δ C₁ w Adm P) := by ring
        _ ≤ ENNReal.ofReal (rankFactor d L γ δ C₁ ((∑ A ∈ 𝒦', (A.filter fun a => a ∈ B).card : ℕ) : ℤ)) *
            (ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K) (jK + ((K.filter fun a => a ∈ B).card : ℤ))) *
              (eraseSet M K).countA L γ δ C₁ w (resAdm Adm M K) P) := by gcongr
        _ = ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K) (jK + ((K.filter fun a => a ∈ B).card : ℤ))) *
            (ENNReal.ofReal (rankFactor d L γ δ C₁ ((∑ A ∈ 𝒦', (A.filter fun a => a ∈ B).card : ℕ) : ℤ)) *
              (eraseSet M K).countA L γ δ C₁ w (resAdm Adm M K) P) := by ring
        _ ≤ ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K) (jK + ((K.filter fun a => a ∈ B).card : ℤ))) *
            ((∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHSs L γ η C₀ A.card (eDart M A)
                ((if A = K then jK else j' A) + ((A.filter fun a => a ∈ B).card : ℤ)))) *
              (eraseSet (eraseSet M K) (𝒦'.biUnion id)).countA L γ δ C₁ w
                (resAdm (resAdm Adm M K) (eraseSet M K) (𝒦'.biUnion id)) P) := by gcongr
        _ = _ := by rw [← mul_assoc, h3]; rfl

end WaveTurbulence.FinalCountAsm
