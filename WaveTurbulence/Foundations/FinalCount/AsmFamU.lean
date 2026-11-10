/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTerm10
/-! **FINALCOUNT-ASSEMBLY: V-uniform threshold versions** of `erase_family_deviation_sharp` and `terminal_family`.  `WTPrefix` chooses `L₀`
before the garden, hence before the atom type `V = GBranch G.tree`; here `V` is quantified AFTER `L₀`.  Proofs are copies with the quantifier moved. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u v
variable {d : ℕ}

theorem erase_family_deviation_sharpU {d : ℕ} (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) (c₀ : ℕ) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ (V : Type u) [DecidableEq V], ∀ (𝒦 : Finset (Finset V)),
    ∀ {D : Type v} [Fintype D] [DecidableEq D] (M : Molecule V D), FamData M 𝒦 →
    ∃ j : Finset V → ℤ,
      M.circuitRank = (eraseSet M (𝒦.biUnion id)).circuitRank + ∑ K ∈ 𝒦, j K ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 → ∀ {w : Mom d}
        (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ)
        (_ : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S)),
        FamTame M 𝒦 Adm → FamLad L γ δ P c₀ M 𝒦 →
        IsDeviation (M.countA L γ δ C₁ w Adm P)
          ((eraseSet M (𝒦.biUnion id)).countA L γ δ C₁ w (resAdm Adm M (𝒦.biUnion id)) P)
          (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K) (j K))) := by
  obtain ⟨L₀, hL₀, hcl⟩ := erase_cluster_deviation_sharp.{u, v} hd hγ0 hγ1 hη hη1 hC0 hC0η c₀
  refine ⟨L₀, hL₀, fun V _ 𝒦 => ?_⟩
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
      have hp : ∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHSs L γ η C₀ A.card (eDart (eraseSet M K) A) (j' A)) =
          ∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHSs L γ η C₀ A.card (eDart M A)
            (if A = K then jK else j' A)) :=
        Finset.prod_congr rfl fun A hA => by rw [hcong A hA, if_neg (hne' A hA)]
      rw [hp] at h2
      rw [Finset.prod_insert hK, Finset.biUnion_insert]
      beta_reduce
      rw [if_pos rfl]
      unfold IsDeviation at h1 h2 ⊢
      calc M.countA L γ δ C₁ w Adm P
          ≤ ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K) jK) *
              (eraseSet M K).countA L γ δ C₁ w (resAdm Adm M K) P := h1
        _ ≤ ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart M K) jK) *
              ((∏ A ∈ 𝒦', ENNReal.ofReal (clusterRHSs L γ η C₀ A.card (eDart M A)
                (if A = K then jK else j' A))) *
              (eraseSet (eraseSet M K) (𝒦'.biUnion id)).countA L γ δ C₁ w
                (resAdm (resAdm Adm M K) (eraseSet M K) (𝒦'.biUnion id)) P) :=
            by gcongr
        _ = _ := by rw [← mul_assoc, h3]; rfl

theorem terminal_familyU (hd : 3 ≤ d) {γ η C₀ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hη : 0 < η)
    (hη1 : η ≤ gam0 γ / 1000) (hC0 : 0 ≤ C₀) (hC0η : C₀ * η ^ 4 ≤ 1) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L → ∀ C₁ δ : ℝ, 1 ≤ C₁ → 0 < δ → δ ≤ 1 →
    ∀ {V : Type v} [DecidableEq V] [Nonempty V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]
    {M₀ : Molecule V D₀} {hf : HSt V D₀} {Tm : V → Prop} {A : Set (D₀ → (Fin d → ℤ))} {P : Finset V → ℝ},
      LadderHered M₀ P → (∀ S, 0 ≤ P S) → LCtx M₀ hf.s →
      (∀ k0 ∈ A, ∀ v ∈ M₀.atoms, Tm v → ∀ x y, M₀.atom x = v → M₀.atom y = v → k0 x = k0 y) →
      (∀ k0 ∈ A, ∀ x, k0 (M₀.mate x) = k0 x) →
      (∀ v ∈ M₀.atoms, Tm v → M₀.deg v < 4 → ∃ k, ∀ k0 ∈ A, ∀ x, M₀.atom x = v → k0 x = k) →
      (∀ x, hf.s.M.atom x ≠ hf.s.M.atom (hf.s.M.mate x)) → (∀ a ∈ hf.s.M.atoms, hf.s.M.deg a ≤ 4) →
      (∀ a ∈ hf.s.M.atoms, 1 ≤ hf.s.M.deg a) →
      ∃ (𝒦 : Finset (Finset V)) (j : Finset V → ℤ) (Rs : Finset V),
        𝒦.biUnion id = tameSet hf Tm ∧ Clusters hf.s.M 𝒦 ∧
        hf.s.M.circuitRank = (eraseSet hf.s.M (tameSet hf Tm)).circuitRank + ∑ K ∈ 𝒦, j K ∧
        CompRep (hf.op5 Tm).s.M Rs ∧
        QS L γ δ C₁ (0 : Mom d) P hf A ≤ (∏ K ∈ 𝒦, ENNReal.ofReal (clusterRHSs L γ η C₀ K.card (eDart hf.s.M K) (j K))) *
          ∏ a ∈ Rs, (compMol (hf.op5 Tm).s.M a).countA L γ δ C₁ (0 : Mom d)
            (projAdm (hf.op5 Tm).s.M (compP (hf.op5 Tm).s.M a) (adm5 (AdmS (fun k => k ∈ A) hf.s) hf.s.M (tameSet hf Tm))) P := by
  obtain ⟨L₀, hL₀, hfam⟩ := erase_family_deviation_sharpU.{v, u} hd hγ0 hγ1 hη hη1 hC0 hC0η 4
  refine ⟨max L₀ (Real.exp 1), le_trans hL₀ (le_max_left _ _), fun L hL C₁ δ hC₁ hδ hδ1 V _ _ D₀ _ _ M₀ hf Tm A P hP hP0 hc hTame hmate hfix hnl hm4 hdpos => ?_⟩
  have hL' : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hLe : Real.exp 1 ≤ L := le_trans (le_max_right _ _) hL
  have hTsub : tameSet hf Tm ⊆ hf.s.M.atoms := fun v hv => (tameSet_mem.1 hv).1
  obtain ⟨𝒦, h1, hD⟩ := exists_famData hf.s.M (tameSet hf Tm) hTsub hnl hm4 (fun a ha => hdpos a (hTsub ha))
  obtain ⟨j, hrk, hdev⟩ := hfam V 𝒦 hf.s.M hD
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hLe
  have hX : ∀ S, 0 ≤ Molecule.ladderWeight L γ δ (P S) := fun S => by
    have := hP0 S
    unfold Molecule.ladderWeight
    exact le_min (by positivity) (by positivity)
  have hKfacts : ∀ K ∈ 𝒦, (∀ a ∈ K, a ∈ hf.s.M.atoms ∧ hf.s.cls a = .eps ∧ Tm a) ∧ (∀ a ∈ K, 1 ≤ hf.s.M.deg a) ∧
      ∀ a ∈ K, ∀ b ∈ K, (eraseSet hf.s.M (hf.s.M.atoms \ K)).SameComponent a b := by
    intro K hK
    refine ⟨fun a ha => ?_, hD.dpos K hK, hD.int K hK⟩
    have : a ∈ tameSet hf Tm := by rw [← h1]; exact Finset.mem_biUnion.2 ⟨K, hK, ha⟩
    exact tameSet_mem.1 this
  have hFT : FamTame hf.s.M 𝒦 (AdmS (fun k => k ∈ A) hf.s) := famTame_state hc Tm A hTame hmate hfix 𝒦 hKfacts
  have hFL : FamLad L γ δ P 4 hf.s.M 𝒦 := famLad_state hP hc hLe hδ hP0 le_rfl hm4 𝒦
  have hdev' := hdev L hL' C₁ δ hC₁ hδ hδ1 (w := (0 : Mom d)) (AdmS (fun k => k ∈ A) hf.s) P hX hFT hFL
  rw [h1] at hdev' hrk
  obtain ⟨Rs, hR, hbd⟩ := terminal_chain hf.s.M (tameSet hf Tm) L γ δ C₁ (0 : Mom d) hL0 hδ (by linarith)
    (AdmS (fun k => k ∈ A) hf.s) P hX hdev'
  exact ⟨𝒦, j, Rs, h1, hD.cl, hrk, hR, hbd⟩

end WaveTurbulence.FinalCountAsm
