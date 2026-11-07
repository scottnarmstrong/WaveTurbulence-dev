/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3LadErase2
public import WaveTurbulence.Foundations.FinalCount.G3ClFam2
/-! **FINALCOUNT-G3 (R29 item 6, O3), part 3: the ladder ratio of an erasure, `FamLad`.**  Erasing the atoms of `E` one at a time
(`ladderProd_le_erase1`) loses `≤ 2` rungs each, each of weight `≤ (log L)²`: `∏_{M.max} X^z ≤ (log L)^{4|E|} ∏_{(M - E).max} X^z`.
Hence `FamLad L γ δ P c₀ M 𝒦` for every family, `c₀ ≥ 4`, `L ≥ e`, nonnegative gap scales `P` that are constant along inclusions of
ladder sets of `M` (`LadderHered`, the named premise of `G3Ladder`; DH23 `kqmainest2`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u v
variable {V : Type u} [DecidableEq V] {D : Type v} [Fintype D] [DecidableEq D]

theorem ladderWeight_bounds {L γ δ : ℝ} (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ Molecule.ladderWeight L γ δ p ∧ Molecule.ladderWeight L γ δ p ≤ Real.log L ^ 2 := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) hL
  have hlog : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  unfold Molecule.ladderWeight
  refine ⟨le_min (one_le_pow₀ hlog) ?_, min_le_left _ _⟩
  have : 0 ≤ δ * L ^ (2 * γ) * p := by positivity
  linarith

theorem ladProd_erase_one {L γ δ : ℝ} (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) {P : Finset V → ℝ} (hP0 : ∀ S, 0 ≤ P S)
    (M : Molecule V D) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (hher : ∀ S' S, M.IsLadderSet S' → M.IsLadderSet S → S' ⊆ S → P S' = P S) (a : V) :
    ladProd L γ δ P M.maximalLadders ≤ (Real.log L ^ 2) ^ 2 * ladProd L γ δ P (eraseSet M {a}).maximalLadders := by
  refine ladderProd_le_erase1 M hM (fun S => Molecule.ladderWeight L γ δ (P S)) (Real.log L ^ 2)
    (fun S => (ladderWeight_bounds hL hδ (hP0 S)).1) (fun S => (ladderWeight_bounds hL hδ (hP0 S)).2) ?_
  intro S' hS' S hS hsub
  have h1 := (mem_maximalLadders_iff _).1 hS'
  have h2 := (mem_maximalLadders_iff _).1 hS
  show Molecule.ladderWeight L γ δ (P S') = Molecule.ladderWeight L γ δ (P S)
  rw [hher S' S (isLadderSet_of_erase M h1.1) h2.1 hsub]

theorem ladProd_erase_set {L γ δ : ℝ} (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) {P : Finset V → ℝ} (hP0 : ∀ S, 0 ≤ P S)
    (M : Molecule V D) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (hher : ∀ S' S, M.IsLadderSet S' → M.IsLadderSet S → S' ⊆ S → P S' = P S) (E : Finset V) :
    ladProd L γ δ P M.maximalLadders ≤ (Real.log L ^ 2) ^ (2 * E.card) *
      ladProd L γ δ P (eraseSet M E).maximalLadders := by
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by
    have := Real.add_one_le_exp 1; linarith)
  induction E using Finset.induction_on with
  | empty =>
    rw [Finset.card_empty, mul_zero, pow_zero, one_mul, maximalLadders_eraseSet_empty]
  | insert a E ha ih =>
    have hN : ∀ b ∈ (eraseSet M E).atoms, (eraseSet M E).deg b ≤ 4 := fun b hb =>
      le_trans (deg_erase_le (Finset.mem_sdiff.1 hb).2) (hM b (Finset.mem_sdiff.1 hb).1)
    have hhN : ∀ S' S, (eraseSet M E).IsLadderSet S' → (eraseSet M E).IsLadderSet S → S' ⊆ S → P S' = P S :=
      fun S' S h1 h2 hs => hher S' S (isLadderSet_of_erase M h1) (isLadderSet_of_erase M h2) hs
    have h1 := ladProd_erase_one (γ := γ) hL hδ hP0 (eraseSet M E) hN hhN a
    have e1 : (eraseSet (eraseSet M E) {a}).maximalLadders = (eraseSet M (insert a E)).maximalLadders := by
      have := (iterIso M E {a}).maximalLadders_eq
      rw [Finset.union_comm, ← Finset.insert_eq] at this
      exact this.symm
    rw [e1] at h1
    rw [Finset.card_insert_of_notMem ha]
    have hpos : 0 ≤ (Real.log L ^ 2) ^ 2 := by positivity
    calc ladProd L γ δ P M.maximalLadders
        ≤ (Real.log L ^ 2) ^ (2 * E.card) * ladProd L γ δ P (eraseSet M E).maximalLadders := ih
      _ ≤ (Real.log L ^ 2) ^ (2 * E.card) * ((Real.log L ^ 2) ^ 2 *
            ladProd L γ δ P (eraseSet M (insert a E)).maximalLadders) := by gcongr
      _ = _ := by ring

/-- **O3 (R29 item 6)**: the ladder ratio `FamLad` holds for every family of clusters. -/
theorem famLad_of_hered {L γ δ : ℝ} (hL : Real.exp 1 ≤ L) (hδ : 0 < δ) {P : Finset V → ℝ} (hP0 : ∀ S, 0 ≤ P S)
    {c₀ : ℕ} (hc₀ : 4 ≤ c₀) (M : Molecule V D) (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4)
    (hher : ∀ S' S, M.IsLadderSet S' → M.IsLadderSet S → S' ⊆ S → P S' = P S) (𝒦 : Finset (Finset V)) :
    FamLad L γ δ P c₀ M 𝒦 := by
  intro 𝒜 _ K _ _
  have hlog1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  set N := eraseSet M (𝒜.biUnion id) with hN
  have hN4 : ∀ b ∈ N.atoms, N.deg b ≤ 4 := fun b hb =>
    le_trans (deg_erase_le (Finset.mem_sdiff.1 hb).2) (hM b (Finset.mem_sdiff.1 hb).1)
  have hhN : ∀ S' S, N.IsLadderSet S' → N.IsLadderSet S → S' ⊆ S → P S' = P S :=
    fun S' S h1 h2 hs => hher S' S (isLadderSet_of_erase M h1) (isLadderSet_of_erase M h2) hs
  have h1 := ladProd_erase_set (γ := γ) hL hδ hP0 N hN4 hhN K
  have e1 : (eraseSet N K).maximalLadders = (eraseSet M (𝒜.biUnion id ∪ K)).maximalLadders :=
    (iterIso M (𝒜.biUnion id) K).maximalLadders_eq.symm
  rw [e1] at h1
  refine le_trans h1 ?_
  have hpow : (Real.log L ^ 2) ^ (2 * K.card) ≤ Real.log L ^ (c₀ * (K.card + eDart M K)) := by
    rw [← pow_mul]
    refine pow_le_pow_right₀ hlog1 ?_
    nlinarith [Nat.zero_le (eDart M K)]
  have hnn : 0 ≤ ladProd L γ δ P (eraseSet M (𝒜.biUnion id ∪ K)).maximalLadders :=
    Finset.prod_nonneg fun S _ => pow_nonneg (le_trans zero_le_one (ladderWeight_bounds hL hδ (hP0 S)).1) _
  exact mul_le_mul_of_nonneg_right hpow hnn

end WaveTurbulence.FinalCountG3
