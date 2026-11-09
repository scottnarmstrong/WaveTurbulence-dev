/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCLadProd
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCGain
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCLadProd`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 13: ladders of the removed vine against the chart rungs.

Realisations of the maximal ladders of `K.vc` inside the block `S`; joints are never ladder atoms; a ladder atom
equal to `rx j` forces the whole rung to be the chart rung `j`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Interior
variable {M : Molecule V D} {S : Finset V} {a b : V} (hB : M.IsBlock S a b) {m : ℕ} {u v : Fin (m + 1) → V}
include hB

end Interior

section ChartRung
variable {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
  (A : FullVineChart M X S a b) {m : ℕ} {u v : Fin (m + 1) → V}
include hB

end ChartRung

section Realization
variable {M : Molecule V D} {m : ℕ} {u v : Fin (m + 1) → V}

end Realization

section Classify
variable {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (hB : M.IsBlock S a b)
  (A : FullVineChart M X S a b) {m : ℕ} {u v : Fin (m + 1) → V}
include hB

end Classify

section Gain
variable {M : Molecule V D} (K : VineCut g M) (hB : M.IsBlock K.C.atoms K.C.upper K.C.lower)
  (hM : ∀ x ∈ M.atoms, M.deg x ≤ 4) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)
  (P : Finset V → ℝ)

/-- The maximal ladder (of nonzero scale) of the removed vine that contains the chart rung `j`, if any. -/
noncomputable def gl (j : Fin A.indexing.shape.m) : Option (Finset V) :=
  if hh : ∃ S' ∈ K.vc.maximalLadders, P S' ≠ 0 ∧ rx A j ∈ S' ∧ A.junction ≠ some j then
    some (Classical.choose hh) else none

theorem gl_spec {j : Fin A.indexing.shape.m} {S' : Finset V} (h : gl K A P j = some S') :
    S' ∈ K.vc.maximalLadders ∧ P S' ≠ 0 ∧ rx A j ∈ S' ∧ A.junction ≠ some j := by
  unfold gl at h
  split_ifs at h with hh
  · have := Classical.choose_spec hh
    rw [← Option.some.inj h]
    exact this

include hB hM in
theorem gl_eq {j : Fin A.indexing.shape.m} {S' : Finset V} (h1 : S' ∈ K.vc.maximalLadders) (h2 : P S' ≠ 0)
    (h3 : rx A j ∈ S') (h4 : A.junction ≠ some j) : gl K A P j = some S' := by
  have hh : ∃ S' ∈ K.vc.maximalLadders, P S' ≠ 0 ∧ rx A j ∈ S' ∧ A.junction ≠ some j := ⟨S', h1, h2, h3, h4⟩
  unfold gl
  rw [dif_pos hh]
  congr 1
  obtain ⟨hS0, -, hx0, -⟩ := Classical.choose_spec hh
  by_contra hne
  have := vc_ladders_disjoint K hB hM hS0 h1 hne
  exact Finset.disjoint_left.mp this hx0 h3

include hB hM in
theorem ladder_deficit {S' : Finset V} (hS' : S' ∈ K.vc.maximalLadders) (hP : P S' ≠ 0) :
    2 * (Molecule.ladderLength S' + 1 -
        (Finset.univ.filter fun j => gl K A P j = some S').card) ≤ (S' ∩ specialSet A).card := by
  obtain ⟨m, u, v, hlad, hat⟩ := mem_maximalLadders_isLadderSet hS'
  obtain ⟨hlad', hS⟩ := vc_isLadder K hB hlad
  have hz : Molecule.ladderLength S' = m := ladderLength_eq hlad' hat
  rw [hz]
  obtain ⟨hne_u, hne_v, hnuv⟩ := ladder_ne hlad'
  set c := (Finset.univ.filter fun j => gl K A P j = some S').card with hcdef
  let chartI : Finset (Fin (m + 1)) :=
    Finset.univ.filter fun i => ∃ j, A.junction ≠ some j ∧ ChartAt A u v i j
  have hc : chartI.card ≤ c := by
    refine Finset.card_le_card_of_forall_subsingleton
      (fun i j => A.junction ≠ some j ∧ ChartAt A u v i j) ?_ ?_
    · intro i hi
      obtain ⟨j, hj, hch⟩ := (Finset.mem_filter.mp hi).2
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hj, hch⟩
      apply gl_eq K hB hM A P hS' hP _ hj
      rw [← hat, mem_ladderAtoms]
      rcases hch with ⟨h1, -⟩ | ⟨-, h2⟩
      · left; exact ⟨i, h1⟩
      · right; exact ⟨i, h2⟩
    · intro j _ i hi i' hi'
      obtain ⟨-, -, hch⟩ := hi
      obtain ⟨-, -, hch'⟩ := hi'
      by_contra hne
      rcases hch with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases hch' with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · exact hne_u i i' hne (a1.trans b1.symm)
      · exact hnuv i i' (a1.trans b2.symm)
      · exact hnuv i' i (b1.trans a2.symm)
      · exact hne_u i i' hne (a1.trans b1.symm)
  let badI : Finset (Fin (m + 1)) := Finset.univ.filter fun i => ¬ ∃ j, A.junction ≠ some j ∧ ChartAt A u v i j
  have hsum : chartI.card + badI.card = m + 1 := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (m + 1))))
      (fun i => ∃ j, A.junction ≠ some j ∧ ChartAt A u v i j)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  have hbad : ∀ i ∈ badI, u i ∈ S' ∩ specialSet A ∧ v i ∈ S' ∩ specialSet A := by
    intro i hi
    have hni := (Finset.mem_filter.mp hi).2
    rcases rung_class hB A hlad' hS i with h | ⟨h1, h2⟩
    · exact absurd h hni
    · refine ⟨Finset.mem_inter.mpr ⟨?_, h1⟩, Finset.mem_inter.mpr ⟨?_, h2⟩⟩
      · rw [← hat, mem_ladderAtoms]; left; exact ⟨i, rfl⟩
      · rw [← hat, mem_ladderAtoms]; right; exact ⟨i, rfl⟩
  have hB2 : (badI.image u ∪ badI.image v).card = 2 * badI.card := by
    rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun x y hxy => by_contra fun hh => hne_u x y hh hxy),
      Finset.card_image_of_injective _ (fun x y hxy => by_contra fun hh => hne_v x y hh hxy)]
    · ring
    · rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hz
      obtain ⟨i', -, hi'⟩ := Finset.mem_image.mp hz'
      exact hnuv i i' (hi.trans hi'.symm)
  have hsub : badI.image u ∪ badI.image v ⊆ S' ∩ specialSet A := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact (hbad i hi).1
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact (hbad i hi).2
  have := Finset.card_le_card hsub
  omega

include hB hM in
/-- The ladder product of the removed vine is controlled by the chart-rung weights: up to `(log L)^4`
(at most two rungs of special atoms), `∏ 𝔛_j^{z_j} ≤ (log L)^4 ∏_{rungs} 𝔛`. -/
theorem ladderProdVC_le_gain (L γ δ : ℝ) (hL : Real.exp 1 ≤ L) (hδ : 0 ≤ δ) (hP0 : ∀ S, 0 ≤ P S) :
    K.ladderProdVC L γ δ P ≤ Real.log L ^ 4 *
      ∏ j : Fin A.indexing.shape.m, (gl K A P j).elim 1 (fun S' => Molecule.ladderWeight L γ δ (P S')) := by
  have hlog1 : 1 ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos 1) hL
    rwa [Real.log_exp] at this
  set ML := K.vc.maximalLadders with hML
  set MLp := ML.filter (fun S' => P S' ≠ 0) with hMLp
  set Wt : Finset V → ℝ := fun S' => Molecule.ladderWeight L γ δ (P S') with hWt
  have hW1 : ∀ S', 1 ≤ Wt S' := fun S' => FinalCount.ladderWeight_ge_one L γ δ (P S') hL hδ (hP0 S')
  have hWY : ∀ S', Wt S' ≤ Real.log L ^ 2 := fun S' => FinalCount.ladderWeight_le L γ δ (P S')
  have hlog2 : 1 ≤ Real.log L ^ 2 := one_le_pow₀ hlog1
  -- Step A
  have hA : K.ladderProdVC L γ δ P = ∏ S' ∈ MLp, Wt S' ^ Molecule.ladderLength S' := by
    unfold VineCut.ladderProdVC
    symm
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro S' hS' hn
    have : P S' = 0 := by
      by_contra hne; exact hn (Finset.mem_filter.mpr ⟨hS', hne⟩)
    have h1 : Wt S' = 1 := by
      simp only [hWt, Molecule.ladderWeight, this, mul_zero, add_zero]
      exact min_eq_right hlog2
    simp [h1]
  -- Step B
  have hT : ∀ j S', gl K A P j = some S' → S' ∈ MLp := by
    intro j S' h
    obtain ⟨h1, h2, -, -⟩ := gl_spec K A P h
    exact Finset.mem_filter.mpr ⟨h1, h2⟩
  have hB' := prod_fiber_weights (gl K A P) Wt MLp hT
  have hB'' : (∏ j : Fin A.indexing.shape.m, (gl K A P j).elim 1 (fun S' => Molecule.ladderWeight L γ δ (P S'))) =
      ∏ S' ∈ MLp, Wt S' ^ (Finset.univ.filter fun j => gl K A P j = some S').card := hB'
  rw [hA, hB'']
  -- Step C
  set c : Finset V → ℕ := fun S' => (Finset.univ.filter fun j => gl K A P j = some S').card with hc
  set b : Finset V → ℕ := fun S' => Molecule.ladderLength S' + 1 - c S' with hb
  have hdef : ∀ S' ∈ MLp, 2 * b S' ≤ (S' ∩ specialSet A).card := by
    intro S' hS'
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hS'
    exact ladder_deficit K hB hM A P h1 h2
  have hsumb : ∑ S' ∈ MLp, b S' ≤ 2 := by
    have h1 : ∑ S' ∈ MLp, (S' ∩ specialSet A).card ≤ 5 := by
      have hdisj : (MLp : Set (Finset V)).PairwiseDisjoint (fun S' => S' ∩ specialSet A) := by
        intro S' hS' S'' hS'' hne
        have hd := vc_ladders_disjoint K hB hM (Finset.mem_filter.mp hS').1 (Finset.mem_filter.mp hS'').1 hne
        exact Finset.disjoint_left.mpr fun z hz hz' =>
          Finset.disjoint_left.mp hd (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz').1
      rw [← Finset.card_biUnion hdisj]
      refine (Finset.card_le_card ?_).trans (card_specialSet A)
      intro z hz
      obtain ⟨S', -, hzS⟩ := Finset.mem_biUnion.mp hz
      exact (Finset.mem_inter.mp hzS).2
    have h2 : 2 * ∑ S' ∈ MLp, b S' ≤ ∑ S' ∈ MLp, (S' ∩ specialSet A).card := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum hdef
    omega
  have key := prod_pow_le_of_deficit MLp Wt (Real.log L ^ 2) (fun S' => Molecule.ladderLength S') c b
    (fun S' _ => hW1 S') (fun S' _ => hWY S') hlog2 (fun S' _ => by simp only [hb]; omega) hsumb
  calc ∏ S' ∈ MLp, Wt S' ^ Molecule.ladderLength S' ≤ (Real.log L ^ 2) ^ 2 * ∏ S' ∈ MLp, Wt S' ^ c S' := key
    _ = Real.log L ^ 4 * ∏ S' ∈ MLp, Wt S' ^ (Finset.univ.filter fun j => gl K A P j = some S').card := by
        rw [← pow_mul]

end Gain

end WaveTurbulence.GammaLow.FinalCount.Step1
