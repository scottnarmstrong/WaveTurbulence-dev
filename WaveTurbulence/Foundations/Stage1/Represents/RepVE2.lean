/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVE1
public import WaveTurbulence.Foundations.Vine.A.VineChosenIncoherency
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-E: the vine part of `g_sk` is bounded by the cohmol indices of the unit chains

`vineIncoh_eq_piece`: the chosen vine incoherency index of a chain piece is its `pieceRealization` index (realization
independence, VINE-A).  `sum_vineIncoh_le_cohmol`: `Σ_{T ∈ unitIngredients} vineIncoh T ≤ Σ_j cohmolIndex B_j`, given that every
ingredient is an ingredient of the block of some unit `j` whose chain assembly is `B₀ j` (`hcov`).
`card_bad_le`: the same for `bskOf` against `#{i | nor i = false}`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.RedSplice WaveTurbulence.VineEstS2 WaveTurbulence.Vine
  WaveTurbulence.RegRed WaveTurbulence.VineEstS3 WaveTurbulence.Stage1

variable {w : ℕ}

theorem vineIncoh_eq_piece {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n) (i : Fin n) (layer0 : GBranch G.tree → ℕ) :
    vineIncoh G layer0 (assemblyPieceAt B i).atoms =
      realizedIncoherencyIndex (pieceRealization B i) layer0 := by
  classical
  have hv : ∃ X p q, G.molecule.IsVine X (assemblyPieceAt B i).atoms p q :=
    ⟨_, _, _, (assemblyPieceAt B i).vine⟩
  unfold vineIncoh
  rw [dif_pos hv]
  refine VineA.realized_index_eq_of_atoms _ (pieceRealization B i) hv.choose_spec.choose_spec.choose_spec.1
    (assemblyPieceAt B i).vine.1 layer0

theorem ingredient_piece {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : CLChainAssembly G R n) {T : Finset (GBranch G.tree)}
    (hI : IsIngredient G.molecule U T) : ∃ i : Fin n, (assemblyPieceAt B i).atoms = T := by
  obtain ⟨L, hs, -, -, h2⟩ := assemblyPieces_spine B
  obtain ⟨p, q, hm | hm⟩ := isIngredient_vc (Mole.garden_isMolecule G) B.isBlock hs hI
  · exact h2 T p q hm
  · exact h2 T q p hm

section Cover
variable {G : Garden w} (σ : Prescription G) {J₀ : Type} [Fintype J₀] {U₀ : J₀ → Finset (GBranch G.tree)}
  {a₀ b₀ : J₀ → GBranch G.tree} {R₀ : ∀ j, CLRegionData G (U₀ j) (a₀ j) (b₀ j)} {n₀ : J₀ → ℕ}
  (B₀ : ∀ j, CLChainAssembly G (R₀ j) (n₀ j))
  (hcov : ∀ T ∈ unitIngredients G σ, ∃ j, IsIngredient G.molecule (U₀ j) T)

include hcov in
theorem exists_piece_index :
    ∀ T ∈ unitIngredients G σ, ∃ x : (Σ j, Fin (n₀ j)), (assemblyPieceAt (B₀ x.1) x.2).atoms = T := by
  intro T hT
  obtain ⟨j, hj⟩ := hcov T hT
  obtain ⟨i, hi⟩ := ingredient_piece (B₀ j) hj
  exact ⟨⟨j, i⟩, hi⟩

include hcov in
theorem sum_vineIncoh_le_cohmol (layer0 : GBranch G.tree → ℕ) :
    ∑ T ∈ (Set.toFinite (unitIngredients G σ)).toFinset, vineIncoh G layer0 T ≤
      ∑ j, ∑ i : Fin (n₀ j), realizedIncoherencyIndex (pieceRealization (B₀ j) i) layer0 := by
  classical
  set Ing := (Set.toFinite (unitIngredients G σ)).toFinset with hIng
  have hmem : ∀ T ∈ Ing, T ∈ unitIngredients G σ := fun T hT => (Set.Finite.mem_toFinset _).1 hT
  rcases isEmpty_or_nonempty (Σ j, Fin (n₀ j)) with hE | hN
  · have : Ing = ∅ := Finset.eq_empty_of_forall_notMem fun T hT => by
      obtain ⟨x, -⟩ := exists_piece_index σ B₀ hcov T (hmem T hT)
      exact hE.elim x
    rw [this]; simp
  choose! idx hidx using exists_piece_index σ B₀ hcov
  have hinj : Set.InjOn idx (Ing : Set (Finset (GBranch G.tree))) := by
    intro T hT T' hT' h
    rw [← hidx T (hmem T hT), ← hidx T' (hmem T' hT'), h]
  let g : (Σ j, Fin (n₀ j)) → ℕ := fun x => realizedIncoherencyIndex (pieceRealization (B₀ x.1) x.2) layer0
  have e1 : ∑ T ∈ Ing, vineIncoh G layer0 T = ∑ T ∈ Ing, g (idx T) := by
    refine Finset.sum_congr rfl fun T hT => ?_
    conv_lhs => rw [← hidx T (hmem T hT)]
    exact vineIncoh_eq_piece (B₀ (idx T).1) (idx T).2 layer0
  rw [e1, ← Finset.sum_image (f := g) hinj]
  calc ∑ x ∈ Ing.image idx, g x ≤ ∑ x : (Σ j, Fin (n₀ j)), g x :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := Fintype.sum_sigma g

include hcov in
theorem card_bad_le :
    bskOf G σ ≤ ∑ j, (Finset.univ.filter fun i : Fin (n₀ j) => (assemblyPieceAt (B₀ j) i).vineType.IsBad = true).card := by
  classical
  set Ing := (Set.toFinite (unitIngredients G σ)).toFinset with hIng
  have hmem : ∀ T ∈ Ing, T ∈ unitIngredients G σ := fun T hT => (Set.Finite.mem_toFinset _).1 hT
  rcases isEmpty_or_nonempty (Σ j, Fin (n₀ j)) with hE | hN
  · have hIe : Ing = ∅ := Finset.eq_empty_of_forall_notMem fun T hT => by
      obtain ⟨x, -⟩ := exists_piece_index σ B₀ hcov T (hmem T hT)
      exact hE.elim x
    have hb0 : bskOf G σ = 0 := by
      unfold bskOf
      rw [Set.ncard_eq_zero (Set.toFinite _)]
      ext T
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hT
      have : T ∈ Ing := (Set.Finite.mem_toFinset (Set.toFinite (unitIngredients G σ))).2 hT
      rw [hIe] at this
      simp at this
    rw [hb0]; exact Nat.zero_le _
  choose! idx hidx using exists_piece_index σ B₀ hcov
  let Bad : Finset (Finset (GBranch G.tree)) := Ing.filter (fun T => IsBadVineSet G T)
  have hb : bskOf G σ = Bad.card := by
    unfold bskOf
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    congr 1
    ext T
    simp [Bad, Ing, Set.Finite.mem_toFinset]
  rw [hb]
  let S : Finset (Σ j, Fin (n₀ j)) := Finset.univ.filter fun x => (assemblyPieceAt (B₀ x.1) x.2).vineType.IsBad = true
  have hS : S.card = ∑ j, (Finset.univ.filter fun i : Fin (n₀ j) => (assemblyPieceAt (B₀ j) i).vineType.IsBad = true).card := by
    simp only [S]
    rw [Finset.card_filter, Fintype.sum_sigma (fun x : (Σ j, Fin (n₀ j)) =>
      if (assemblyPieceAt (B₀ x.1) x.2).vineType.IsBad = true then 1 else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  rw [← hS]
  refine Finset.card_le_card_of_injOn idx ?_ ?_
  · intro T hT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Bad] at hT
    obtain ⟨hTI, X, p, q, hX, hv⟩ := hT
    have hpiece := (assemblyPieceAt (B₀ (idx T).1) (idx T).2).vine
    rw [hidx T (hmem T hTI)] at hpiece
    simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rw [isBad_unique hpiece hv]
    exact hX
  · intro T hT T' hT' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Bad] at hT hT'
    rw [← hidx T (hmem T hT.1), ← hidx T' (hmem T' hT'.1), h]

end Cover

end WaveTurbulence.Represents
