/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a-G port of main `WaveTurbulence.Foundations.Stage1.Represents.RepVE2` (sha256 in COPIED-SHA256SUMS-G) over 𝒱_γ:
-- the chain assembly is L5b's `Famb.VineEstS2.CLChainAssemblyΓ γ`, the cohmol groups of a piece are L5b's `famGroups`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Represents.RepVE1
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.GammaLow.Famb.Family
public import WaveTurbulence.Foundations.GammaLow.Famb.VineEstS2.ChainPieces
public import WaveTurbulence.Foundations.GammaLow.Famc.ClassCount.TVineFacts
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RealizationIso
public import WaveTurbulence.Foundations.Stage1.Represents.RepVE2
import Mathlib.Tactic
/-!
# S2 REPRESENTS, VINE-E over `𝒱_γ`: the vine part of `g_sk` is bounded by the cohmol indices of the unit chains

`vineIncoh_eq_famGroups`: the incoherency index `vineIncoh γ` of (the atoms of) a chain piece is the index of its cohmol
groups `famGroups γ` (L5b, TARGET Def `cohmol`): for a bad vine (I)/(II) both are the index of a realization
(realization independence, main's `VineA.realized_index_eq_of_atoms`); for a T-vine both count the incoherent pieces
(L5c's `vineIncoh_tvine`). `sum_vineIncoh_le_cohmol`: `Σ_{T ∈ unitIngredients} vineIncoh T ≤ Σ_j Σ_i` (index of the
groups of piece `i` of `B₀ j`), given that every ingredient is an ingredient of the block of some unit `j` (`hcov`).
`card_bad_le`: the same for `bskOf` against the bad labels of the pieces (a T-vine is never bad: `2m + 5` atoms against
the even atom count of (I)/(II)).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama.Represents
open Finset WaveTurbulence WaveTurbulence.GammaLow.FinalCount WaveTurbulence.RegRed

variable {w : ℕ} {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

/-- A piece of a chain assembly over `𝒱_γ` (`γ ≤ 1/2`) is a bad vine (I)/(II) at its joints, or a T-vine there. -/
theorem chainPiece_cases {G : Garden w} (P : Famb.VineEstS2.ChainPieceΓ γ G.molecule) :
    G.molecule.IsVine .I P.atoms P.upper P.lower ∨ G.molecule.IsVine .II P.atoms P.upper P.lower ∨
      G.molecule.IsTVine P.atoms P.upper P.lower := by
  have hγ : γ ≤ 1 / 2 := Fact.out
  rcases P.vine with ⟨-, h⟩ | ⟨hγ', -⟩
  · exact h
  · exact absurd hγ (not_le.mpr hγ')

/-- The index of a realization is the index of its group set. -/
theorem realizedIncoherencyIndex_eq_groupIncoherency {G : Garden w} {X : VineType} {S : Finset (GBranch G.tree)}
    {a b : GBranch G.tree} (r : Vine.VineRealization G.molecule X S a b) (layer0 : GBranch G.tree → ℕ) :
    Vine.realizedIncoherencyIndex r layer0 = Famb.groupIncoherency (Vine.Param.realizedGroupSet r) layer0 := by
  classical
  rw [VineEstS4.realizedIncoherencyIndex_eq_card]
  unfold Famb.groupIncoherency
  congr 1

/-- **The index of a chain piece** (realization independence for (I)/(II), pieces for T-vines). -/
theorem vineIncoh_eq_famGroups {G : Garden w} (P : Famb.VineEstS2.ChainPieceΓ γ G.molecule)
    (layer0 : GBranch G.tree → ℕ) :
    vineIncoh γ G layer0 P.atoms =
      Famb.groupIncoherency (Famb.famGroups γ G.molecule P.atoms P.upper P.lower) layer0 := by
  classical
  have hγ : γ ≤ 1 / 2 := Fact.out
  have hB := P.isBlock
  by_cases hbad : G.molecule.IsVine .I P.atoms P.upper P.lower ∨ G.molecule.IsVine .II P.atoms P.upper P.lower
  · obtain ⟨X, hXb, hX⟩ : ∃ X : VineType, X.IsBad = true ∧ G.molecule.IsVine X P.atoms P.upper P.lower := by
      rcases hbad with h | h
      · exact ⟨.I, rfl, h⟩
      · exact ⟨.II, rfl, h⟩
    have hfam : ∃ (Y : VineType) (r : Vine.VineRealization G.molecule Y P.atoms P.upper P.lower),
        Famb.famGroups γ G.molecule P.atoms P.upper P.lower = Vine.Param.realizedGroupSet r := by
      by_cases hI : G.molecule.IsVine .I P.atoms P.upper P.lower
      · exact ⟨_, _, by unfold Famb.famGroups; rw [dif_pos hI]⟩
      · have hII : G.molecule.IsVine .II P.atoms P.upper P.lower := hbad.resolve_left hI
        exact ⟨_, _, by unfold Famb.famGroups; rw [dif_neg hI, dif_pos hII]⟩
    obtain ⟨Y, r, hr⟩ := hfam
    have hv : ∃ X p q, X.IsBad = true ∧ G.molecule.IsVine X P.atoms p q := ⟨X, _, _, hXb, hX⟩
    unfold vineIncoh
    rw [dif_pos hv, hr, ← realizedIncoherencyIndex_eq_groupIncoherency]
    exact VineA.realized_index_eq_of_atoms _ r hv.choose_spec.choose_spec.choose_spec.2.1 hB layer0
  · have hI : ¬ G.molecule.IsVine .I P.atoms P.upper P.lower := fun h => hbad (Or.inl h)
    have hII : ¬ G.molecule.IsVine .II P.atoms P.upper P.lower := fun h => hbad (Or.inr h)
    have hT : G.molecule.IsTVine P.atoms P.upper P.lower :=
      ((chainPiece_cases P).resolve_left hI).resolve_left hII
    rw [Famc.ClassCount.vineIncoh_tvine γ G layer0 hT]
    have hfam : Famb.famGroups γ G.molecule P.atoms P.upper P.lower =
        G.molecule.tvineGroups P.atoms P.upper P.lower := by
      unfold Famb.famGroups; rw [dif_neg hI, dif_neg hII, if_pos hγ]
    rw [hfam]
    unfold Famc.tvineIncoherency Famb.groupIncoherency
    congr 1
    ext g
    simp only [Finset.mem_filter]

theorem vineIncoh_eq_piece {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : Famb.VineEstS2.CLChainAssemblyΓ γ G R n) (i : Fin n)
    (layer0 : GBranch G.tree → ℕ) :
    vineIncoh γ G layer0 (Famb.VineEstS2.assemblyPieceAtΓ B i).atoms =
      Famb.groupIncoherency (Famb.famGroups γ G.molecule (Famb.VineEstS2.assemblyPieceAtΓ B i).atoms
        (Famb.VineEstS2.assemblyPieceAtΓ B i).upper (Famb.VineEstS2.assemblyPieceAtΓ B i).lower) layer0 :=
  vineIncoh_eq_famGroups _ layer0

theorem ingredient_piece {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {R : CLRegionData G U a b} {n : ℕ} (B : Famb.VineEstS2.CLChainAssemblyΓ γ G R n) {T : Finset (GBranch G.tree)}
    (hI : IsIngredientG γ G.molecule U T) : ∃ i : Fin n, (Famb.VineEstS2.assemblyPieceAtΓ B i).atoms = T := by
  obtain ⟨L, hs, -, -, h2⟩ := assemblyPieces_spine B
  obtain ⟨p, q, hm | hm⟩ := isIngredient_vc (Mole.garden_isMolecule G) B.isBlock hs hI
  · exact h2 T p q hm
  · exact h2 T q p hm

/-- A chain piece whose atom set is a bad vine set (for some joints) is a bad vine at its own joints. -/
theorem chainPiece_isBadVine_of_badSet {G : Garden w} (P : Famb.VineEstS2.ChainPieceΓ γ G.molecule)
    (h : RedSplice.IsBadVineSet G P.atoms) : G.molecule.IsBadVine P.atoms P.upper P.lower := by
  obtain ⟨X, p, q, hX, hv⟩ := h
  rcases chainPiece_cases P with hI | hII | hT
  · exact Or.inl hI
  · exact Or.inr hII
  · exfalso
    obtain ⟨m, hm⟩ := Famc.ClassCount.tvine_card_odd hT
    obtain ⟨k, hk⟩ := (Represents.isBad_iff_even hv).mp hX
    omega

section CoverMk
variable {G : Garden w} {Mk : Set (CLVineG γ G)} (σ : RedSplice.Prescription G) {J₀ : Type} [Fintype J₀]
  {U₀ : J₀ → Finset (GBranch G.tree)}
  {a₀ b₀ : J₀ → GBranch G.tree} {R₀ : ∀ j, CLRegionData G (U₀ j) (a₀ j) (b₀ j)} {n₀ : J₀ → ℕ}
  (B₀ : ∀ j, Famb.VineEstS2.CLChainAssemblyΓ γ G (R₀ j) (n₀ j))
  (hcov : ∀ T ∈ unitIngredients γ G σ Mk, ∃ j, IsIngredientG γ G.molecule (U₀ j) T)

include hcov in
/-- B1b (Mk-general form of `exists_piece_index`). -/
theorem exists_piece_indexMk :
    ∀ T ∈ unitIngredients γ G σ Mk, ∃ x : (Σ j, Fin (n₀ j)),
      (Famb.VineEstS2.assemblyPieceAtΓ (B₀ x.1) x.2).atoms = T := by
  intro T hT
  obtain ⟨j, hj⟩ := hcov T hT
  obtain ⟨i, hi⟩ := ingredient_piece (B₀ j) hj
  exact ⟨⟨j, i⟩, hi⟩

include hcov in
/-- B1b (Mk-general form of `sum_vineIncoh_le_cohmol`). -/
theorem sum_vineIncoh_le_cohmolMk (layer0 : GBranch G.tree → ℕ) :
    ∑ T ∈ (Set.toFinite (unitIngredients γ G σ Mk)).toFinset, vineIncoh γ G layer0 T ≤
      ∑ j, ∑ i : Fin (n₀ j), Famb.groupIncoherency (Famb.famGroups γ G.molecule
        (Famb.VineEstS2.assemblyPieceAtΓ (B₀ j) i).atoms (Famb.VineEstS2.assemblyPieceAtΓ (B₀ j) i).upper
        (Famb.VineEstS2.assemblyPieceAtΓ (B₀ j) i).lower) layer0 := by
  classical
  set Ing := (Set.toFinite (unitIngredients γ G σ Mk)).toFinset with hIng
  have hmem : ∀ T ∈ Ing, T ∈ unitIngredients γ G σ Mk := fun T hT => (Set.Finite.mem_toFinset _).1 hT
  rcases isEmpty_or_nonempty (Σ j, Fin (n₀ j)) with hE | hN
  · have : Ing = ∅ := Finset.eq_empty_of_forall_notMem fun T hT => by
      obtain ⟨x, -⟩ := exists_piece_indexMk σ B₀ hcov T (hmem T hT)
      exact hE.elim x
    rw [this]; simp
  choose! idx hidx using exists_piece_indexMk σ B₀ hcov
  have hinj : Set.InjOn idx (Ing : Set (Finset (GBranch G.tree))) := by
    intro T hT T' hT' h
    rw [← hidx T (hmem T hT), ← hidx T' (hmem T' hT'), h]
  let g : (Σ j, Fin (n₀ j)) → ℕ := fun x => Famb.groupIncoherency (Famb.famGroups γ G.molecule
    (Famb.VineEstS2.assemblyPieceAtΓ (B₀ x.1) x.2).atoms (Famb.VineEstS2.assemblyPieceAtΓ (B₀ x.1) x.2).upper
    (Famb.VineEstS2.assemblyPieceAtΓ (B₀ x.1) x.2).lower) layer0
  have e1 : ∑ T ∈ Ing, vineIncoh γ G layer0 T = ∑ T ∈ Ing, g (idx T) := by
    refine Finset.sum_congr rfl fun T hT => ?_
    conv_lhs => rw [← hidx T (hmem T hT)]
    exact vineIncoh_eq_piece (B₀ (idx T).1) (idx T).2 layer0
  rw [e1, ← Finset.sum_image (f := g) hinj]
  calc ∑ x ∈ Ing.image idx, g x ≤ ∑ x : (Σ j, Fin (n₀ j)), g x :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = _ := Fintype.sum_sigma g

include hcov in
/-- B1b (Mk-general form of `card_bad_le`): `b_sk` is at most the number of pieces with a bad label. -/
theorem card_bad_leMk (hM9 : Famb.NormalChartSupply γ) :
    bskOf γ G σ Mk ≤ ∑ j, (Finset.univ.filter fun i : Fin (n₀ j) =>
      (Famb.VineEstS2.assemblyPieceAtΓ (B₀ j) i).label.IsBad = true).card := by
  classical
  set Ing := (Set.toFinite (unitIngredients γ G σ Mk)).toFinset with hIng
  have hmem : ∀ T ∈ Ing, T ∈ unitIngredients γ G σ Mk := fun T hT => (Set.Finite.mem_toFinset _).1 hT
  rcases isEmpty_or_nonempty (Σ j, Fin (n₀ j)) with hE | hN
  · have hIe : Ing = ∅ := Finset.eq_empty_of_forall_notMem fun T hT => by
      obtain ⟨x, -⟩ := exists_piece_indexMk σ B₀ hcov T (hmem T hT)
      exact hE.elim x
    have hb0 : bskOf γ G σ Mk = 0 := by
      unfold bskOf
      rw [Set.ncard_eq_zero (Set.toFinite _)]
      ext T
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hT
      have : T ∈ Ing := (Set.Finite.mem_toFinset (Set.toFinite (unitIngredients γ G σ Mk))).2 hT
      rw [hIe] at this
      simp at this
    rw [hb0]; exact Nat.zero_le _
  choose! idx hidx using exists_piece_indexMk σ B₀ hcov
  let Bad : Finset (Finset (GBranch G.tree)) := Ing.filter (fun T => RedSplice.IsBadVineSet G T)
  have hb : bskOf γ G σ Mk = Bad.card := by
    unfold bskOf
    rw [← Set.ncard_coe_finset, Finset.coe_filter]
    congr 1
    ext T
    simp [Bad, Ing, Set.Finite.mem_toFinset]
  rw [hb]
  let S : Finset (Σ j, Fin (n₀ j)) := Finset.univ.filter fun x =>
    (Famb.VineEstS2.assemblyPieceAtΓ (B₀ x.1) x.2).label.IsBad = true
  have hS : S.card = ∑ j, (Finset.univ.filter fun i : Fin (n₀ j) =>
      (Famb.VineEstS2.assemblyPieceAtΓ (B₀ j) i).label.IsBad = true).card := by
    simp only [S]
    rw [Finset.card_filter, Fintype.sum_sigma (fun x : (Σ j, Fin (n₀ j)) =>
      if (Famb.VineEstS2.assemblyPieceAtΓ (B₀ x.1) x.2).label.IsBad = true then 1 else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.card_filter]
  rw [← hS]
  refine Finset.card_le_card_of_injOn idx ?_ ?_
  · intro T hT
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Bad] at hT
    obtain ⟨hTI, hbadT⟩ := hT
    set P := Famb.VineEstS2.assemblyPieceAtΓ (B₀ (idx T).1) (idx T).2 with hP
    have hPa : P.atoms = T := hidx T (hmem T hTI)
    have hbadP : RedSplice.IsBadVineSet G P.atoms := hPa ▸ hbadT
    simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    exact (P.label_isBad hM9 (Mole.garden_isMolecule G)).mpr (chainPiece_isBadVine_of_badSet P hbadP)
  · intro T hT T' hT' h
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Bad] at hT hT'
    rw [← hidx T (hmem T hT.1), ← hidx T' (hmem T' hT'.1), h]

end CoverMk

section Cover
variable {G : Garden w} (σ : RedSplice.Prescription G) {J₀ : Type} [Fintype J₀] {U₀ : J₀ → Finset (GBranch G.tree)}
  {a₀ b₀ : J₀ → GBranch G.tree} {R₀ : ∀ j, CLRegionData G (U₀ j) (a₀ j) (b₀ j)} {n₀ : J₀ → ℕ}
  (B₀ : ∀ j, Famb.VineEstS2.CLChainAssemblyΓ γ G (R₀ j) (n₀ j))
  (hcov : ∀ T ∈ unitIngredients γ G σ, ∃ j, IsIngredientG γ G.molecule (U₀ j) T)

end Cover

end WaveTurbulence.GammaLow.Fama.Represents
