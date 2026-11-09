/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Layervine.First
public import WaveTurbulence.Foundations.LayerCnt.Multi
public import WaveTurbulence.Foundations.LayerCnt.LadderSum
public import WaveTurbulence.Foundations.Spine.CoarseSplicedDraft.LadderCounts
/-! # layervine′, first bound: `LayervineTVineFirst` (packet L5c)

TARGET L1519 for T-vines: at most three ladders (L3's `LaddersStatement`) carry the interior rung sequences of main's
multi-ladder bound `LayerCnt.multi_sum_le`; at most `13 + 4·3 = 25` atoms are outside their interiors; the number of
interior rungs is at most `m + 2`; the incoherency of each ladder is at most the T-vine incoherency index
(`ladder_incCnt_le_tvineIncoherency`). The constants are those of main's `layervine_bound` up to the exponents. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Famc
open Finset WaveTurbulence.LayerCnt WaveTurbulence.Vine

theorem mem_unionAll {V : Type} [DecidableEq V] {ls : List (Finset V)} {x : V} :
    x ∈ TVine.Struct.unionAll ls ↔ ∃ L ∈ ls, x ∈ L := by
  induction ls with
  | nil => simp [TVine.Struct.unionAll]
  | cons L ls ih =>
    simp only [TVine.Struct.unionAll, List.foldr_cons, mem_union, List.mem_cons] at ih ⊢
    constructor
    · rintro (h | h)
      · exact ⟨L, Or.inl rfl, h⟩
      · obtain ⟨L', hL', hx⟩ := ih.mp h
        exact ⟨L', Or.inr hL', hx⟩
    · rintro ⟨L', rfl | hL', hx⟩
      · exact Or.inl hx
      · exact Or.inr (ih.mpr ⟨L', hL', hx⟩)

/-- The numerical step: `(𝔇+1)^31 · 3^{2(m+2)+48𝔇(g+1)} ≤ 81 · 9^m · (2^31 3^48)^{𝔇(g+1)}`. -/
theorem layervine_nat_le (m 𝔇 g : ℕ) :
    (𝔇 + 1) ^ (25 + 2 * 3) * 3 ^ (2 * (m + 2) + 16 * 3 * 𝔇 * (g + 1)) ≤
      81 * 9 ^ m * (2 ^ 31 * 3 ^ 48) ^ (𝔇 * (g + 1)) := by
  have h1 : (𝔇 + 1) ^ (25 + 2 * 3) ≤ (2 ^ 31) ^ (𝔇 * (g + 1)) := by
    have : 𝔇 + 1 ≤ 2 ^ 𝔇 := Nat.lt_two_pow_self
    calc (𝔇 + 1) ^ (25 + 2 * 3) ≤ (2 ^ 𝔇) ^ 31 := Nat.pow_le_pow_left this _
      _ = (2 ^ 31) ^ 𝔇 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (2 ^ 31) ^ (𝔇 * (g + 1)) := Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ (by omega))
  have h2 : 3 ^ (2 * (m + 2) + 16 * 3 * 𝔇 * (g + 1)) = 81 * 9 ^ m * (3 ^ 48) ^ (𝔇 * (g + 1)) := by
    rw [show (81 : ℕ) = 3 ^ 4 by norm_num, show (9 : ℕ) = 3 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_add,
      ← pow_add]
    congr 1
    ring
  rw [h2, mul_pow]
  calc (𝔇 + 1) ^ (25 + 2 * 3) * (81 * 9 ^ m * (3 ^ 48) ^ (𝔇 * (g + 1)))
      ≤ (2 ^ 31) ^ (𝔇 * (g + 1)) * (81 * 9 ^ m * (3 ^ 48) ^ (𝔇 * (g + 1))) := Nat.mul_le_mul_right _ h1
    _ = 81 * 9 ^ m * ((2 ^ 31) ^ (𝔇 * (g + 1)) * (3 ^ 48) ^ (𝔇 * (g + 1))) := by ring

/-- **TARGET `layervine`, first bound, for T-vines** (from N3 Thm 6(iv) and N2 Prop 1.17(b)). -/
theorem layervineTVineFirst (hLad : LaddersInput) (hPS : PieceShapeInput) : LayervineTVineFirst := by
  intro B hB
  set X : ℝ := (2 : ℝ) ^ 31 * 3 ^ 48 * B ^ 80 with hX
  refine ⟨max 81 X, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro w G S a b hT m hm 𝔇 C₂ hC₂ g _hg 𝓕 hf hinj
  set C₀ : ℝ := max 81 X with hC₀
  set M := G.molecule with hMdef
  have hM : M.IsMolecule := Mole.garden_isMolecule G
  obtain ⟨ls, hlen, hls, hpw, hunc⟩ := hLad M hM S a b hT
  have hch : ∀ c : Fin ls.length, ∃ m' : ℕ, ∃ u v : Fin (m' + 1) → GBranch G.tree,
      M.IsLadder u v ∧ Molecule.ladderAtoms u v = ls.get c := fun c => (hls _ (List.get_mem ls c)).2
  choose mc uc vc hLc hAc using hch
  have hLS : ∀ c, Molecule.ladderAtoms (uc c) (vc c) ⊆ S := fun c => by
    rw [hAc c]; exact (hls _ (List.get_mem ls c)).1
  have hdisjL : ∀ c c' : Fin ls.length, c ≠ c' → Disjoint (ls.get c) (ls.get c') := by
    intro c c' hcc
    rcases lt_or_gt_of_ne hcc with h | h
    · exact List.pairwise_iff_get.mp hpw c c' h
    · exact (List.pairwise_iff_get.mp hpw c' c h).symm
  let Q : ∀ c : Fin ls.length, FullRungSequence M (mc c - 1) := fun c => ladderRungSeq M (hLc c)
  have hint : ∀ c, intAtoms (Q c).u (Q c).v (mc c - 1) ⊆ Molecule.ladderAtoms (uc c) (vc c) :=
    fun c => intAtoms_ladder_sub M (hLc c)
  have hS : ∀ c, intAtoms (Q c).u (Q c).v (mc c - 1) ⊆ S := fun c => (hint c).trans (hLS c)
  have hdisj : ∀ c c', c ≠ c' →
      Disjoint (intAtoms (Q c).u (Q c).v (mc c - 1)) (intAtoms (Q c').u (Q c').v (mc c' - 1)) := by
    intro c c' hcc
    have h := hdisjL c c' hcc
    rw [← hAc c, ← hAc c'] at h
    exact Finset.disjoint_of_subset_left (hint c) (Finset.disjoint_of_subset_right (hint c') h)
  have hN : Fintype.card (Fin ls.length) ≤ 3 := by simpa using hlen
  -- atoms outside the interiors
  have hr : (S \ allInt M Q).card ≤ 25 := by
    have hsub : S \ allInt M Q ⊆ (S \ TVine.Struct.unionAll ls) ∪
        univ.biUnion (fun c => Molecule.ladderAtoms (uc c) (vc c) \ intAtoms (Q c).u (Q c).v (mc c - 1)) := by
      intro x hx
      obtain ⟨hxS, hxI⟩ := mem_sdiff.mp hx
      by_cases hxU : x ∈ TVine.Struct.unionAll ls
      · obtain ⟨L, hL, hxL⟩ := mem_unionAll.mp hxU
        obtain ⟨c, rfl⟩ := List.get_of_mem hL
        refine mem_union_right _ (mem_biUnion.mpr ⟨c, mem_univ _, mem_sdiff.mpr ⟨by rw [hAc c]; exact hxL, ?_⟩⟩)
        intro h
        exact hxI (mem_biUnion.mpr ⟨c, mem_univ _, h⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hxS, hxU⟩)
    have hb : (univ.biUnion (fun c => Molecule.ladderAtoms (uc c) (vc c) \
        intAtoms (Q c).u (Q c).v (mc c - 1))).card ≤ 12 := by
      refine (card_biUnion_le).trans ?_
      calc ∑ c : Fin ls.length, (Molecule.ladderAtoms (uc c) (vc c) \ intAtoms (Q c).u (Q c).v (mc c - 1)).card
          ≤ ∑ _c : Fin ls.length, 4 := Finset.sum_le_sum (fun c _ => card_ends_le M (hLc c))
        _ = 4 * ls.length := by simp [mul_comm]
        _ ≤ 12 := by omega
    calc (S \ allInt M Q).card ≤ _ := card_le_card hsub
      _ ≤ (S \ TVine.Struct.unionAll ls).card + 12 := (card_union_le _ _).trans (by omega)
      _ ≤ 25 := by omega
  -- the number of interior rungs
  have hK : ∑ c, (mc c - 1) ≤ m + 2 := by
    have hcard : ∑ c, (2 * mc c + 2) ≤ 2 * m + 5 := by
      rw [← hm]
      calc ∑ c, (2 * mc c + 2) = ∑ c, (Molecule.ladderAtoms (uc c) (vc c)).card :=
            Finset.sum_congr rfl (fun c _ => (CoarseSpliced.card_ladderAtoms_ladder (hLc c)).symm)
        _ = (univ.biUnion fun c => Molecule.ladderAtoms (uc c) (vc c)).card := by
            rw [card_biUnion]
            intro c _ c' _ hcc
            have h := hdisjL c c' hcc
            rwa [← hAc c, ← hAc c'] at h
        _ ≤ S.card := card_le_card (biUnion_subset.mpr (fun c _ => hLS c))
    have : ∑ c, (mc c - 1) ≤ ∑ c, mc c := Finset.sum_le_sum (fun c _ => Nat.sub_le _ _)
    have h2 : ∑ c, (2 * mc c + 2) = 2 * ∑ c, mc c + 2 * Fintype.card (Fin ls.length) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, smul_eq_mul]; ring
    omega
  -- the layering family of incoherency index g
  set 𝓕' := 𝓕.filter (fun f => tvineIncoherency M S a b f = g) with h𝓕'
  have hf' : ∀ f ∈ 𝓕', (∀ x, f x ≤ 𝔇) ∧ ParentProp M f (depthB G) := by
    intro f hf0
    have hff := hf f (mem_filter.mp hf0).1
    exact ⟨hff.2, fun x hx => garden_parent_step G hff.1 x hx⟩
  have hG : ∀ f ∈ 𝓕', ∀ c, incCnt (fun i => f ((Q c).u i)) (fun i => f ((Q c).v i)) 1 (mc c - 1) ≤ g := by
    intro f hf0 c
    rw [← (mem_filter.mp hf0).2]
    exact ladder_incCnt_le_tvineIncoherency hPS hT (hLc c) (hLS c) f
  have hinj' : ∀ f ∈ 𝓕', ∀ f'' ∈ 𝓕', (∀ x ∈ S, f x = f'' x) → f = f'' :=
    fun f hf0 f'' hf1 h => hinj f (mem_filter.mp hf0).1 f'' (mem_filter.mp hf1).1 h
  have key := multi_sum_le M hM Q hS hdisj (depth := depthB G) (𝔇 := 𝔇) (G := g) hN hr hK B hB 𝓕' hf' hG hinj'
  have hpr : ∀ f : GBranch G.tree → ℕ,
      ∏ x ∈ bondsIn M S, B ^ dst (f (M.atom x)) (f (M.atom (M.mate x))) = B ^ bondExp M S f := fun f => by
    unfold bondExp; rw [Finset.prod_pow_eq_pow_sum]
  simp only [hpr]
  refine key.trans ?_
  -- numerics
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hX1 : (1 : ℝ) ≤ X := by
    have : (1 : ℝ) ≤ B ^ 80 := one_le_pow₀ hB
    rw [hX]; nlinarith [show (1 : ℝ) ≤ (2 : ℝ) ^ 31 * 3 ^ 48 by norm_num]
  have hC1 : (1 : ℝ) ≤ C₀ := le_trans (by norm_num) (le_max_left _ _)
  have hnat := layervine_nat_le m 𝔇 g
  have hcast : (((𝔇 + 1) ^ (25 + 2 * 3) * 3 ^ (2 * (m + 2) + 16 * 3 * 𝔇 * (g + 1)) : ℕ) : ℝ) ≤
      81 * 9 ^ m * ((2 : ℝ) ^ 31 * 3 ^ 48) ^ (𝔇 * (g + 1)) := by exact_mod_cast hnat
  have hBp : B ^ (10 * 𝔇 * 3 * (g + 1) + 2 * 𝔇 * 25) ≤ (B ^ 80) ^ (𝔇 * (g + 1)) := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ hB
    nlinarith
  have h9 : (9 : ℝ) ^ m ≤ C₀ ^ m := pow_le_pow_left₀ (by norm_num) (le_trans (by norm_num) (le_max_left _ _)) m
  have h81 : (81 : ℝ) ≤ C₀ ^ (g + 1) := (le_max_left _ _).trans (le_self_pow₀ hC1 (by omega))
  have hXp : X ^ (𝔇 * (g + 1)) ≤ (C₀ ^ 𝔇) ^ (g + 1) := by
    rw [← pow_mul]; exact pow_le_pow_left₀ (by linarith) (le_max_right _ _) _
  have hC₂' : (C₀ ^ (𝔇 + 1)) ^ (g + 1) ≤ C₂ ^ (g + 1) :=
    pow_le_pow_left₀ (by positivity) hC₂ _
  calc (((𝔇 + 1) ^ (25 + 2 * 3) * 3 ^ (2 * (m + 2) + 16 * 3 * 𝔇 * (g + 1)) : ℕ) : ℝ) *
        B ^ (10 * 𝔇 * 3 * (g + 1) + 2 * 𝔇 * 25)
      ≤ (81 * 9 ^ m * ((2 : ℝ) ^ 31 * 3 ^ 48) ^ (𝔇 * (g + 1))) * (B ^ 80) ^ (𝔇 * (g + 1)) :=
        mul_le_mul hcast hBp (by positivity) (by positivity)
    _ = 81 * 9 ^ m * X ^ (𝔇 * (g + 1)) := by rw [hX, mul_pow ((2 : ℝ) ^ 31 * 3 ^ 48)]; ring
    _ ≤ C₀ ^ (g + 1) * C₀ ^ m * (C₀ ^ 𝔇) ^ (g + 1) := by
        apply mul_le_mul (mul_le_mul h81 h9 (by positivity) (by positivity)) hXp (by positivity) (by positivity)
    _ = C₀ ^ m * (C₀ ^ (𝔇 + 1)) ^ (g + 1) := by rw [pow_succ C₀ 𝔇, mul_pow]; ring
    _ ≤ C₀ ^ m * C₂ ^ (g + 1) := mul_le_mul_of_nonneg_left hC₂' (by positivity)

end WaveTurbulence.GammaLow.Famc
