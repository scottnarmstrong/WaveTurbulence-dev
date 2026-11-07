/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4Main
public import WaveTurbulence.Foundations.FinalCount.Split1Thm
import Mathlib.Tactic

/-! # Case (4), the non-exceptional branch, outside the small-cell configurations (finalcount-g8, F6-1)

`Case4SmallCell` is the one input of Prop 9.6 that remains: the closure `𝕄₁` of a case-(4) component is not
`Y`-exceptional, and either some complete `(Y2)`-route of `𝕄₁` reaches a post molecule with at most four atoms and a ladder
cell (`YReachesSmallCell`), or `𝕄₁` itself has at most four atoms.  This is the only place where the hypotheses
`¬ YReachesSmallCell`, `5 ≤ |𝕄₁|` of `prop104_two_proved` (resp. of the good-cell condition of the last
operation (d)) are not available (findings F6-1 / F6-2).  `case4_nonexc_of_smallcell` proves `Case4NonExc` from it with
`case4_two_split` / `case4_one_split`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4

/-- **The small-cell sub-branch of case (4)** (NAMED input; finding F6-2).  Same data as `Case4NonExc`, with the
additional hypothesis that `𝕄₁` reaches a small cell or has at most four atoms; same conclusion `𝔄₀ ≤ L^{-η/128}`. -/
structure Case4SmallCell (d : ℕ) (γ η : ℝ) : Prop where
  two : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → (∃ v₂ : V, v₂ ∉ M.atoms) → ¬ odd →
      (¬ ∀ a ∈ M.atoms, M.deg a = 2) → ((alphaAtoms M.atoms cls).card = 0 ∧ (betaAtoms M.atoms cls).card = 2) →
      ∀ (b b' : V) (y₁ y₂ y₃ y₄ : D), Case4TwoData M cls b b' y₁ y₂ y₃ y₄ →
        ¬ YReachesQT (closureTwo M b b' y₁ y₂ y₃ y₄) →
        (YReachesSmallCell (closureTwo M b b' y₁ y₂ y₃ y₄) ∨ (closureTwo M b b' y₁ y₂ y₃ y₄).atoms.card ≤ 4) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128)))
  one : ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)
      (cls : V → Cls) (odd : Prop) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      FinalShape M cls odd → FinalDec M cls L γ η Adm → (M.atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
      (∀ S, 0 ≤ P S) → MaxLadderGapAdm M L (0 : Mom d) P (GapScale L) Adm → (∃ v₂ : V, v₂ ∉ M.atoms) → ¬ odd →
      (¬ ∀ a ∈ M.atoms, M.deg a = 2) → ((alphaAtoms M.atoms cls).card = 0 ∧ (betaAtoms M.atoms cls).card = 2) →
      ∀ (b b' : V) (x₁ x₂ y y' : D), Case4OneData M cls b b' x₁ x₂ y y' →
        ¬ YReachesQT (closureOne M b b' x₁ x₂) →
        (YReachesSmallCell (closureOne M b b' x₁ x₂) ∨ (closureOne M b b' x₁ x₂).atoms.card ≤ 4) →
        M.countA L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128)))

section
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem card_closure_le (M : Molecule V D) (b b' : V) (y₁ y₂ y₃ y₄ : D)
    (h1 : M.atom (M.mate y₁) ∈ (M.atoms \ {b}) \ {b'}) (h2 : M.atom (M.mate y₂) ∈ (M.atoms \ {b}) \ {b'})
    (h3 : M.atom (M.mate y₃) ∈ (M.atoms \ {b}) \ {b'}) (h4 : M.atom (M.mate y₄) ∈ (M.atoms \ {b}) \ {b'}) :
    (closureTwo M b b' y₁ y₂ y₃ y₄).atoms.card ≤ M.atoms.card := by
  rw [atoms_closureTwo M b b' y₁ y₂ y₃ y₄ h1 h2 h3 h4]
  exact card_le_card (sdiff_subset.trans sdiff_subset)

end

/-- **`Case4NonExc` from `Case4SmallCell`**: outside the small-cell configurations the decoration-level split
(`case4_two_split`, `case4_one_split`) proves the non-exceptional bound. -/
theorem case4_nonexc_of_smallcell (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1)
    (hSC : Case4SmallCell.{u, v} d γ η) : Case4NonExc.{u, v} d γ η := by
  classical
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < min γ (1 - γ) := lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
  have hη200 : η ≤ min γ (1 - γ) / 200 := by nlinarith
  have hηd : (d : ℝ) * η ≤ min γ (1 - γ) / 4 := by linarith
  obtain ⟨CSC2, hCSC2, hSC2⟩ := hSC.two
  obtain ⟨CSC1, hCSC1, hSC1⟩ := hSC.one
  obtain ⟨CS2, hCS2, hSp2⟩ := case4_two_split.{u, v} d hd γ hγ η hη hη200 hηd hηs
  obtain ⟨CS1, hCS1, hSp1⟩ := case4_one_split.{u, v} d hd γ hγ η hη hη200 hηd hηs
  constructor
  · refine ⟨max CSC2 CS2, hCSC2.trans (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
    obtain ⟨R0, hR01, hR0⟩ := hSC2 m C1 ((le_max_left _ _).trans hC1) δ hδ
    obtain ⟨R1, hR1⟩ := hSp2 m C1 ((le_max_right _ _).trans hC1) δ hδ
    refine ⟨max R0 R1, hR01.trans (le_max_left _ _), fun L hL => ?_⟩
    have hL0 : R0 ≤ L := (le_max_left _ _).trans hL
    have hLR1 : R1 ≤ L := (le_max_right _ _).trans hL
    have hL1 : 1 ≤ L := hR01.trans hL0
    intro V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' y₁ y₂ y₃ y₄ D4 hnq
    by_cases hsc : YReachesSmallCell (closureTwo M b b' y₁ y₂ y₃ y₄) ∨
        (closureTwo M b b' y₁ y₂ y₃ y₄).atoms.card ≤ 4
    · exact hR0 L hL0 M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' y₁ y₂ y₃ y₄ D4 hnq hsc
    push Not at hsc
    obtain ⟨hns, h5⟩ := hsc
    have hLp : 0 < L := by linarith
    by_cases hAex : ∃ κ, Adm κ
    swap
    · push Not at hAex
      rw [countA_zero_of_noAdm M L γ δ C1 Adm P hAex]; exact bot_le
    obtain ⟨κ0, hκ0⟩ := hAex
    have hM : M.IsMolecule := hS.isMolecule
    have hy12 : y₁ ≠ y₂ := fun h => D4.hfar1 (by rw [h])
    have hy34 : y₃ ≠ y₄ := fun h => D4.hfar2 (by rw [h])
    have hyd : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ≠ b ∧ M.atom (M.mate y) ≠ b' := fun y hy =>
      ⟨fun h => D4.hnb (h ▸ D4.hendsE y hy), fun h => D4.hnb' (h ▸ D4.hendsE y hy)⟩
    have hat : ∀ {K : Finset V} {p q : D}, crossDarts M K = {p, q} → M.atom p ∈ K ∧ M.atom q ∈ K := by
      intro K p q h
      exact ⟨(mem_crossDarts.mp (by rw [h]; simp)).1, (mem_crossDarts.mp (by rw [h]; simp)).1⟩
    have hat1 : M.atom y₁ = b := mem_singleton.mp (hat D4.hc1).1
    have hat2 : M.atom y₂ = b := mem_singleton.mp (hat D4.hc1).2
    have hat3 : M.atom y₃ = b' := mem_singleton.mp (hat D4.hc2).1
    have hat4 : M.atom y₄ = b' := mem_singleton.mp (hat D4.hc2).2
    have hall1 : ∀ x, M.atom x = b → x = y₁ ∨ x = y₂ := by
      intro x hx
      have : x ∈ crossDarts M {b} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
        fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
      rw [D4.hc1] at this; simpa using this
    have hall2 : ∀ x, M.atom x = b' → x = y₃ ∨ x = y₄ := by
      intro x hx
      have : x ∈ crossDarts M {b'} := mem_crossDarts.mpr ⟨by rw [hx]; exact mem_singleton_self _,
        fun h => hS.noLoop x (hx.trans (mem_singleton.mp h).symm)⟩
      rw [D4.hc2] at this; simpa using this
    have hends : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ∈ M.atoms ∧ M.atom (M.mate y) ≠ b ∧
        M.atom (M.mate y) ≠ b' := fun y hy => ⟨M.atom_mem _, (hyd y hy).1, (hyd y hy).2⟩
    have hreg := regcore_closureTwo M hS.caps hS.noLoop hS.conn (nocut_M0 hS hF hLp hnodd hκ0 hfr) D4.hdeg4 D4.hbb'
      hat1 hat2 hat3 hat4 hy12 hy34 hall1 hall2 D4.ho1 D4.ho2 D4.ho3 D4.ho4 hends D4.hfar1 D4.hfar2
    have hm : ∀ y ∈ ({y₁, y₂, y₃, y₄} : Finset D), M.atom (M.mate y) ∈ (M.atoms \ {b}) \ {b'} := fun y hy =>
      mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨M.atom_mem _, by simpa using (hyd y hy).1⟩, by simpa using (hyd y hy).2⟩
    have hAt := atoms_closureTwo M b b' y₁ y₂ y₃ y₄ (hm y₁ (by simp)) (hm y₂ (by simp)) (hm y₃ (by simp))
      (hm y₄ (by simp))
    have htrip := trip_closureTwo M b b' y₁ y₂ y₃ y₄ hS.noTriple hAt
    have hszcl : ((closureTwo M b b' y₁ y₂ y₃ y₄).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
      (Nat.cast_le.mpr (card_closure_le M b b' y₁ y₂ y₃ y₄ (hm y₁ (by simp)) (hm y₂ (by simp)) (hm y₃ (by simp))
        (hm y₄ (by simp)))).trans hsz
    have heven := shape_even hS hnodd
    have hdb := hS.dir2 b D4.hb D4.hdeg2
    have hdb' := hS.dir2 b' D4.hb' D4.hdeg2'
    set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
    refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
    refine hR1 L hLR1 M hS.caps hS.noLoop heven hS.conn b b' y₁ y₂ y₃ y₄ D4.hb D4.hb' D4.hbb' hdb hdb' D4.hc1 D4.ho1
      D4.ho2 D4.hc2 D4.ho3 D4.ho4 D4.hfar1 D4.hfar2 (hyd y₁ (by simp)).2 (hyd y₂ (by simp)).2
      (hyd y₃ (by simp)).1 (hyd y₄ (by simp)).1 hreg htrip hszcl h5 hnq hns P' (fun S _ => hP _)
      (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)
      (fun κ hκ => ⟨⟨fun p q hpq hpB hpo => ?_, hκ.2⟩,
        ne_of_gapAt_ne (hF.betaGap κ hκ.1 b D4.hb D4.hbeta y₁ y₂ hat1 hat2 hy12),
        ne_of_gapAt_ne (hF.betaGap κ hκ.1 b' D4.hb' D4.hbeta' y₃ y₄ hat3 hat4 hy34)⟩)
    have hpA : M.atom p ∈ M.atoms := M.atom_mem p
    have hε : (cls (M.atom p)).IsEps := D4.heps _ hpA (fun h => hpB (by simp [h])) (fun h => hpB (by simp [h]))
    exact (hF.epsLG κ hκ.1 _ hpA hε p q rfl hpq.symm hpo).le
  · refine ⟨max CSC1 CS1, hCSC1.trans (le_max_left _ _), fun m C1 hC1 δ hδ => ?_⟩
    obtain ⟨R0, hR01, hR0⟩ := hSC1 m C1 ((le_max_left _ _).trans hC1) δ hδ
    obtain ⟨R1, hR1⟩ := hSp1 m C1 ((le_max_right _ _).trans hC1) δ hδ
    refine ⟨max R0 R1, hR01.trans (le_max_left _ _), fun L hL => ?_⟩
    have hL0 : R0 ≤ L := (le_max_left _ _).trans hL
    have hLR1 : R1 ≤ L := (le_max_right _ _).trans hL
    have hL1 : 1 ≤ L := hR01.trans hL0
    intro V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' x₁ x₂ y y' D1 hnq
    by_cases hsc : YReachesSmallCell (closureOne M b b' x₁ x₂) ∨ (closureOne M b b' x₁ x₂).atoms.card ≤ 4
    · exact hR0 L hL0 M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' x₁ x₂ y y' D1 hnq hsc
    push Not at hsc
    obtain ⟨hns, h5⟩ := hsc
    have hLp : 0 < L := by linarith
    by_cases hAex : ∃ κ, Adm κ
    swap
    · push Not at hAex
      rw [countA_zero_of_noAdm M L γ δ C1 Adm P hAex]; exact bot_le
    obtain ⟨κ0, hκ0⟩ := hAex
    have hM : M.IsMolecule := hS.isMolecule
    have hcard : (crossDarts M {b, b'}).card = 2 := by rw [D1.hc, card_pair D1.hne]
    have heven := shape_even hS hnodd
    have hconnE := connected_erase_of_two_cross M hS.conn heven {b, b'} hcard
    have hnocut := nocut_M0 hS hF hLp hnodd hκ0 hfr
    have hreg := regcore_closureOne hS.caps hS.noLoop hS.conn hnocut D1.hb D1.hb' D1.hdeg4 D1.hc D1.hne D1.ho1 D1.ho2
      D1.hfar
    have hend : ∀ w, (cls w).IsEps → w ∉ ({b, b'} : Finset V) := by
      intro w hw hwB
      rcases mem_insert.mp hwB with h | h
      · exact D1.hnb (h ▸ hw)
      · exact D1.hnb' ((mem_singleton.mp h) ▸ hw)
    have hx1 : M.atom (M.mate x₁) ∉ ({b, b'} : Finset V) := hend _ D1.hendsE.1
    have hx2 : M.atom (M.mate x₂) ∉ ({b, b'} : Finset V) := hend _ D1.hendsE.2
    have hAt : (closureOne M b b' x₁ x₂).atoms = M.atoms \ {b, b'} := by
      change insert (M.atom (M.mate x₁)) (insert (M.atom (M.mate x₂)) (M.atoms \ {b, b'})) = _
      rw [insert_eq_of_mem (mem_sdiff.mpr ⟨M.atom_mem _, hx2⟩), insert_eq_of_mem (mem_sdiff.mpr ⟨M.atom_mem _, hx1⟩)]
    have htrip := trip_closureOne M b b' x₁ x₂ hS.noTriple hAt
    have hszcl : ((closureOne M b b' x₁ x₂).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m :=
      (Nat.cast_le.mpr (by rw [hAt]; exact card_le_card sdiff_subset)).trans hsz
    have hdb := hS.dir2 b D1.hb D1.hdeg2
    have hdb' := hS.dir2 b' D1.hb' D1.hdeg2'
    set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
    refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
    refine hR1 L hLR1 M hS.caps hS.noLoop b b' x₁ x₂ y y' D1.hb D1.hb' hdb hdb' D1.hc D1.ho1 D1.ho2 D1.hfar D1.hyb
      D1.hyb' D1.hyy' hS.conn (chain_piece_connected D1.hK) hconnE hreg htrip hszcl h5 hnq hns P' (fun S _ => hP _)
      (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)
      (fun κ hκ => ⟨⟨fun p q hpq hpB hpo => ?_, hκ.2⟩,
        ne_of_gapAt_ne (hF.betaGap κ hκ.1 b D1.hb D1.hbeta y y' D1.hyb D1.hyb' D1.hyy')⟩)
    have hpA : M.atom p ∈ M.atoms := M.atom_mem p
    have hε : (cls (M.atom p)).IsEps := D1.heps _ hpA (fun h => hpB (by simp [h])) (fun h => hpB (by simp [h]))
    exact (hF.epsLG κ hκ.1 _ hpA hε p q rfl hpq.symm hpo).le

end WaveTurbulence.FinalCountG8
