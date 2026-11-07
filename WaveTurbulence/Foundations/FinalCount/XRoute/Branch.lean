/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.C4NonExc
public import WaveTurbulence.Foundations.FinalCount.XRoute.TheoremAX
import Mathlib.Tactic

/-! # G8-XROUTE: the small-cell branch of case (4) (R26)

`case4SmallCell_proved` proves G8's named input `Case4SmallCell` (module `C4NonExc`, sha256 in COPIED-SHA256SUMS).
The proof is the T-branch of `case_four_of_nonexc` with `theorem_A_X` / `theorem_A_X_one` in place of
`theorem_A` / `theorem_A_one`: the route to `X` comes from `smallCell_route` when `YReachesSmallCell` holds, and from
`small_final` (route length `0`) when the closure has at most four atoms.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp WaveTurbulence.MoleProp4

theorem case4SmallCell_proved (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hsm : (d : ℝ) * η ≤ min γ (1 - γ) / 1000) (hηs : 4 * 1440061 * η ≤ 1) :
    Case4SmallCell.{u, v} d γ η := by
  classical
  have hγ01 : γ ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hγ.1], hγ.2⟩
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hpos : 0 < min γ (1 - γ) := lt_min (by linarith [hγ.1]) (by linarith [hγ.2])
  have hηmax : η ≤ min γ (1 - γ) / 2 := by nlinarith
  constructor
  · obtain ⟨CA, hCA, hthA⟩ := theorem_A_X.{u, v} d hd γ hγ η hη hηmax hηs (opCInput.{u, v} d γ η hγ01)
      (opDInput.{u, v} d γ η hη)
    refine ⟨CA, hCA, fun m C1 hC1 δ hδ => ?_⟩
    obtain ⟨RA, hRA⟩ := hthA C1 hC1 δ hδ
    refine ⟨max RA 1, le_max_right _ _, fun L hL => ?_⟩
    have hLRA : RA ≤ L := (le_max_left _ _).trans hL
    have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
    have hLp : 0 < L := by linarith
    intro V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' y₁ y₂ y₃ y₄ D4 hnq hsc
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
    have hne : (closureTwo M b b' y₁ y₂ y₃ y₄).atoms.Nonempty :=
      ⟨M.atom (M.mate y₁), by rw [hAt]; exact hm y₁ (by simp)⟩
    obtain ⟨k, hk, hroute⟩ : ∃ k ≤ 2, YRouteX k (closureTwo M b b' y₁ y₂ y₃ y₄) := by
      rcases hsc with hsc | hsc
      · exact smallCell_route hsc 2 hreg htrip
      · exact ⟨0, by norm_num, YRouteX.done _ (small_final hreg hne hsc hnq)⟩
    have hcard1 : (crossDarts M {b}).card = 2 := by rw [D4.hc1, card_pair hy12]
    have heven := shape_even hS hnodd
    have hconnb := connected_erase_of_two_cross M hS.conn heven {b} hcard1
    have hM : M.IsMolecule := hS.isMolecule
    have hKA : ({b} : Finset V) ⊆ M.atoms := by simpa using D4.hb
    let Ta : TwoExit M := ⟨{b}, hKA, y₂, y₁, by rw [D4.hc1]; exact pair_comm _ _, hy12.symm, D4.hfar1.symm,
      D4.ho2, D4.ho1⟩
    have p₃ : M.atom y₃ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₃) ∉ ({b} : Finset V) :=
      ⟨by rw [hat3]; simpa using D4.hbb'.symm, by simpa using (hyd y₃ (by simp)).1⟩
    have p₄ : M.atom y₄ ∉ ({b} : Finset V) ∧ M.atom (M.mate y₄) ∉ ({b} : Finset V) :=
      ⟨by rw [hat4]; simpa using D4.hbb'.symm, by simpa using (hyd y₄ (by simp)).1⟩
    obtain ⟨hcK, hdir⟩ := chain_after_erase hS.noLoop D4.hc2 p₃ p₄
    have hbN : b' ∈ (Degen.eraseAtoms M {b}).atoms := mem_sdiff.mpr ⟨D4.hb', by simpa using D4.hbb'.symm⟩
    have hneN : (⟨y₄, p₄⟩ : Degen.RetainedDart M {b}) ≠ ⟨y₃, p₃⟩ := fun h => hy34 (congrArg Subtype.val h).symm
    have hKb : ({b'} : Finset V) ⊆ (Degen.eraseAtoms M {b}).atoms := by simpa using hbN
    let Tb : TwoExit (Degen.eraseAtoms M {b}) :=
      ⟨{b'}, hKb, ⟨y₄, p₄⟩, ⟨y₃, p₃⟩, by rw [hcK]; exact pair_comm _ _, hneN, D4.hfar2.symm, D4.ho4, D4.ho3⟩
    have hdb := hS.dir2 b D4.hb D4.hdeg2
    have hdb' := hS.dir2 b' D4.hb' D4.hdeg2'
    have hdbN : (Degen.eraseAtoms M {b}).outdeg b' = 1 ∧ (Degen.eraseAtoms M {b}).indeg b' = 1 := by
      unfold Molecule.outdeg Molecule.indeg; rw [hdir true, hdir false]; exact hdb'
    have hcapN := caps_eraseAtoms {b} hS.caps
    have hconnP : ∀ u ∈ Tb.post.atoms, ∀ w ∈ Tb.post.atoms, Tb.post.SameComponent u w := Tb.post_connected hconnb
    have hcapP := Tb.post_caps hcapN
    have hdegN : ∀ v ∈ Tb.Y, (Degen.eraseAtoms M {b}).deg v = 2 := by
      intro v hv
      have hv' : v = b' := mem_singleton.mp hv
      rw [hv']
      have := Mole.outdeg_add_indeg (Degen.eraseAtoms M {b}) b'; omega
    have hbA : (Degen.eraseAtoms M {b}).bonds.card + ({b} : Finset V).card + 1 = M.bonds.card :=
      erase_chain_bonds M Ta (fun v hv => by rw [mem_singleton.mp hv]; exact D4.hdeg2)
    have hbB : (Degen.eraseAtoms (Degen.eraseAtoms M {b}) {b'}).bonds.card + ({b'} : Finset V).card + 1 =
        (Degen.eraseAtoms M {b}).bonds.card := erase_chain_bonds (Degen.eraseAtoms M {b}) Tb hdegN
    have hpb : Tb.post.bonds.card = (Degen.eraseAtoms (Degen.eraseAtoms M {b}) {b'}).bonds.card + 1 :=
      Tb.post_bonds_eq
    have hMb := c5_two_bonds D4.hb D4.hb' D4.hbb' D4.hdeg2 D4.hdeg2' D4.hdeg4
    have hpatoms : Tb.post.atoms.card + 2 = M.atoms.card := by
      rw [Tb.post_atoms, card_sdiff_of_subset Tb.sub]
      have h1 : (Degen.eraseAtoms M {b}).atoms.card + 1 = M.atoms.card := by
        change (M.atoms \ {b}).card + 1 = _
        rw [card_sdiff_of_subset hKA]; have := card_pos.mpr ⟨b, D4.hb⟩; simp; omega
      have h2 : ({b'} : Finset V).card = 1 := card_singleton _
      show (Degen.eraseAtoms M {b}).atoms.card - ({b'} : Finset V).card + 2 = _
      omega
    have hEp : (Tb.post.bonds.card : ℤ) = 2 * Tb.post.atoms.card - 1 := by
      rw [card_singleton] at hbA hbB; omega
    obtain ⟨z, hz, hz4, hz3⟩ := exists_deg_ne_four Tb.post hcapP hEp
    have hgood : ∀ S ∈ MoleProp.ladderCells Tb.post, GoodCell Tb.post S :=
      fun S hS' => goodCell_of_connected_low hconnP hz hz3 hS'
    set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
    refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
    have hmain := hRA L hLRA M hS.caps hS.noLoop b b' y₁ y₂ y₃ y₄ D4.hb D4.hb' D4.hbb' hdb hdb' D4.hc1 D4.ho1
      D4.ho2 D4.hc2 D4.ho3 D4.ho4 D4.hfar1 D4.hfar2 (hyd y₁ (by simp)).2 (hyd y₂ (by simp)).2
      (hyd y₃ (by simp)).1 (hyd y₄ (by simp)).1 hS.conn hconnb hconnP hgood k hk hroute hreg.cap hreg.loop hreg.reg
      hreg.conn P' (fun S _ => hP _) (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)
      (fun κ hκ => ⟨⟨fun p q hpq hpB hpo => ?_, hκ.2⟩, ne_of_gapAt_ne (hF.betaGap κ hκ.1 b D4.hb D4.hbeta y₁ y₂ hat1 hat2 hy12)⟩)
    · exact hmain
    · have hpA : M.atom p ∈ M.atoms := M.atom_mem p
      have hε : (cls (M.atom p)).IsEps := D4.heps _ hpA (fun h => hpB (by simp [h])) (fun h => hpB (by simp [h]))
      exact (hF.epsLG κ hκ.1 _ hpA hε p q rfl hpq.symm hpo).le
  · obtain ⟨CA1, hCA1, hthA1⟩ := theorem_A_X_one.{u, v} d hd γ hγ η hη hηmax hηs (opCInput.{u, v} d γ η hγ01)
    refine ⟨CA1, hCA1, fun m C1 hC1 δ hδ => ?_⟩
    obtain ⟨RA1, hRA1⟩ := hthA1 C1 hC1 δ hδ
    refine ⟨max RA1 1, le_max_right _ _, fun L hL => ?_⟩
    have hLRA1 : RA1 ≤ L := (le_max_left _ _).trans hL
    have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
    have hLp : 0 < L := by linarith
    intro V D _ _ _ M cls odd Adm P hS hF hsz hP hMA hfr hnodd hnc hcase b b' x₁ x₂ y y' D1 hnq hsc
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
    have hne : (closureOne M b b' x₁ x₂).atoms.Nonempty :=
      ⟨M.atom (M.mate x₁), by rw [hAt]; exact mem_sdiff.mpr ⟨M.atom_mem _, hx1⟩⟩
    obtain ⟨k, hk, hroute⟩ : ∃ k ≤ 2, YRouteX k (closureOne M b b' x₁ x₂) := by
      rcases hsc with hsc | hsc
      · exact smallCell_route hsc 2 hreg htrip
      · exact ⟨0, by norm_num, YRouteX.done _ (small_final hreg hne hsc hnq)⟩
    set P' : Finset V → ℝ := fun S => P (Mole.appbLinkParent M S) with hP'
    refine (countA_le_countAFree_cell M hM L γ δ C1 (0 : Mom d) Adm P (GapScale L) hMA).trans ?_
    have hdb := hS.dir2 b D1.hb D1.hdeg2
    have hdb' := hS.dir2 b' D1.hb' D1.hdeg2'
    have hmain := hRA1 L hLRA1 M hS.caps hS.noLoop b b' x₁ x₂ y y' D1.hb D1.hb' hdb hdb' D1.hc D1.hfar D1.hyb
      D1.hyb' D1.hyy' hS.conn (chain_piece_connected D1.hK) hconnE k hk hroute hreg.cap hreg.loop hreg.reg hreg.conn
      P' (fun S _ => hP _) (fun κ => Adm κ ∧ CellGapRestriction M L (0 : Mom d) P' (GapScale L) κ)
      (fun κ hκ => ⟨⟨fun p q hpq hpB hpo => ?_, hκ.2⟩,
        ne_of_gapAt_ne (hF.betaGap κ hκ.1 b D1.hb D1.hbeta y y' D1.hyb D1.hyb' D1.hyy')⟩)
    · exact hmain
    · have hpA : M.atom p ∈ M.atoms := M.atom_mem p
      have hε : (cls (M.atom p)).IsEps := D1.heps _ hpA (fun h => hpB (by simp [h])) (fun h => hpB (by simp [h]))
      exact (hF.epsLG κ hκ.1 _ hpA hε p q rfl hpq.symm hpo).le

end WaveTurbulence.FinalCountG8
