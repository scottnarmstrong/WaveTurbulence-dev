/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Split1Thm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Count.Prop104Low
import Mathlib.Tactic

/-! # Case (4)′, the non-exceptional branch, at every `γ ∈ (0, 1)`: the decoration-level split (M2 §4.8 (B))

Ports of main's `opCFree` (`OpCFree.lean`), `class2_bound` (`Split2Class2.lean`), `split_arith` (`Split2Arith.lean`),
`case4_two_split` (`Split2Thm.lean`) and `case4_one_split` (`Split1Thm.lean`) to every `γ ∈ (0, 1)`:
* operation (c) in its SHARP form `L^{min(γ, 1−γ)}` (main's proof already derives it and then weakens it to `L^{1−γ}`,
  which is too weak at `γ < 1/2`: erratum F-M2-1; M2 §4.8 class 2 uses "Lemma 4.1 sharp (≤ δ⁻¹L^{γ₀}, whatever the β-gap)");
* Prop 10.4(2)′ from L6-COUNT (`Count.prop104_two_proved_low`, all `γ ∈ (0, 1)`);
* the exponent bookkeeping `L^{γ₀} · L^{−(γ₀ + ηs/16)} = L^{−ηs/16}` holds for every `γ` (`split_arith_sharp`).
Everything else is main's verbatim. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
open Finset
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount
universe u v
open WaveTurbulence.FinalCountG8 WaveTurbulence.MoleProp4

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

open Set in
theorem opCFree_sharp {d : ℕ} {L γ δ C1 : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : δ ∈ Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1) (M : Molecule V D)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2)
    (hMconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (Y : Finset V) (x₁ x₂ : D) (hYM : Y ⊆ M.atoms) (hch : ∀ b ∈ Y, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hcross : crossDarts M Y = {x₁, x₂}) (hne : M.atom (M.mate x₁) ≠ M.atom (M.mate x₂))
    (hYconn : ∀ a ∈ Y, ∀ b ∈ Y, (piece M Y).SameComponent a b)
    (hpost : ∀ a ∈ (Degen.eraseAtoms M Y).atoms, ∀ b ∈ (Degen.eraseAtoms M Y).atoms,
      (Degen.eraseAtoms M Y).SameComponent a b)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S)
    (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → ∃ y y', M.atom y ∈ Y ∧ M.atom y' = M.atom y ∧ y ≠ y' ∧ κ y ≠ κ y') :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ)) *
        MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d) (MoleProp.erasedFreeAdmissibility M Y Adm) P := by
  classical
  have hLp : 0 < L := by linarith
  have hδ0 : 0 < δ := hδ.1
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have h0 : MoleProp.countEFree M L γ δ (0 : Mom 0) Adm = 0 :=
      countEFree_eq_zero M L γ δ 0 Adm fun κ _ hκ => by
        obtain ⟨y, y', _, _, _, h⟩ := hAdm κ hκ
        exact h (Subsingleton.elim _ _)
    rw [MoleProp.countAFree_eq_normalization, h0]
    simp
  have hx : x₁ ≠ x₂ := fun h => hne (by rw [h])
  have hY1 : 1 ≤ Y.card := by
    have : x₁ ∈ crossDarts M Y := by rw [hcross]; simp
    exact card_pos.mpr ⟨M.atom x₁, (mem_crossDarts.mp this).1⟩
  let T : Exits2 M := ⟨Y, hYM, x₁, x₂, hcross, hx⟩
  obtain ⟨n, hn, hcount⟩ := countEFree_le_chain M hYM hch hYconn hd hL hδ.1 (γ := γ) Adm hAdm
  have hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => by
    have := hcap a ha; have := Mole.outdeg_add_indeg M a; omega
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms M Y), 0 ≤ P S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff M Y S').mp (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M this.1), this.1⟩)
  have hPpiece : ∀ S' ∈ MoleProp.ladderCells (piece M Y), 0 ≤ P S' := fun S' hS' => by
    have := (mem_filter.mp hS').2
    exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M
      ((isLadderCell_piece_iff S').mp this).1), ((isLadderCell_piece_iff S').mp this).1⟩)
  -- ranks
  have hF1 : M.numComponents = 1 := Mole.numComponents_eq_one M ⟨M.atom x₁, M.atom_mem x₁⟩ hMconn
  have hFp : (piece M Y).numComponents = 1 := Mole.numComponents_eq_one (piece M Y)
    (by rw [piece_atoms hYM]; exact ⟨M.atom x₁, T.atom_x⟩) (by rw [piece_atoms hYM]; exact hYconn)
  have hFe : (Degen.eraseAtoms M Y).numComponents = 1 :=
    Mole.numComponents_eq_one (Degen.eraseAtoms M Y) ⟨M.atom (M.mate x₁), mem_sdiff.mpr
      ⟨M.atom_mem _, (mem_crossDarts.mp T.x_mem).2⟩⟩ hpost
  have hrk := T.circuitRank_eq4 hF1 hFp hFe
  have hrkp : (piece M Y).circuitRank = 0 := by
    unfold Molecule.circuitRank
    rw [chain_piece_card M hYM hch hY1 hcross hx, piece_atoms hYM, hFp]
    push_cast; ring
  rw [hrkp, zero_add] at hrk
  -- cells
  have hcellsP : MoleProp.ladderCells (piece M Y) = ∅ := by
    rw [T.ladderCells_piece_eq']
    refine eq_empty_of_forall_notMem fun S hS => ?_
    obtain ⟨hS1, hS2⟩ := mem_filter.mp hS
    have hS3 := (mem_filter.mp hS1).2
    refine no_cell_of_deg_le_two M hS3 fun a ha => ?_
    have := Mole.outdeg_add_indeg M a; have := hch a (hS2 ha); omega
  have hcp := T.cellProduct_le4 hloop hdeg (L := L) (γ := γ) (δ := δ) hLp.le hδ.1.le hlog P hP
  have hcpP : MoleProp.cellProduct (piece M Y) L γ δ P = 1 := by
    unfold MoleProp.cellProduct; rw [hcellsP]; simp
  have hcp' : MoleProp.cellProduct M L γ δ P ≤
      MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P * (Real.log L ^ 2) ^ 4 := by
    have h := hcp
    change MoleProp.cellProduct M L γ δ P ≤ MoleProp.cellProduct (piece M Y) L γ δ P *
      MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P * (Real.log L ^ 2) ^ 4 at h
    rwa [hcpP, one_mul] at h
  have hbpos : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := by
    have : 0 < C1 := by linarith
    have := hδ.1; positivity
  have hb1 : C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 := by
    have hC : 0 < C1 := by linarith
    have h1 : C1⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC1
    have h2 : δ ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hδ.1.le hδ.2 (by norm_num)
    calc C1⁻¹ * δ ^ (1 / 2 : ℝ) ≤ 1 * 1 := mul_le_mul h1 h2 (by have := hδ.1; positivity) zero_le_one
      _ = 1 := one_mul 1
  have ne := MoleProp.freeNormalization_pos (Degen.eraseAtoms M Y) (d := d) (γ := γ) hLp hδ.1
    (by linarith : 0 < C1) hlog0 P hPerase
  have hcpE : 0 ≤ MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P :=
    (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPerase).le
  have hnorm : MoleProp.freeNormalization M (d := d) L γ δ C1 P ≤
      (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) *
        MoleProp.freeNormalization (Degen.eraseAtoms M Y) (d := d) L γ δ C1 P := by
    have := norm_split1 (a := (d : ℝ) - γ) (χP := 0) (χE := (Degen.eraseAtoms M Y).circuitRank) hLp hbpos
      (cP := 1) (cE := MoleProp.cellProduct (Degen.eraseAtoms M Y) L γ δ P) (cM := MoleProp.cellProduct M L γ δ P)
      (W := (Real.log L ^ 2) ^ 4) zero_le_one hcpE (by simpa using hcp')
    unfold MoleProp.freeNormalization
    rw [hrk]
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using this
  have hnreal := bibridge_n_bound (n := (n : ℝ)) (L := L) (δ := δ) (γ := γ) (d := d) (s := 1) hL hδ.1
    hγ.1 hγ.2 hd (Nat.cast_nonneg _) (by simpa using hn)
  have hdev : (n : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) ≤
      ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hW : (Real.log L ^ 2) ^ 4 = Real.log L ^ (8 : ℝ) := by
      rw [← pow_mul, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hW]
    have hWnn : 0 ≤ Real.log L ^ (8 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc (n : ℝ) * (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ)) =
          ((n : ℝ) * L ^ (-((d : ℝ) - γ))) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * Real.log L ^ (8 : ℝ) := by ring
      _ ≤ (3 ^ d * (d * δ⁻¹ + 1) * ((1 : ℕ) + 1) * L ^ min γ (1 - γ)) * 1 * Real.log L ^ (8 : ℝ) := by
          refine mul_le_mul (mul_le_mul hnreal hb1 hbpos.le (by positivity)) le_rfl hWnn (by positivity)
      _ ≤ 2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ) := by
          have hK : 0 ≤ (3 : ℝ) ^ d * (d * δ⁻¹ + 1) := by have := hδ.1; positivity
          calc _ = 2 * (3 ^ d * (d * δ⁻¹ + 1)) * L ^ min γ (1 - γ) * Real.log L ^ (8 : ℝ) := by push_cast; ring
            _ ≤ 2 * (3 ^ d * (d * δ⁻¹ + 1)) * L ^ min γ (1 - γ) * Real.log L ^ (8 : ℝ) := by gcongr
            _ = _ := by ring
  have hmain : MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ((n : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4)) *
        MoleProp.countAFree (Degen.eraseAtoms M Y) L γ δ C1 (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility M Y Adm) P := by
    rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization]
    calc _ ≤ (((n : ℕ∞) * MoleProp.countEFree (Degen.eraseAtoms M Y) L γ δ (0 : Mom d)
              (MoleProp.erasedFreeAdmissibility M Y Adm) : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) * (Real.log L ^ 2) ^ 4) *
            MoleProp.freeNormalization (Degen.eraseAtoms M Y) (d := d) L γ δ C1 P) :=
          mul_le_mul' (ENat.toENNReal_mono hcount)
            (ENNReal.ofReal_le_ofReal hnorm)
      _ = _ := by
          rw [ENNReal.ofReal_mul (by positivity), ENat.toENNReal_mul, ENat.toENNReal_coe]
          ring
  exact hmain.trans (mul_le_mul' hdev le_rfl)


theorem class2_bound_sharp {d : ℕ} {L γ δ η C1 ε₂ : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hη : 0 ≤ η)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (hL11a : 11 ≤ L ^ (η / 2)) (hL11b : 11 ≤ L ^ (η / 2 / 2))
    {M₀ : Molecule V D} (Ta : TwoExit M₀) (Tb : TwoExit Ta.post) (Bs : Finset V)
    (hcap : ∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) (hloop : ∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z))
    (hconn : ∀ a ∈ M₀.atoms, ∀ b ∈ M₀.atoms, M₀.SameComponent a b)
    (hY3a : Ta.Y.card ≤ 3) (hcha : ∀ b ∈ Ta.Y, M₀.outdeg b = 1 ∧ M₀.indeg b = 1)
    (hYconna : ∀ a ∈ Ta.Y, ∀ b ∈ Ta.Y, (piece M₀ Ta.Y).SameComponent a b)
    (hcBa : Ta.c ∉ Bs) (hdBa : Ta.d ∉ Bs)
    (hpostA : ∀ a ∈ Ta.post.atoms, ∀ b ∈ Ta.post.atoms, Ta.post.SameComponent a b)
    (hopenA : ∀ S ∈ MoleProp.ladderCells Ta.post, GoodCell Ta.post S)
    (hcap1 : ∀ a ∈ Ta.post.atoms, Ta.post.outdeg a ≤ 2 ∧ Ta.post.indeg a ≤ 2)
    (hloop1 : ∀ z, Ta.post.atom z ≠ Ta.post.atom (Ta.post.mate z))
    (hchb : ∀ b ∈ Tb.Y, Ta.post.outdeg b = 1 ∧ Ta.post.indeg b = 1)
    (hYconnb : ∀ a ∈ Tb.Y, ∀ b ∈ Tb.Y, (piece Ta.post Tb.Y).SameComponent a b)
    (hcBb : Tb.c ∉ Bs \ Ta.Y) (hdBb : Tb.d ∉ Bs \ Ta.Y)
    (hpostE : ∀ a ∈ (Degen.eraseAtoms Ta.post Tb.Y).atoms, ∀ b ∈ (Degen.eraseAtoms Ta.post Tb.Y).atoms,
      (Degen.eraseAtoms Ta.post Tb.Y).SameComponent a b)
    (hxy : Ta.post.atom Tb.y = Ta.post.atom Tb.x)
    (hBs : (Bs \ Ta.Y) \ Tb.Y = ∅)
    {Dcl : Type*} [Fintype Dcl] [DecidableEq Dcl] (cl : Molecule V Dcl)
    (Φ : Degen.RetainedDart Ta.post Tb.Y ⊕ Bool ≃ Dcl)
    (hA : Tb.post.atoms = cl.atoms) (ha : ∀ x, cl.atom (Φ x) = Tb.post.atom x)
    (hm : ∀ x, cl.mate (Φ x) = Φ (Tb.post.mate x)) (ho : ∀ x, cl.out (Φ x) = Tb.post.out x)
    (Q : (Dcl → (Fin d → ℤ)) → Prop)
    (hQ2 : ∀ P : Finset V → ℝ,
      (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond cl (Φ (Sum.inr true))), 0 ≤ P S) →
      MoleProp.countAFree (MoleProp.eraseBond cl (Φ (Sum.inr true))) L γ δ C1 (0 : Mom d)
        (fun κ => lgAdm (MoleProp.eraseBond cl (Φ (Sum.inr true))) L γ (η / 2 / 2) P κ ∧
          MoleProp.erasedBondAdmissibility cl (Φ (Sum.inr true))
            (fun κ0 => MoleProp.LargeGap cl L γ (η / 2 / 2) (0 : Mom d) κ0 ∧ Q κ0) κ) P ≤ ENNReal.ofReal ε₂)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S)
    (Adm : (D → (Fin d → ℤ)) → Prop) (hAdm : ∀ κ, Adm κ → lgAdmOff M₀ Bs L γ η P κ)
    (hgap : ∀ κ, Adm κ → ∀ g, Ta.postLabels κ g Tb.x ≠ Ta.postLabels κ g Tb.y) :
    MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧ ¬ Cls1 Ta Tb Φ Q Bs L γ η κ) P ≤
      ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) *
        (ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ)) * ENNReal.ofReal ε₂) := by
  classical
  have hY3a' := hY3a
  have hA1 := opDW hL hlog hδ hC1 M₀ Ta hcap hloop hconn Bs hY3a hcha hYconna hpostA hopenA P hP
    (fun κ => Adm κ ∧ ¬ Cls1 Ta Tb Φ Q Bs L γ η κ) (fun κ h => hAdm κ h.1)
    (fun g₁ κ => ∀ g₂ ∈ Icc (0 : ℤ) 4, Tb.PostGoodOff (Bs \ Ta.Y) L γ (η / 2 / 2) (Ta.postLabels κ g₁) g₂ →
      Q (MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂)))
    (by
      rintro κ ⟨hκ, hn⟩ hsym
      obtain ⟨g₁, hg₁, hpa⟩ := Ta.exists_postGoodOff hL hL11a hsym hcap Bs hcBa hdBa (hAdm κ hκ).1
      refine ⟨g₁, hg₁, hpa, fun g₂ hg₂ hpb => ?_⟩
      by_contra hq
      exact hn ⟨g₁, hg₁, g₂, hg₂, hpa, hpb, hq⟩)
  refine hA1.trans (mul_le_mul' le_rfl ?_)
  refine iSup₂_le fun g₁ hg₁ => ?_
  unfold TwoExit.afreeSupPost
  refine iSup₂_le fun P' hP' => ?_
  -- the dart isomorphism between the erased post and `𝕄₁ ∖ ℓ`
  have hmt : cl.mate (Φ (Sum.inr true)) = Φ (Sum.inr false) := by rw [hm]; rfl
  set e := Φ (Sum.inr true) with he
  let ι := withoutEquiv cl Φ hmt
  have hAe : (Degen.eraseAtoms Ta.post Tb.Y).atoms = (MoleProp.eraseBond cl e).atoms := by
    change Ta.post.atoms \ Tb.Y = cl.atoms
    rw [← Tb.post_atoms]; exact hA
  have hae : ∀ z, (MoleProp.eraseBond cl e).atom (ι z) = (Degen.eraseAtoms Ta.post Tb.Y).atom z :=
    fun z => ha (Sum.inl z)
  have hme : ∀ z, (MoleProp.eraseBond cl e).mate (ι z) = ι ((Degen.eraseAtoms Ta.post Tb.Y).mate z) :=
    fun z => Subtype.ext (hm (Sum.inl z))
  have hoe : ∀ z, (MoleProp.eraseBond cl e).out (ι z) = (Degen.eraseAtoms Ta.post Tb.Y).out z :=
    fun z => ho (Sum.inl z)
  have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms Ta.post Tb.Y), 0 ≤ P' S' := fun S' hS' => by
    have := (MoleProp.isLadderCell_erase_iff Ta.post Tb.Y S').mp (mem_filter.mp hS').2
    exact hP' S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms Ta.post this.1), this.1⟩)
  have hcellsE := MoleProp.ladderCells_eq_of_dart_equiv (Degen.eraseAtoms Ta.post Tb.Y) (MoleProp.eraseBond cl e)
    ι hAe hae hme hoe
  -- operation (c) on the second chain
  have hC := opCFree_sharp hγ hL hlog hδ hC1 Ta.post hloop1 hcap1 hpostA Tb.Y Tb.x Tb.y Tb.sub hchb Tb.cross Tb.far
    hYconnb hpostE P' hP'
    (Ta.postAdmOff Bs (fun κ => Adm κ ∧ ¬ Cls1 Ta Tb Φ Q Bs L γ η κ)
      (fun g₁ κ => ∀ g₂ ∈ Icc (0 : ℤ) 4, Tb.PostGoodOff (Bs \ Ta.Y) L γ (η / 2 / 2) (Ta.postLabels κ g₁) g₂ →
        Q (MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂))) L γ (η / 2) P' g₁)
    (by
      rintro κ' ⟨_, κ, ⟨hκ, _⟩, _, _, rfl⟩
      exact ⟨Tb.x, Tb.y, Tb.atom_x, hxy, Tb.ne, hgap κ hκ g₁⟩)
  refine hC.trans (mul_le_mul' le_rfl ?_)
  refine (MoleProp.countAFree_le_of_dart_equiv (Degen.eraseAtoms Ta.post Tb.Y) (MoleProp.eraseBond cl e) ι hAe hae
    hme hoe L γ δ C1 0 _ (fun κ => lgAdm (MoleProp.eraseBond cl e) L γ (η / 2 / 2) P' κ ∧
      MoleProp.erasedBondAdmissibility cl e (fun κ0 => MoleProp.LargeGap cl L γ (η / 2 / 2) (0 : Mom d) κ0 ∧ Q κ0) κ)
    ?_ P').trans (hQ2 P' (fun S hS => hPerase S (by rw [hcellsE]; exact hS)))
  rintro κ'' ⟨κ', ⟨hlg', κ, ⟨hκ, hn⟩, hsym, hW, rfl⟩, hsym', rfl⟩
  have hlgE := lgAdmOff_erase Ta.post (Bs \ Ta.Y) Tb.Y hlg'
  rw [hBs] at hlgE
  have h2 := lgAdm_mono (Degen.eraseAtoms Ta.post Tb.Y) hL (show η / 2 / 2 ≤ η / 2 by linarith) (lgAdmOff_empty hlgE)
  refine ⟨lgAdm_relabel _ _ ι hAe hae hme hoe h2, ?_⟩
  obtain ⟨g₂, hg₂, hpb⟩ := Tb.exists_postGoodOff hL hL11b (κ := Ta.postLabels κ g₁) hsym' hcap1 (Bs \ Ta.Y) hcBb hdBb
    hlg'.1
  refine ⟨MoleProp.relabelDartLabels Φ (Tb.postLabels (Ta.postLabels κ g₁) g₂),
    ⟨FinalCountG8.largeGap_relabel Tb.post cl Φ ha ho (postGoodOff_largeGap Tb hBs hpb), hW g₂ hg₂ hpb⟩, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := Φ.surjective x
    rw [hm, relabel_apply, relabel_apply]
    exact Tb.postLabels_mate hsym' g₂ y
  · funext x
    obtain ⟨z, rfl⟩ := ι.surjective x
    change MoleProp.relabelDartLabels Φ _ (Φ (Sum.inl z)) = MoleProp.relabelDartLabels ι _ (ι z)
    rw [relabel_apply, relabel_apply]
    rfl

end

theorem split_arith_sharp {d m : ℕ} {L γ δ ηs a : ℝ} (hδ : 0 < δ) (hLe : Real.exp 1 ≤ L)
    (ha0 : 0 ≤ a) (ha : a ≤ (1 + Real.log L) ^ m)
    (hbig : splitK d m δ * Real.log L ^ (56 + m) ≤ L ^ (ηs / 32)) :
    21125 * Real.log L ^ (14 : ℝ) * (21125 * Real.log L ^ (14 : ℝ) *
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 * ((a + 1) * L ^ (-(ηs / 16))))) +
      21125 * Real.log L ^ (14 : ℝ) * (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ) *
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
          ((a + 1) * L ^ (-(min γ (1 - γ) + ηs / 16))))) ≤ L ^ (-(ηs / 32)) := by
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  set ℓ := Real.log L with hℓ
  have h14 : ℓ ^ (14 : ℝ) = ℓ ^ 14 := by
    rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h8 : ℓ ^ (8 : ℝ) = ℓ ^ 8 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hexp : L ^ min γ (1 - γ) * L ^ (-(min γ (1 - γ) + ηs / 16)) = L ^ (-(ηs / 16)) := by
    rw [← Real.rpow_add hLp]; congr 1; ring
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hS : ((scaleSet L).card : ℝ) ≤ 5 * ℓ := card_scaleSet_le_log hlog
  have hS0 : (0 : ℝ) ≤ (scaleSet L).card := Nat.cast_nonneg _
  set Ks := (110 * ((scaleSet L).card : ℝ) ^ 2 * (ℓ ^ 2) ^ 6) ^ 2 with hKs
  have hKs0 : 0 ≤ Ks := sq_nonneg _
  have hKsle : Ks ≤ 2750 ^ 2 * ℓ ^ 28 := by
    have h1 : 110 * ((scaleSet L).card : ℝ) ^ 2 * (ℓ ^ 2) ^ 6 ≤ 2750 * ℓ ^ 14 := by
      have h2 : ((scaleSet L).card : ℝ) ^ 2 ≤ (5 * ℓ) ^ 2 := pow_le_pow_left₀ hS0 hS 2
      calc 110 * ((scaleSet L).card : ℝ) ^ 2 * (ℓ ^ 2) ^ 6 ≤ 110 * (5 * ℓ) ^ 2 * (ℓ ^ 2) ^ 6 := by gcongr
        _ = 2750 * ℓ ^ 14 := by ring
    calc Ks ≤ (2750 * ℓ ^ 14) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = 2750 ^ 2 * ℓ ^ 28 := by ring
  have hbound : a + 1 ≤ 2 ^ (m + 1) * ℓ ^ m := by
    have h1 : (1 : ℝ) ≤ (1 + ℓ) ^ m := one_le_pow₀ (by linarith)
    have h2 : (1 + ℓ) ^ m ≤ (2 * ℓ) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
    calc a + 1 ≤ (1 + ℓ) ^ m + 1 := by linarith
      _ ≤ 2 * (1 + ℓ) ^ m := by linarith
      _ ≤ 2 * (2 * ℓ) ^ m := by linarith
      _ = 2 ^ (m + 1) * ℓ ^ m := by rw [mul_pow, pow_succ]; ring
  have hc3 : 0 ≤ 2 * 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) := by positivity
  set c3 := 2 * 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) with hc3d
  rw [h14, h8]
  have hLm0 : 0 ≤ L ^ (-(ηs / 16)) := Real.rpow_nonneg hLp.le _
  have e : 21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 * (Ks * ((a + 1) * L ^ (-(ηs / 16))))) +
      21125 * ℓ ^ 14 * (c3 * ℓ ^ 8 * L ^ min γ (1 - γ) * (Ks * ((a + 1) * L ^ (-(min γ (1 - γ) + ηs / 16))))) =
      (21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 + c3 * ℓ ^ 8) * Ks * (a + 1)) * L ^ (-(ηs / 16)) := by
    have h := hexp
    calc _ = 21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 + c3 * ℓ ^ 8) * Ks * (a + 1) * (L ^ min γ (1 - γ) * L ^ (-(min γ (1 - γ) + ηs / 16))) -
        21125 * ℓ ^ 14 * (21125 * ℓ ^ 14) * Ks * (a + 1) * (L ^ min γ (1 - γ) * L ^ (-(min γ (1 - γ) + ηs / 16))) +
        21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 * (Ks * ((a + 1) * L ^ (-(ηs / 16))))) := by ring
      _ = _ := by rw [h]; ring
  have h8le : ℓ ^ 8 ≤ ℓ ^ 14 := pow_le_pow_right₀ hlog (by norm_num)
  have hT : 21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 + c3 * ℓ ^ 8) * Ks * (a + 1) ≤ splitK d m δ * ℓ ^ (56 + m) := by
    have hsum : 21125 * ℓ ^ 14 + c3 * ℓ ^ 8 ≤ (21125 + c3) * ℓ ^ 14 := by nlinarith
    calc 21125 * ℓ ^ 14 * (21125 * ℓ ^ 14 + c3 * ℓ ^ 8) * Ks * (a + 1)
        ≤ 21125 * ℓ ^ 14 * ((21125 + c3) * ℓ ^ 14) * (2750 ^ 2 * ℓ ^ 28) * (2 ^ (m + 1) * ℓ ^ m) := by
          have hp1 : 0 ≤ 21125 * ℓ ^ 14 + c3 * ℓ ^ 8 := by positivity
          have hp2 : 0 ≤ a + 1 := by linarith
          gcongr
      _ = splitK d m δ * ℓ ^ (56 + m) := by unfold splitK; rw [pow_add ℓ 56 m]; ring
  rw [e]
  calc _ ≤ (splitK d m δ * ℓ ^ (56 + m)) * L ^ (-(ηs / 16)) := mul_le_mul_of_nonneg_right hT hLm0
    _ ≤ L ^ (ηs / 32) * L ^ (-(ηs / 16)) := mul_le_mul_of_nonneg_right hbig hLm0
    _ = L ^ (-(ηs / 32)) := by rw [← Real.rpow_add hLp]; congr 1; ring


theorem case4_two_split_all (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M₀ : Molecule V D),
        (∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) → (∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z)) →
        (∀ a ∈ M₀.atoms, M₀.deg a % 2 = 0) → (∀ a ∈ M₀.atoms, ∀ c ∈ M₀.atoms, M₀.SameComponent a c) →
        ∀ (b b' : V) (y₁ y₂ y₃ y₄ : D), b ∈ M₀.atoms → b' ∈ M₀.atoms → b ≠ b' →
        (M₀.outdeg b = 1 ∧ M₀.indeg b = 1) → (M₀.outdeg b' = 1 ∧ M₀.indeg b' = 1) →
        crossDarts M₀ {b} = {y₁, y₂} → M₀.out y₁ = false → M₀.out y₂ = true →
        crossDarts M₀ {b'} = {y₃, y₄} → M₀.out y₃ = false → M₀.out y₄ = true →
        M₀.atom (M₀.mate y₁) ≠ M₀.atom (M₀.mate y₂) → M₀.atom (M₀.mate y₃) ≠ M₀.atom (M₀.mate y₄) →
        M₀.atom (M₀.mate y₁) ≠ b' → M₀.atom (M₀.mate y₂) ≠ b' →
        M₀.atom (M₀.mate y₃) ≠ b → M₀.atom (M₀.mate y₄) ≠ b →
        RegCore (closureTwo M₀ b b' y₁ y₂ y₃ y₄) → (tripSet (closureTwo M₀ b b' y₁ y₂ y₃ y₄)).card ≤ 2 →
        ((closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        5 ≤ (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card → ¬ YReachesQT (closureTwo M₀ b b' y₁ y₂ y₃ y₄) →
        ¬ YReachesSmallCell (closureTwo M₀ b b' y₁ y₂ y₃ y₄) →
        ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S) →
        ∀ Adm : (D → (Fin d → ℤ)) → Prop,
          (∀ κ, Adm κ → lgAdmOff M₀ {b, b'} L γ η P κ ∧ κ y₁ ≠ κ y₂ ∧ κ y₃ ≠ κ y₄) →
          MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128))) := by
  have hγ0 : γ ∈ Set.Ioo (0 : ℝ) 1 := hγ
  have hpos : 0 < min γ (1 - γ) := lt_min hγ0.1 (by linarith [hγ.2])
  have hηs0 : 0 < η / 2 / 2 := by positivity
  obtain ⟨Cs, hCs, hP104⟩ := Count.prop104_two_proved_low.{u, v} d hd γ hγ0 (η / 2 / 2) hηs0 (by linarith) (by
      have : (d : ℝ) * (η / 2 / 2) ≤ d * η := by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith
      linarith) (by linarith)
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R1, hR1⟩ := hP104 m C1 hC1 δ hδ
  obtain ⟨A0, hA0⟩ := exists_mul_log_rpow_le (splitK d m δ) (((56 + m : ℕ) : ℝ)) (θ := η / 2 / 2 / 32) (by positivity)
  refine ⟨max (max R1 A0) (max (Real.exp 1) ((11 : ℝ) ^ (1 / (η / 2 / 2)))), fun L hL => ?_⟩
  have hLR1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLA0 : A0 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL11' : (11 : ℝ) ^ (1 / (η / 2 / 2)) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hL11b : 11 ≤ L ^ (η / 2 / 2) := eleven_le_rpow hηs0 hL11'
  have hL11a : 11 ≤ L ^ (η / 2) := by
    refine hL11b.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hbig : splitK d m δ * Real.log L ^ (56 + m) ≤ L ^ (η / 2 / 2 / 32) := by
    have := hA0 L hLA0
    rwa [Real.rpow_natCast] at this
  have hδ0 := hδ.1
  intro V D _ _ _ M₀ hcap hloop heven hconn0 b b' y₁ y₂ y₃ y₄ hb hb' hbb' hdb hdb' hc1 ho1 ho2 hc2 ho3 ho4 huv huv'
    hs1 hs2 hs3 hs4 hcl htrip hsz h5 hnq hnsc P hP Adm hAdm
  classical
  have hy12 : y₁ ≠ y₂ := fun h => huv (by rw [h])
  have hy34 : y₃ ≠ y₄ := fun h => huv' (by rw [h])
  have hy1m : y₁ ∈ crossDarts M₀ {b} := by rw [hc1]; exact mem_insert_self _ _
  have hy2m : y₂ ∈ crossDarts M₀ {b} := by rw [hc1]; exact mem_insert_of_mem (mem_singleton_self _)
  have hy3m : y₃ ∈ crossDarts M₀ {b'} := by rw [hc2]; exact mem_insert_self _ _
  have hy4m : y₄ ∈ crossDarts M₀ {b'} := by rw [hc2]; exact mem_insert_of_mem (mem_singleton_self _)
  have hat3 : M₀.atom y₃ = b' := mem_singleton.mp (mem_crossDarts.mp hy3m).1
  have hat4 : M₀.atom y₄ = b' := mem_singleton.mp (mem_crossDarts.mp hy4m).1
  have hu1 : M₀.atom (M₀.mate y₁) ≠ b := fun h => (mem_crossDarts.mp hy1m).2 (by rw [h]; exact mem_singleton_self _)
  have hu2 : M₀.atom (M₀.mate y₂) ≠ b := fun h => (mem_crossDarts.mp hy2m).2 (by rw [h]; exact mem_singleton_self _)
  have hu3 : M₀.atom (M₀.mate y₃) ≠ b' := fun h => (mem_crossDarts.mp hy3m).2 (by rw [h]; exact mem_singleton_self _)
  have hu4 : M₀.atom (M₀.mate y₄) ≠ b' := fun h => (mem_crossDarts.mp hy4m).2 (by rw [h]; exact mem_singleton_self _)
  have hKA : ({b} : Finset V) ⊆ M₀.atoms := by simpa using hb
  -- the first chain
  let Ta : TwoExit M₀ := ⟨{b}, hKA, y₂, y₁, by rw [hc1]; exact pair_comm _ _, hy12.symm, huv.symm, ho2, ho1⟩
  have p₃ : M₀.atom y₃ ∉ ({b} : Finset V) ∧ M₀.atom (M₀.mate y₃) ∉ ({b} : Finset V) :=
    ⟨by rw [hat3]; simpa using hbb'.symm, by simpa using hs3⟩
  have p₄ : M₀.atom y₄ ∉ ({b} : Finset V) ∧ M₀.atom (M₀.mate y₄) ∉ ({b} : Finset V) :=
    ⟨by rw [hat4]; simpa using hbb'.symm, by simpa using hs4⟩
  obtain ⟨hcK, hdir⟩ := chain_after_erase hloop hc2 p₃ p₄
  have hc1' : M₀.atom (M₀.mate y₁) ∉ ({b'} : Finset V) := by simpa using hs1
  have hc2' : M₀.atom (M₀.mate y₂) ∉ ({b'} : Finset V) := by simpa using hs2
  have hcross2 : crossDarts Ta.post {b'} = {Sum.inl ⟨y₄, p₄⟩, Sum.inl ⟨y₃, p₃⟩} := by
    change crossDarts (Mole.addBond (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))) {b'} = _
    rw [crossDarts_addBond_inl _ hc1' hc2' hcK]
    exact pair_comm _ _
  have hbN : ({b'} : Finset V) ⊆ Ta.post.atoms := by
    rw [Ta.post_atoms]
    intro x hx
    rw [mem_singleton] at hx
    rw [hx]
    exact mem_sdiff.mpr ⟨hb', by show b' ∉ ({b} : Finset V); simpa using hbb'.symm⟩
  let Tb : TwoExit Ta.post := ⟨{b'}, hbN, Sum.inl ⟨y₄, p₄⟩, Sum.inl ⟨y₃, p₃⟩, hcross2,
    fun h => hy34 (congrArg Subtype.val (Sum.inl.inj h)).symm, huv'.symm, ho4, ho3⟩
  let Φ : Degen.RetainedDart Ta.post Tb.Y ⊕ Bool ≃
      (Degen.RetainedDart (Degen.eraseAtoms M₀ {b}) {b'} ⊕ Bool) ⊕ Bool :=
    bondPostEquiv (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂)) {b'} hc1' hc2'
  have hA : Tb.post.atoms = (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms :=
    bondPostEquiv_atoms (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))
      (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄)) {b'} hc1' hc2'
  have ha : ∀ x, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).atom (Φ x) = Tb.post.atom x := fun x =>
    bondPostEquiv_atom (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))
      (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄)) {b'} hc1' hc2' x
  have hm : ∀ x, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).mate (Φ x) = Φ (Tb.post.mate x) := fun x =>
    bondPostEquiv_mate (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))
      (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄)) {b'} hc1' hc2' x
  have ho : ∀ x, (closureTwo M₀ b b' y₁ y₂ y₃ y₄).out (Φ x) = Tb.post.out x := fun x =>
    bondPostEquiv_out (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))
      (M₀.atom (M₀.mate y₃)) (M₀.atom (M₀.mate y₄)) {b'} hc1' hc2' x
  have hSplit := hR1 L hLR1 (closureTwo M₀ b b' y₁ y₂ y₃ y₄) hcl.cap hcl.loop hcl.reg hcl.conn hcl.nocut
    (triple_of_tripSet htrip) (bb_le_three_of_nonexc hcl hnq) hsz hnq hnsc (Φ (Sum.inr true))
  obtain ⟨Q, hQ1, hQ2⟩ := hSplit
  -- structure of the first post
  have hpostA : ∀ a ∈ Ta.post.atoms, ∀ c ∈ Ta.post.atoms, Ta.post.SameComponent a c := Ta.post_connected hconn0
  have h5A : 5 ≤ Ta.post.atoms.card := h5.trans (card_le_card (by
    rw [← hA, Tb.post_atoms]; exact sdiff_subset))
  have hopenA : ∀ S ∈ MoleProp.ladderCells Ta.post, GoodCell Ta.post S := fun S hS => goodCell_of_connected hpostA h5A hS
  have hcap1 := Ta.post_caps hcap
  have hloop1 := Ta.post_loop hloop
  have hdb2 : (Degen.eraseAtoms M₀ {b}).outdeg b' = 1 ∧ (Degen.eraseAtoms M₀ {b}).indeg b' = 1 := by
    unfold Molecule.outdeg Molecule.indeg; rw [hdir true, hdir false]; exact hdb'
  have hchb : ∀ x ∈ Tb.Y, Ta.post.outdeg x = 1 ∧ Ta.post.indeg x = 1 := by
    intro x hx
    have hx' : x = b' := mem_singleton.mp hx
    subst hx'
    have hdne : M₀.atom (M₀.mate y₁) ≠ x := fun h => hc1' (by rw [h]; exact mem_singleton_self _)
    have hcne : M₀.atom (M₀.mate y₂) ≠ x := fun h => hc2' (by rw [h]; exact mem_singleton_self _)
    constructor
    · change (Mole.addBond (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))).outdeg x = 1
      rw [addBond_outdeg, if_neg hdne, add_zero]; exact hdb2.1
    · change (Mole.addBond (Degen.eraseAtoms M₀ {b}) (M₀.atom (M₀.mate y₁)) (M₀.atom (M₀.mate y₂))).indeg x = 1
      rw [addBond_indeg', if_neg hcne, add_zero]; exact hdb2.2
  have hYconna : ∀ x ∈ Ta.Y, ∀ y ∈ Ta.Y, (piece M₀ Ta.Y).SameComponent x y := fun x hx y hy => by
    rw [mem_singleton.mp hx, mem_singleton.mp hy]; exact Relation.EqvGen.refl _
  have hYconnb : ∀ x ∈ Tb.Y, ∀ y ∈ Tb.Y, (piece Ta.post Tb.Y).SameComponent x y := fun x hx y hy => by
    rw [mem_singleton.mp hx, mem_singleton.mp hy]; exact Relation.EqvGen.refl _
  have hcBa : Ta.c ∉ ({b, b'} : Finset V) := by
    change M₀.atom (M₀.mate y₂) ∉ ({b, b'} : Finset V)
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hu2, hs2⟩
  have hdBa : Ta.d ∉ ({b, b'} : Finset V) := by
    change M₀.atom (M₀.mate y₁) ∉ ({b, b'} : Finset V)
    simp only [mem_insert, mem_singleton, not_or]; exact ⟨hu1, hs1⟩
  have hcBb : Tb.c ∉ (({b, b'} : Finset V) \ Ta.Y) := by
    change M₀.atom (M₀.mate y₄) ∉ (({b, b'} : Finset V) \ {b})
    simp only [mem_sdiff, mem_insert, mem_singleton, not_and, not_not]
    intro h; rcases h with h | h
    · exact h
    · exact absurd h hu4
  have hdBb : Tb.d ∉ (({b, b'} : Finset V) \ Ta.Y) := by
    change M₀.atom (M₀.mate y₃) ∉ (({b, b'} : Finset V) \ {b})
    simp only [mem_sdiff, mem_insert, mem_singleton, not_and, not_not]
    intro h; rcases h with h | h
    · exact h
    · exact absurd h hu3
  have hpostB : ∀ a ∈ Tb.post.atoms, ∀ c ∈ Tb.post.atoms, Tb.post.SameComponent a c := Tb.post_connected hpostA
  have h5B : 5 ≤ Tb.post.atoms.card := by rw [hA]; exact h5
  have hopenB : ∀ S ∈ MoleProp.ladderCells Tb.post, GoodCell Tb.post S := fun S hS => goodCell_of_connected hpostB h5B hS
  have hBs : ((({b, b'} : Finset V) \ Ta.Y) \ Tb.Y) = ∅ := by
    change ((({b, b'} : Finset V) \ {b}) \ {b'}) = ∅
    ext x; simp only [mem_sdiff, mem_insert, mem_singleton, notMem_empty, iff_false]; tauto
  have heven1 : ∀ a ∈ Ta.post.atoms, Ta.post.deg a % 2 = 0 := by
    intro a ha
    rw [Ta.post_atoms] at ha
    obtain ⟨ha1, ha2⟩ := mem_sdiff.mp ha
    rw [Ta.post_deg ha2]; exact heven a ha1
  have hpostE : ∀ a ∈ (Degen.eraseAtoms Ta.post Tb.Y).atoms, ∀ c ∈ (Degen.eraseAtoms Ta.post Tb.Y).atoms,
      (Degen.eraseAtoms Ta.post Tb.Y).SameComponent a c :=
    connected_erase_of_two_cross Ta.post hpostA heven1 {b'} (by
      rw [hcross2]; exact card_pair (fun h => hy34 (congrArg Subtype.val (Sum.inl.inj h)).symm))
  have hxy : Ta.post.atom Tb.y = Ta.post.atom Tb.x := by
    change M₀.atom y₃ = M₀.atom y₄
    rw [hat3, hat4]
  have hY3a : Ta.Y.card ≤ 3 := by change ({b} : Finset V).card ≤ 3; simp
  have hY3b : Tb.Y.card ≤ 3 := by change ({b'} : Finset V).card ≤ 3; simp
  have hcha : ∀ x ∈ Ta.Y, M₀.outdeg x = 1 ∧ M₀.indeg x = 1 := fun x hx => by
    rw [mem_singleton.mp hx]; exact hdb
  -- the two classes
  have hcls1 := class1_bound (η := η) hL1 hlog hδ (hCs.trans hC1) Ta Tb {b, b'} hcap hloop hconn0 hY3a hcha hYconna hpostA hopenA
    hcap1 hloop1 hY3b hchb hYconnb hpostB hopenB hBs (closureTwo M₀ b b' y₁ y₂ y₃ y₄) Φ hA ha hm ho Q hQ1 P hP Adm
    (fun κ h => (hAdm κ h).1)
  have hcls2 := class2_bound_sharp (η := η) hL1 hlog hη.le hγ0 hδ (hCs.trans hC1) hL11a hL11b Ta Tb {b, b'} hcap hloop hconn0 hY3a hcha
    hYconna hcBa hdBa hpostA hopenA hcap1 hloop1 hchb hYconnb hcBb hdBb hpostE hxy hBs
    (closureTwo M₀ b b' y₁ y₂ y₃ y₄) Φ hA ha hm ho Q hQ2 P hP Adm (fun κ h => (hAdm κ h).1)
    (fun κ hκ g h => (hAdm κ hκ).2.2 h.symm)
  have hl0 : 0 ≤ Real.log L := by linarith
  have hA0 : 0 ≤ 21125 * Real.log L ^ (14 : ℝ) := mul_nonneg (by norm_num) (Real.rpow_nonneg hl0 _)
  have hC0 : 0 ≤ 2 * 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hl0 _)) (Real.rpow_nonneg hLp.le _)
  have hε1 : 0 ≤ (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
      ((((closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card : ℕ) + 1 : ℝ) * L ^ (-(η / 2 / 2 / 16))) := by
    have := hLp; positivity
  have hε2 : 0 ≤ (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
      (((((closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card : ℕ) : ℝ) + 1) * L ^ (-(min γ (1 - γ) + η / 2 / 2 / 16))) := by
    have := hLp; positivity
  have hs := split_arith_sharp (d := d) (m := m) (L := L) (γ := γ) (δ := δ) (ηs := η / 2 / 2)
    (a := ((closureTwo M₀ b b' y₁ y₂ y₃ y₄).atoms.card : ℝ)) hδ0 hLe (Nat.cast_nonneg _) hsz hbig
  refine (countAFree_or_le M₀ L γ δ C1 P Adm (fun κ => Adm κ ∧ Cls1 Ta Tb Φ Q {b, b'} L γ η κ)
    (fun κ => Adm κ ∧ ¬ Cls1 Ta Tb Φ Q {b, b'} L γ η κ) (fun κ hκ => by
      by_cases h : Cls1 Ta Tb Φ Q {b, b'} L γ η κ
      · exact Or.inl ⟨hκ, h⟩
      · exact Or.inr ⟨hκ, h⟩)).trans ((add_le_add hcls1 hcls2).trans ?_)
  refine (ofReal_sum_bound _ _ _ _ _ hA0 hC0 hε1 hε2 hs).trans (le_of_eq ?_)
  congr 2
  ring


theorem case4_one_split_all (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hη200 : η ≤ min γ (1 - γ) / 200) (hηd : d * η ≤ min γ (1 - γ) / 4) (hηs : 4 * 1440061 * η ≤ 1) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m : ℕ, ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M₀ : Molecule V D),
        (∀ a ∈ M₀.atoms, M₀.outdeg a ≤ 2 ∧ M₀.indeg a ≤ 2) → (∀ z, M₀.atom z ≠ M₀.atom (M₀.mate z)) →
        ∀ (b b' : V) (x₁ x₂ y y' : D), b ∈ M₀.atoms → b' ∈ M₀.atoms →
        (M₀.outdeg b = 1 ∧ M₀.indeg b = 1) → (M₀.outdeg b' = 1 ∧ M₀.indeg b' = 1) →
        crossDarts M₀ {b, b'} = {x₁, x₂} → M₀.out x₁ = false → M₀.out x₂ = true →
        M₀.atom (M₀.mate x₁) ≠ M₀.atom (M₀.mate x₂) →
        M₀.atom y = b → M₀.atom y' = b → y ≠ y' →
        (∀ a ∈ M₀.atoms, ∀ c ∈ M₀.atoms, M₀.SameComponent a c) →
        (∀ a ∈ ({b, b'} : Finset V), ∀ c ∈ ({b, b'} : Finset V), (piece M₀ {b, b'}).SameComponent a c) →
        (∀ a ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms, ∀ c ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms,
          (Degen.eraseAtoms M₀ {b, b'}).SameComponent a c) →
        RegCore (closureOne M₀ b b' x₁ x₂) →
        (tripSet (closureOne M₀ b b' x₁ x₂)).card ≤ 2 →
        ((closureOne M₀ b b' x₁ x₂).atoms.card : ℝ) ≤ (1 + Real.log L) ^ m →
        5 ≤ (closureOne M₀ b b' x₁ x₂).atoms.card → ¬ YReachesQT (closureOne M₀ b b' x₁ x₂) →
        ¬ YReachesSmallCell (closureOne M₀ b b' x₁ x₂) →
        ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells M₀, 0 ≤ P S) →
        ∀ Adm : (D → (Fin d → ℤ)) → Prop,
          (∀ κ, Adm κ → lgAdmOff M₀ {b, b'} L γ η P κ ∧ κ y ≠ κ y') →
          MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) Adm P ≤ ENNReal.ofReal (L ^ (-(η / 128))) := by
  have hγ0 : γ ∈ Set.Ioo (0 : ℝ) 1 := hγ
  have hpos : 0 < min γ (1 - γ) := lt_min hγ0.1 (by linarith [hγ.2])
  have hηs0 : 0 < η / 2 := by positivity
  obtain ⟨Cs, hCs, hP104⟩ := Count.prop104_two_proved_low.{u, v} d hd γ hγ0 (η / 2) hηs0 (by linarith) (by
      have : (d : ℝ) * (η / 2) ≤ d * η := by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
        nlinarith
      linarith) (by linarith)
  refine ⟨Cs, hCs, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨R1, hR1⟩ := hP104 m C1 hC1 δ hδ
  obtain ⟨A0, hA0⟩ := exists_mul_log_rpow_le (splitK d m δ) (((56 + m : ℕ) : ℝ)) (θ := η / 2 / 32) (by positivity)
  refine ⟨max (max R1 A0) (max (Real.exp 1) ((11 : ℝ) ^ (1 / (η / 2)))), fun L hL => ?_⟩
  have hLR1 : R1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLA0 : A0 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hL11' : (11 : ℝ) ^ (1 / (η / 2)) ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hL11 : 11 ≤ L ^ (η / 2) := eleven_le_rpow hηs0 hL11'
  have hbig : splitK d m δ * Real.log L ^ (56 + m) ≤ L ^ (η / 2 / 32) := by
    have := hA0 L hLA0
    rwa [Real.rpow_natCast] at this
  have hδ0 := hδ.1
  intro V D _ _ _ M₀ hcap hloop b b' x₁ x₂ y y' hb hb' hdb hdb' hc ho1 ho2 huv hy hy' hyy' hconn0 hYconn hconnK hcl
    htrip hsz h5 hnq hnsc P hP Adm hAdm
  classical
  have hne : x₂ ≠ x₁ := fun h => huv (by rw [h])
  have hx1m : x₁ ∈ crossDarts M₀ {b, b'} := by rw [hc]; exact mem_insert_self _ _
  have hx2m : x₂ ∈ crossDarts M₀ {b, b'} := by rw [hc]; exact mem_insert_of_mem (mem_singleton_self _)
  have hY : ({b, b'} : Finset V) ⊆ M₀.atoms := by
    intro z hz; simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
  let T : TwoExit M₀ := ⟨{b, b'}, hY, x₂, x₁, by rw [hc]; exact pair_comm _ _, hne, huv.symm, ho2, ho1⟩
  have hSplit := hR1 L hLR1 (closureOne M₀ b b' x₁ x₂) hcl.cap hcl.loop hcl.reg hcl.conn hcl.nocut
    (triple_of_tripSet htrip) (bb_le_three_of_nonexc hcl hnq) hsz hnq hnsc (Sum.inr true)
  obtain ⟨Q, hQ1, hQ2⟩ := hSplit
  have hpost : ∀ a ∈ T.post.atoms, ∀ c ∈ T.post.atoms, T.post.SameComponent a c := hcl.conn
  have hopen : ∀ S ∈ MoleProp.ladderCells T.post, GoodCell T.post S := fun S hS => goodCell_of_connected hpost h5 hS
  have hch : ∀ x ∈ T.Y, M₀.outdeg x = 1 ∧ M₀.indeg x = 1 := fun x hx => by
    rcases mem_insert.mp hx with rfl | h
    · exact hdb
    · rw [mem_singleton.mp h]; exact hdb'
  have hBs : ({b, b'} : Finset V) \ T.Y = ∅ := by
    change ({b, b'} : Finset V) \ {b, b'} = ∅
    simp
  have hY3 : T.Y.card ≤ 3 := by
    change ({b, b'} : Finset V).card ≤ 3
    exact (card_insert_le _ _).trans (by simp)
  have hcB : T.c ∉ ({b, b'} : Finset V) := (mem_crossDarts.mp hx2m).2
  have hdB : T.d ∉ ({b, b'} : Finset V) := (mem_crossDarts.mp hx1m).2
  -- the first class: operation (d)
  have hcls1 : MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧ Cls1One T Q {b, b'} L γ η κ) P ≤
      ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) * ENNReal.ofReal
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
          (((closureOne M₀ b b' x₁ x₂).atoms.card + 1 : ℝ) * L ^ (-(η / 2 / 16)))) := by
    have hA1 := opDW hL1 hlog hδ (hCs.trans hC1) M₀ T hcap hloop hconn0 {b, b'} hY3 hch hYconn hpost hopen P hP
      (fun κ => Adm κ ∧ Cls1One T Q {b, b'} L γ η κ) (fun κ h => (hAdm κ h.1).1)
      (fun g κ => ¬ Q (T.postLabels κ g))
      (by
        rintro κ ⟨hκ, g, hg, hpg, hnq'⟩ _
        exact ⟨g, hg, hpg, hnq'⟩)
    refine hA1.trans (mul_le_mul' le_rfl ?_)
    refine iSup₂_le fun g hg => ?_
    unfold TwoExit.afreeSupPost
    refine iSup₂_le fun P' hP' => ?_
    refine (countAFree_mono_adm T.post (L := L) (γ := γ) (δ := δ) (C1 := C1) (P := P')
      (B := fun κ => lgAdm T.post L γ (η / 2) P' κ ∧ ¬ Q κ) ?_).trans (hQ1 P' hP')
    rintro κ''' ⟨hlg, κ, _, _, hnq', rfl⟩
    rw [hBs] at hlg
    exact ⟨lgAdmOff_empty hlg, hnq'⟩
  -- the second class: operation (c)
  have hcls2 : MoleProp.countAFree M₀ L γ δ C1 (0 : Mom d) (fun κ => Adm κ ∧ ¬ Cls1One T Q {b, b'} L γ η κ) P ≤
      ENNReal.ofReal (2 * 3 ^ d * (d * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ)) * ENNReal.ofReal
        ((110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
          (((closureOne M₀ b b' x₁ x₂).atoms.card + 1 : ℝ) * L ^ (-(min γ (1 - γ) + η / 2 / 16)))) := by
    have hC := opCFree_sharp hγ0 hL1 hlog hδ (hCs.trans hC1) M₀ hloop hcap hconn0 {b, b'} x₁ x₂ hY
      (fun z hz => by simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption)
      hc huv hYconn hconnK P hP (fun κ => Adm κ ∧ ¬ Cls1One T Q {b, b'} L γ η κ)
      (fun κ h => ⟨y, y', by rw [hy]; exact mem_insert_self _ _, by rw [hy, hy'], hyy', (hAdm κ h.1).2⟩)
    refine hC.trans (mul_le_mul' le_rfl ?_)
    have hu : M₀.atom (M₀.mate x₁) ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms :=
      mem_sdiff.mpr ⟨M₀.atom_mem _, (mem_crossDarts.mp hx1m).2⟩
    have hv : M₀.atom (M₀.mate x₂) ∈ (Degen.eraseAtoms M₀ {b, b'}).atoms :=
      mem_sdiff.mpr ⟨M₀.atom_mem _, (mem_crossDarts.mp hx2m).2⟩
    set a := M₀.atom (M₀.mate x₁) with ha_def
    set c := M₀.atom (M₀.mate x₂) with hc_def
    let ι := addBondEraseEquiv (Degen.eraseAtoms M₀ {b, b'}) a c
    have hA : (Degen.eraseAtoms M₀ {b, b'}).atoms =
        (MoleProp.eraseBond (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) (Sum.inr true)).atoms := by
      change (Degen.eraseAtoms M₀ {b, b'}).atoms = insert a (insert c (Degen.eraseAtoms M₀ {b, b'}).atoms)
      rw [insert_eq_of_mem hv, insert_eq_of_mem hu]
    have hcells := ladderCells_addBond_erase (Degen.eraseAtoms M₀ {b, b'}) hu hv
    have hPerase : ∀ S' ∈ MoleProp.ladderCells (Degen.eraseAtoms M₀ {b, b'}), 0 ≤ P S' := fun S' hS' => by
      have := (MoleProp.isLadderCell_erase_iff M₀ {b, b'} S').mp (mem_filter.mp hS').2
      exact hP S' (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M₀ this.1), this.1⟩)
    have hself : ({b, b'} : Finset V) \ {b, b'} = ∅ := by simp
    refine (MoleProp.countAFree_le_of_dart_equiv (Degen.eraseAtoms M₀ {b, b'})
      (MoleProp.eraseBond (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) (Sum.inr true)) ι hA
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) L γ δ C1 0 _
      (fun κ => lgAdm (MoleProp.eraseBond (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) (Sum.inr true))
          L γ (η / 2) P κ ∧
        MoleProp.erasedBondAdmissibility (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) (Sum.inr true)
          (fun κ0 => MoleProp.LargeGap (Mole.addBond (Degen.eraseAtoms M₀ {b, b'}) a c) L γ (η / 2) (0 : Mom d) κ0 ∧
            Q κ0) κ) ?_ P).trans
      (hQ2 P (fun S hS => hPerase S (by rw [← hcells]; exact hS)))
    rintro κ'' ⟨κ, ⟨hκ, hn⟩, hsym, rfl⟩
    have hlgE := lgAdmOff_erase M₀ {b, b'} {b, b'} (hAdm κ hκ).1
    rw [hself] at hlgE
    refine ⟨lgAdm_relabel _ _ ι hA (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      (lgAdm_mono (Degen.eraseAtoms M₀ {b, b'}) hL1 (show η / 2 ≤ η by linarith) (lgAdmOff_empty hlgE)), ?_⟩
    obtain ⟨g, hg, hpg⟩ := T.exists_postGoodOff hL1 hL11 hsym hcap {b, b'} hcB hdB (hAdm κ hκ).1.1
    refine ⟨T.postLabels κ g, ⟨postGoodOff_largeGap T hBs hpg, ?_⟩, T.postLabels_mate hsym g, ?_⟩
    · by_contra hq
      exact hn ⟨g, hg, hpg, hq⟩
    · funext x
      obtain ⟨z, rfl⟩ := ι.surjective x
      change T.postLabels κ g (Sum.inl z) = MoleProp.relabelDartLabels ι _ (ι z)
      rw [relabel_apply]
      rfl
  have hA1 : 1 ≤ 21125 * Real.log L ^ (14 : ℝ) := by
    have := Real.one_le_rpow hlog (show (0 : ℝ) ≤ 14 by norm_num)
    linarith
  have hl0 : 0 ≤ Real.log L := by linarith
  have hA0 : 0 ≤ 21125 * Real.log L ^ (14 : ℝ) := by linarith
  have hC0 : 0 ≤ 2 * 3 ^ d * ((d : ℝ) * δ⁻¹ + 1) * Real.log L ^ (8 : ℝ) * L ^ min γ (1 - γ) :=
    mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg hl0 _)) (Real.rpow_nonneg hLp.le _)
  have hε1 : 0 ≤ (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
      (((closureOne M₀ b b' x₁ x₂).atoms.card + 1 : ℝ) * L ^ (-(η / 2 / 16))) := by
    have := hLp; positivity
  have hε2 : 0 ≤ (110 * ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) ^ 2 *
      (((closureOne M₀ b b' x₁ x₂).atoms.card + 1 : ℝ) * L ^ (-(min γ (1 - γ) + η / 2 / 16))) := by
    have := hLp; positivity
  have hs := split_arith_sharp (d := d) (m := m) (L := L) (γ := γ) (δ := δ) (ηs := η / 2)
    (a := ((closureOne M₀ b b' x₁ x₂).atoms.card : ℝ)) hδ0 hLe (Nat.cast_nonneg _) hsz hbig
  have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hA1
  refine (countAFree_or_le M₀ L γ δ C1 P Adm (fun κ => Adm κ ∧ Cls1One T Q {b, b'} L γ η κ)
    (fun κ => Adm κ ∧ ¬ Cls1One T Q {b, b'} L γ η κ) (fun κ hκ => by
      by_cases h : Cls1One T Q {b, b'} L γ η κ
      · exact Or.inl ⟨hκ, h⟩
      · exact Or.inr ⟨hκ, h⟩)).trans ?_
  calc _ ≤ _ := add_le_add hcls1 hcls2
    _ ≤ _ := add_le_add (le_mul_of_one_le_left bot_le h1) (le_mul_of_one_le_left bot_le h1)
    _ ≤ ENNReal.ofReal (L ^ (-(η / 2 / 32))) := ofReal_sum_bound _ _ _ _ _ hA0 hC0 hε1 hε2 hs
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))

end WaveTurbulence.GammaLow.FinalCount
