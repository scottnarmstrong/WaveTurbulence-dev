/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpDW
import Mathlib.Tactic

/-! # Operation (d) at the level of decorations: the normalized count (finalcount-g8, F6-1)

`opDW`: `𝔄(𝕄; Adm) ≤ 21125 (log L)^{14} · sup_{g ∈ [0,4]} 𝔄(post; postAdmOff Adm W g)` for a chain `Y` of exempt atoms
(`≤ 3` atoms, `in = out = 1`) with two exits; `W` is a condition on the decoration of `𝕄` that is pulled back to the post
decorations (they remain images of `Adm`-decorations that satisfy `W g`). Clone of `opDAt` with the post
admissibility `postAdmOff`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
open WaveTurbulence.MoleProp4.TwoExit

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The supremum of the normalized counts of the post problems for the multiplier `g`. -/
noncomputable def _root_.WaveTurbulence.MoleProp4.TwoExit.afreeSupPost {N : Molecule V D} (T : TwoExit N) {d : ℕ}
    (Bs : Finset V) (Adm : (D → (Fin d → ℤ)) → Prop) (W : ℤ → (D → (Fin d → ℤ)) → Prop)
    (L γ δ η' C1 : ℝ) (g : ℤ) : ℝ≥0∞ :=
  ⨆ (P' : Finset V → ℝ) (_ : ∀ S ∈ MoleProp.ladderCells T.post, 0 ≤ P' S),
    MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdmOff Bs Adm W L γ η' P' g) P'

/-- **Operation (d), decoration level** (DH23 L1865–L1867). -/
theorem opDW {d : ℕ} {L γ δ η C1 : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hδ : δ ∈ Set.Ioc (0 : ℝ) 1) (hC1 : 1 ≤ C1)
    (M : Molecule V D) (T : TwoExit M) (hcap : ∀ a ∈ M.atoms, M.outdeg a ≤ 2 ∧ M.indeg a ≤ 2)
    (hloop : ∀ z, M.atom z ≠ M.atom (M.mate z)) (hMconn : ∀ a ∈ M.atoms, ∀ b ∈ M.atoms, M.SameComponent a b)
    (Bs : Finset V) (hY3 : T.Y.card ≤ 3) (hch : ∀ b ∈ T.Y, M.outdeg b = 1 ∧ M.indeg b = 1)
    (hYconn : ∀ a ∈ T.Y, ∀ b ∈ T.Y, (piece M T.Y).SameComponent a b)
    (hpost : ∀ a ∈ T.post.atoms, ∀ b ∈ T.post.atoms, T.post.SameComponent a b)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, GoodCell T.post S)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S)
    (Adm : (D → (Fin d → ℤ)) → Prop) (hAdm : ∀ κ, Adm κ → lgAdmOff M Bs L γ η P κ)
    (W : ℤ → (D → (Fin d → ℤ)) → Prop)
    (hW : ∀ κ, Adm κ → (∀ x, κ (M.mate x) = κ x) → ∃ g ∈ Icc (0 : ℤ) 4, T.PostGoodOff Bs L γ (η / 2) κ g ∧ W g κ) :
    MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤
      ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) *
        ⨆ g ∈ Icc (0 : ℤ) 4, T.afreeSupPost Bs Adm W L γ δ (η / 2) C1 g := by
  classical
  have hLp : 0 < L := by linarith
  have hδ0 : 0 < δ := hδ.1
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  have hYM := T.sub
  set Y := T.Y with hYdef
  have hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => by
    have := hcap a ha; have := Mole.outdeg_add_indeg M a; omega
  have hY1 : 1 ≤ Y.card := card_pos.mpr ⟨M.atom T.x, T.atom_x⟩
  have hopen' : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S := fun S hS _ => hopen S hS
  have hcount := T.countEFree_le_chainW hloop hdeg hch hYconn Bs hopen' hL hδ0 P Adm hAdm W hW
  -- ranks
  have hF1 : M.numComponents = 1 := Mole.numComponents_eq_one M ⟨M.atom T.x, M.atom_mem T.x⟩ hMconn
  have hFp : (piece M Y).numComponents = 1 := Mole.numComponents_eq_one (piece M Y)
    (by rw [piece_atoms hYM]; exact ⟨M.atom T.x, T.atom_x⟩) (by rw [piece_atoms hYM]; exact hYconn)
  have hFq : T.post.numComponents = 1 :=
    Mole.numComponents_eq_one T.post ⟨T.c, by rw [T.post_atoms]; exact T.c_mem⟩ hpost
  have hrkp : (piece M Y).circuitRank = 0 := by
    unfold Molecule.circuitRank
    rw [chain_piece_card M hYM hch hY1 T.cross T.ne, piece_atoms hYM, hFp]
    push_cast; ring
  have hrk : M.circuitRank = T.post.circuitRank := by
    have := T.circuitRank_identity
    rw [hrkp, hF1, hFq, hFp] at this
    push_cast at this; linarith
  -- cells
  have hcellsP : MoleProp.ladderCells (piece M Y) = ∅ := by
    rw [T.ladderCells_piece_eq]
    refine eq_empty_of_forall_notMem fun S hS => ?_
    obtain ⟨hS1, hS2⟩ := mem_filter.mp hS
    refine no_cell_of_deg_le_two M (mem_filter.mp hS1).2 fun a ha => ?_
    have := Mole.outdeg_add_indeg M a; have := hch a (hS2 ha); omega
  have hcpP : ∀ P'' : Finset V → ℝ, MoleProp.cellProduct (piece M Y) L γ δ P'' = 1 := fun P'' => by
    unfold MoleProp.cellProduct; rw [hcellsP]; simp
  have hbpos : 0 < C1⁻¹ * δ ^ (1 / 2 : ℝ) := by
    have : 0 < C1 := by linarith
    positivity
  have hnorm : ∀ P' ∈ T.scaleFamily L P, MoleProp.freeNormalization M (d := d) L γ δ C1 P ≤
      MoleProp.freeNormalization T.post (d := d) L γ δ C1 P' * (Real.log L ^ 2) ^ 6 := by
    intro P' hP'
    have hP'nn := T.scaleFamily_nonneg hP' (fun S hS hc => hP S (by
      have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
      exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M hcell.1), hcell.1⟩))
    have hagree := T.scaleFamily_agree hP'
    have hcells := T.cellProduct_le (γ := γ) hloop hdeg hLp.le hδ0.le hlog P P' hP hP'nn hagree
    have hcp : MoleProp.cellProduct M L γ δ P ≤ MoleProp.cellProduct T.post L γ δ P' * (Real.log L ^ 2) ^ 6 := by
      have h := hcells
      change MoleProp.cellProduct M L γ δ P ≤ MoleProp.cellProduct (piece M T.Y) L γ δ P *
        MoleProp.cellProduct T.post L γ δ P' * (Real.log L ^ 2) ^ 6 at h
      rwa [hcpP, one_mul] at h
    unfold MoleProp.freeNormalization
    rw [hrk]
    have hX : 0 ≤ L ^ (-((d : ℝ) - γ) * (T.post.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ T.post.circuitRank := by
      positivity
    calc _ ≤ L ^ (-((d : ℝ) - γ) * (T.post.circuitRank : ℝ)) * (C1⁻¹ * δ ^ (1 / 2 : ℝ)) ^ T.post.circuitRank *
          (MoleProp.cellProduct T.post L γ δ P' * (Real.log L ^ 2) ^ 6) := mul_le_mul_of_nonneg_left hcp hX
      _ = _ := by ring
  -- the constant
  have hconst : ((5 * T.windowK ^ 2 * (T.scaleFamily L P).card : ℕ) : ℝ) * (Real.log L ^ 2) ^ 6 ≤
      21125 * Real.log L ^ (14 : ℝ) := by
    have hS5 := card_scaleSet_le_log hlog
    have hfam : ((T.scaleFamily L P).card : ℝ) ≤ ((scaleSet L).card : ℝ) ^ 2 := by
      exact_mod_cast T.card_scaleFamily_le hloop hdeg L P
    have hS0 : (0 : ℝ) ≤ (scaleSet L).card := Nat.cast_nonneg _
    have hl0 : 0 ≤ Real.log L := by linarith
    have hK : (T.windowK : ℝ) ≤ 13 := by
      have : T.windowK ≤ 13 := by unfold TwoExit.windowK; change 1 + 4 * Y.card ≤ 13; omega
      exact_mod_cast this
    have h14 : Real.log L ^ (14 : ℝ) = Real.log L ^ 14 := by
      rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h14]
    push_cast
    have h1 : ((scaleSet L).card : ℝ) ^ 2 ≤ (5 * Real.log L) ^ 2 := pow_le_pow_left₀ hS0 hS5 2
    have h2 : (T.windowK : ℝ) ^ 2 ≤ 13 ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hK 2
    calc 5 * (T.windowK : ℝ) ^ 2 * ((T.scaleFamily L P).card : ℝ) * (Real.log L ^ 2) ^ 6
        ≤ 5 * 13 ^ 2 * (5 * Real.log L) ^ 2 * (Real.log L ^ 2) ^ 6 := by
          gcongr
          exact hfam.trans h1
      _ = 21125 * Real.log L ^ 14 := by ring
  -- assemble
  set fam := T.scaleFamily L P with hfam
  set G := ⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ fam,
    MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g) with hG
  rw [MoleProp.countAFree_eq_normalization]
  have hstep : (G : ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P) ≤
      ENNReal.ofReal ((Real.log L ^ 2) ^ 6) *
        ⨆ g ∈ Icc (0 : ℤ) 4, T.afreeSupPost Bs Adm W L γ δ (η / 2) C1 g := by
    rw [hG]
    simp only [ENat.toENNReal_iSup, ENNReal.iSup_mul]
    refine iSup₂_le fun g hg => iSup₂_le fun P' hP' => ?_
    have hP'nn := T.scaleFamily_nonneg hP' (fun S hS hc => hP S (by
      have hcell := (T.isLadderCell_post_iff hc).mp (mem_filter.mp hS).2
      exact mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms M hcell.1), hcell.1⟩))
    have hnq := MoleProp.freeNormalization_pos T.post (d := d) (γ := γ) hLp hδ0 (by linarith : (0 : ℝ) < C1) hlog0 P'
      hP'nn
    calc (MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g) : ℝ≥0∞) *
          ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P)
        ≤ (MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g) : ℝ≥0∞) *
          ENNReal.ofReal (MoleProp.freeNormalization T.post (d := d) L γ δ C1 P' * (Real.log L ^ 2) ^ 6) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hnorm P' hP'))
      _ = ENNReal.ofReal ((Real.log L ^ 2) ^ 6) *
          MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g) P' := by
          rw [MoleProp.countAFree_eq_normalization, ENNReal.ofReal_mul hnq.le]; ring
      _ ≤ _ := by
          refine mul_le_mul' le_rfl ?_
          exact le_iSup₂_of_le (f := fun g' (_ : g' ∈ Icc (0 : ℤ) 4) =>
            T.afreeSupPost Bs Adm W L γ δ (η / 2) C1 g') g hg
            (le_iSup₂_of_le (f := fun P'' (_ : ∀ S ∈ MoleProp.ladderCells T.post, 0 ≤ P'' S) =>
              MoleProp.countAFree T.post L γ δ C1 (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P'' g) P'')
              P' hP'nn le_rfl)
  have hcount' : (MoleProp.countEFree M L γ δ (0 : Mom d) Adm : ℝ≥0∞) ≤
      ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) * (G : ℝ≥0∞) := by
    have h := ENat.toENNReal_mono hcount
    have e : (((5 * (T.windowK : ℕ∞) ^ 2 * (fam.card : ℕ∞) : ℕ∞)) : ℝ≥0∞) =
        ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) := by
      have : (5 * (T.windowK : ℕ∞) ^ 2 * (fam.card : ℕ∞) : ℕ∞) = ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℕ∞) := by
        push_cast; rfl
      rw [this, ENat.toENNReal_coe]
    rw [ENat.toENNReal_mul, e] at h
    exact h
  calc (MoleProp.countEFree M L γ δ (0 : Mom d) Adm : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P)
      ≤ ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) * (G : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P) := mul_le_mul' hcount' le_rfl
    _ = ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) * ((G : ℝ≥0∞) *
        ENNReal.ofReal (MoleProp.freeNormalization M (d := d) L γ δ C1 P)) := by ring
    _ ≤ ((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ≥0∞) * (ENNReal.ofReal ((Real.log L ^ 2) ^ 6) *
        ⨆ g ∈ Icc (0 : ℤ) 4, T.afreeSupPost Bs Adm W L γ δ (η / 2) C1 g) :=
        mul_le_mul' le_rfl hstep
    _ = ENNReal.ofReal (((5 * T.windowK ^ 2 * fam.card : ℕ) : ℝ) * (Real.log L ^ 2) ^ 6) *
        ⨆ g ∈ Icc (0 : ℤ) 4, T.afreeSupPost Bs Adm W L γ δ (η / 2) C1 g := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]; ring
    _ ≤ ENNReal.ofReal (21125 * Real.log L ^ (14 : ℝ)) *
        ⨆ g ∈ Icc (0 : ℤ) 4, T.afreeSupPost Bs Adm W L γ δ (η / 2) C1 g :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hconst) le_rfl


end WaveTurbulence.FinalCountG8
