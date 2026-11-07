/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.EqNorm
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PolyLog
import Mathlib.Tactic

/-! # `BiBridgeEqualInput` (DH23 L1969): a bi-bridge with `k_{ℓ₁} = k_{ℓ₂}`

The post molecule `𝕄[S] + (a₁ → a₂)` is MOLEPROP4's `TwoExit.post` for `Y = atoms ∖ S`, with `x = mate x₂`,
`y = mate x₁`. With equal labels the transport is exact (`EqNorm`), and the bound has constants `K = 25`, `B = 14`
(`|scaleSet|² (log L)^{12} ≤ 25 (log L)^{14}`).

The hypothesis `hopen` of `BiBridgeEqualAt` (finding 2 of FINALCOUNT-G8) is what makes the cell scales of the post
well defined.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v
open WaveTurbulence.MoleProp4

theorem countEFree_eq_zero_of_empty {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
    (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (Adm : (D → (Fin d → ℤ)) → Prop) (h : ∀ κ, ¬ Adm κ) :
    MoleProp.countEFree M L γ δ (0 : Mom d) Adm = 0 := by
  refine nonpos_iff_eq_zero.mp ?_
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun _ => ?_
  have : {κ : D → (Fin d → ℤ) | M.IsDecoration L 0 c κ ∧ M.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ} = ∅ :=
    Set.eq_empty_iff_forall_notMem.mpr fun κ hκ => h κ hκ.2.2
  rw [this, Set.encard_empty]

theorem bibridgeEqualAt {d : ℕ} {L γ δ η C1 : ℝ} (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L) (hδ : 0 < δ) (hC1 : 0 < C1) :
    BiBridgeEqualAt.{u, v} d L γ δ η C1 25 14 := by
  intro V D _ _ _ M hcap hloop S x₁ x₂ hS hcross hne ho1 ho2 hconn hconnT hopen P hP Adm hAdm
  classical
  have hLp : 0 < L := by linarith
  by_cases hat : M.atom x₁ = M.atom x₂
  · -- the large gap at the common atom contradicts equal labels
    rw [MoleProp.countAFree_eq_normalization, countEFree_eq_zero_of_empty M L γ δ Adm (fun κ hκ => ?_)]
    · simp
    · obtain ⟨⟨hLG, _⟩, heq⟩ := hAdm κ hκ
      have h := hLG x₁ x₂ hat (by rw [ho1, ho2]; decide)
      rw [show Molecule.kvec L 0 κ x₁ = Molecule.kvec L 0 κ x₂ by simp [Molecule.kvec, heq], sub_self, norm_zero] at h
      exact absurd h (not_le.mpr (Real.rpow_pos_of_pos hLp _))
  have hx1 : x₁ ∈ crossDarts M S := by rw [hcross]; exact mem_insert_self _ _
  have hx2 : x₂ ∈ crossDarts M S := by rw [hcross]; exact mem_insert_of_mem (mem_singleton_self _)
  have hcrossY : crossDarts M (M.atoms \ S) = {M.mate x₂, M.mate x₁} := by
    ext z
    simp only [mem_crossDarts, mem_sdiff, mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩
      have hm : M.mate z ∈ crossDarts M S := mem_crossDarts.mpr ⟨by_contra fun h => h2 ⟨M.atom_mem _, h⟩ |>.elim, by
        rw [M.mate_mate]; exact h1⟩
      rw [hcross] at hm
      rcases mem_insert.mp hm with h | h
      · right; rw [← h, M.mate_mate]
      · left; rw [← mem_singleton.mp h, M.mate_mate]
    · rintro (rfl | rfl)
      · have := mem_crossDarts.mp hx2
        exact ⟨⟨M.atom_mem _, this.2⟩, fun h => h.2 (by rw [M.mate_mate]; exact this.1)⟩
      · have := mem_crossDarts.mp hx1
        exact ⟨⟨M.atom_mem _, this.2⟩, fun h => h.2 (by rw [M.mate_mate]; exact this.1)⟩
  let T : TwoExit M := ⟨M.atoms \ S, sdiff_subset, M.mate x₂, M.mate x₁, hcrossY,
    fun h => hne (by simpa [M.mate_mate] using (congrArg M.mate h).symm),
    by rw [M.mate_mate, M.mate_mate]; exact fun h => hat h.symm,
    by rw [M.out_mate, ho2]; rfl, by rw [M.out_mate, ho1]; rfl⟩
  have hd : T.d = M.atom x₁ := by change M.atom (M.mate (M.mate x₁)) = _; rw [M.mate_mate]
  have hc : T.c = M.atom x₂ := by change M.atom (M.mate (M.mate x₂)) = _; rw [M.mate_mate]
  have hpost : T.post = Mole.addBond (piece M S) (M.atom x₁) (M.atom x₂) := by
    change Mole.addBond (piece M S) T.d T.c = _
    rw [hd, hc]
  have hdeg : ∀ a ∈ M.atoms, M.deg a ≤ 4 := fun a ha => by
    have h := hcap a ha
    have hsum := Mole.outdeg_add_indeg M a
    omega
  have hopen' : ∀ S' ∈ MoleProp.ladderCells T.post, T.c ∈ S' → GoodCell T.post S' := by
    rw [hpost]; exact fun S' h _ => hopen S' h
  have hmain := EqPost.countAFree_le_eq T hloop hdeg hopen' hconn hconnT (L := L) (γ := γ) (δ := δ) (η := η) (C1 := C1) hL hlog hδ hC1
    P hP Adm (fun κ h => (hAdm κ h).1) (fun κ h hb => by
      have := (hAdm κ h).2
      change κ (M.mate x₂) = κ (M.mate x₁)
      rw [hb, hb]; exact this.symm)
  rw [hpost] at hmain
  refine hmain.trans ?_
  have hS5 := card_scaleSet_le_log hlog
  have hS0 : (0 : ℝ) ≤ (scaleSet L).card := Nat.cast_nonneg _
  have hl0 : 0 ≤ Real.log L := by linarith
  have hK : ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 ≤ 25 * Real.log L ^ (14 : ℝ) := by
    have h1 : ((scaleSet L).card : ℝ) ^ 2 ≤ (5 * Real.log L) ^ 2 := pow_le_pow_left₀ hS0 hS5 2
    have h2 : Real.log L ^ (14 : ℝ) = Real.log L ^ 14 := by
      rw [show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h2]
    calc ((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6 ≤ (5 * Real.log L) ^ 2 * (Real.log L ^ 2) ^ 6 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 25 * Real.log L ^ 14 := by ring
  calc ENNReal.ofReal (((scaleSet L).card : ℝ) ^ 2 * (Real.log L ^ 2) ^ 6) *
        AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1 * AFreeSup (Mole.addBond (piece M S) (M.atom x₁) (M.atom x₂)) d L γ δ η C1
      ≤ ENNReal.ofReal (25 * Real.log L ^ (14 : ℝ)) *
        AFreeSup (piece M (M.atoms \ S)) d L γ δ η C1 * AFreeSup (Mole.addBond (piece M S) (M.atom x₁) (M.atom x₂)) d L γ δ η C1 :=
        mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal hK) le_rfl) le_rfl
    _ = _ := by rw [mul_right_comm]

/-- **`BiBridgeEqualInput`** (DH23 L1969), with the good-cell hypothesis. -/
theorem bibridgeEqualInput (d : ℕ) (γ η : ℝ) : BiBridgeEqualInput.{u, v} d γ η := by
  refine ⟨1, le_rfl, fun C1 hC1 δ hδ => ⟨25, 14, Real.exp 1, fun L hL => ?_⟩⟩
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hL
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hL
  exact @bibridgeEqualAt.{u, v} d L γ δ η C1 hL1 hlog hδ.1 (by linarith [hC1])

end WaveTurbulence.FinalCountG8
