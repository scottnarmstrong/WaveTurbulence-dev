/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.CutTwo
import Mathlib.Tactic

/-! # Counting for a set attached by two bonds at one atom (DH23 L1784, L1963), directly on the induced piece

`𝔈(N) ≤ |Y| · 𝔈(N[Y ∪ {w}]) · 𝔈(N ∖ Y)`: the labels on the darts touching `Y` are the labels of the piece
`N[Y ∪ {w}]` (`w` of degree two there: its two bonds are the exits). Its charge at `w` is `-∑_Y c_v` and
its energy is `-∑_Y Γ_v`, which lies in one of `|Y|` windows of length `2δ⁻¹L^{-2γ}`. Unlike MOLEPROP4-T's `Pinch`
(contracted molecule on `Option V`), the post molecule is an induced piece on `V`, and no directions are needed.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

section Sums
variable {N : Molecule V D} {Y : Finset V} {w : V}

theorem deleted_in_piece (hY : Y ⊆ N.atoms) (hw : w ∉ Y) (hX : ∀ x ∈ crossDarts N Y, N.atom (N.mate x) = w)
    (z : MoleProp.DeletedDart N Y) :
    N.atom z.val ∈ insert w Y ∧ N.atom (N.mate z.val) ∈ insert w Y := by
  have hz := z.property
  simp only [not_and_or, not_not] at hz
  rcases hz with h | h
  · refine ⟨mem_insert_of_mem h, ?_⟩
    by_cases h2 : N.atom (N.mate z.val) ∈ Y
    · exact mem_insert_of_mem h2
    · rw [hX z.val (mem_crossDarts.mpr ⟨h, h2⟩)]; exact mem_insert_self _ _
  · refine ⟨?_, mem_insert_of_mem h⟩
    by_cases h2 : N.atom z.val ∈ Y
    · exact mem_insert_of_mem h2
    · have := hX (N.mate z.val) (mem_crossDarts.mpr ⟨h, by rw [N.mate_mate]; exact h2⟩)
      rw [N.mate_mate] at this
      rw [this]; exact mem_insert_self _ _

/-- The dart of the piece for a dart with both ends in `Y ∪ {w}`. -/
def pieceDart' (N : Molecule V D) (W : Finset V) (x : D) (hx : N.atom x ∈ W ∧ N.atom (N.mate x) ∈ W) :
    Degen.RetainedDart N (N.atoms \ W) :=
  ⟨x, fun h => (mem_sdiff.mp h).2 hx.1, fun h => (mem_sdiff.mp h).2 hx.2⟩

theorem sum_piece_Y (hY : Y ⊆ N.atoms) (hw : w ∉ Y) (hX : ∀ x ∈ crossDarts N Y, N.atom (N.mate x) = w)
    {v : V} (hv : v ∈ Y) {E : Type*} [AddCommMonoid E] (f : D → E) :
    ∑ z ∈ (piece N (insert w Y)).dartsAt v, f z.val = ∑ z ∈ N.dartsAt v, f z := by
  classical
  refine sum_bij (fun z _ => z.val) ?_ ?_ ?_ ?_
  · intro z hz
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2⟩
  · intro a _ b _ h; exact Subtype.ext h
  · intro z hz
    have hzv : N.atom z = v := (mem_filter.mp hz).2
    have h1 : N.atom z ∈ insert w Y := mem_insert_of_mem (hzv ▸ hv)
    have h2 : N.atom (N.mate z) ∈ insert w Y := by
      by_cases h : N.atom (N.mate z) ∈ Y
      · exact mem_insert_of_mem h
      · rw [hX z (mem_crossDarts.mpr ⟨hzv ▸ hv, h⟩)]; exact mem_insert_self _ _
    exact ⟨pieceDart' N (insert w Y) z ⟨h1, h2⟩, mem_filter.mpr ⟨mem_univ _, hzv⟩, rfl⟩
  · intro z _; rfl

theorem sum_piece_w (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hY : Y ⊆ N.atoms) (hw : w ∉ Y)
    (hX : ∀ x ∈ crossDarts N Y, N.atom (N.mate x) = w) {E : Type*} [AddCommMonoid E] (f : D → E) :
    ∑ z ∈ (piece N (insert w Y)).dartsAt w, f z.val = ∑ x ∈ crossDarts N Y, f (N.mate x) := by
  classical
  symm
  refine sum_bij (fun x hx => pieceDart' N (insert w Y) (N.mate x) ⟨?_, ?_⟩) ?_ ?_ ?_ ?_
  · rw [hX x hx]; exact mem_insert_self _ _
  · rw [N.mate_mate]; exact mem_insert_of_mem (mem_crossDarts.mp hx).1
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _, hX x hx⟩
  · intro a _ b _ h
    have := congrArg Subtype.val h
    have h2 : N.mate a = N.mate b := by simpa [pieceDart'] using this
    simpa [N.mate_mate] using congrArg N.mate h2
  · intro z hz
    have hzw : N.atom z.val = w := (mem_filter.mp hz).2
    have hz2 := z.property
    simp only [mem_sdiff, not_and, not_not] at hz2
    have hmz : N.atom (N.mate z.val) ∈ insert w Y := hz2.2 (N.atom_mem _)
    have hmY : N.atom (N.mate z.val) ∈ Y := by
      rcases mem_insert.mp hmz with h | h
      · exact absurd (hzw.trans h.symm) (hloop z.val)
      · exact h
    have hxc : N.mate z.val ∈ crossDarts N Y :=
      mem_crossDarts.mpr ⟨hmY, by rw [N.mate_mate, hzw]; exact hw⟩
    exact ⟨N.mate z.val, hxc, Subtype.ext (N.mate_mate z.val)⟩
  · intro x _; rfl

end Sums


namespace Cut2
variable {N : Molecule V D} (T : Cut2 N)

theorem hX : ∀ x ∈ crossDarts N T.Y, N.atom (N.mate x) = T.w := by
  intro x hx
  rw [T.cross] at hx
  rcases mem_insert.mp hx with rfl | hx
  · rfl
  · rw [mem_singleton.mp hx]; exact T.same.symm

/-- **Counting inequality** for a set attached by two bonds at one atom. -/
theorem countEFree_le (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) {d : ℕ} {L γ δ η : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (P : Finset V → ℝ) :
    MoleProp.countEFree N L γ δ (0 : Mom d) (lgAdm N L γ η P) ≤
      (T.Y.card : ℕ∞) *
        MoleProp.countEFree (piece N (insert T.w T.Y)) L γ δ (0 : Mom d)
          (lgAdm (piece N (insert T.w T.Y)) L γ η P) *
        MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N T.Y (lgAdm N L γ η P)) := by
  classical
  have hτ : 0 < δ⁻¹ * L ^ (-2 * γ) := by positivity
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτdef
  set W := insert T.w T.Y with hW
  have hWsub : W ⊆ N.atoms := insert_subset (by
    have := (mem_crossDarts.mp T.x_mem).2
    have h := N.atom_mem (N.mate T.x)
    exact h) T.sub
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ lgAdm N L γ η P κ}
  have hAfin : A.Finite := (Mole.finite_restricted N hL γ δ 0 β k0).subset fun _ h => h.2.1
  have hmain := MoleProp.encard_le_deletedImage_mul_post N T.Y hL γ δ 0 (lgAdm N L γ η P) c β k0 hk0
  refine hmain.trans (mul_le_mul' ?_ le_rfl)
  -- the piece
  let pr : (D → (Fin d → ℤ)) → (Degen.RetainedDart N (N.atoms \ W) → (Fin d → ℤ)) := fun κ z => κ z.val
  let Φ : (Degen.RetainedDart N (N.atoms \ W) → (Fin d → ℤ)) → (MoleProp.DeletedDart N T.Y → (Fin d → ℤ)) :=
    fun p z => p (pieceDart' N W z.val (deleted_in_piece T.sub T.w_notMem T.hX z))
  have himg : MoleProp.deletedLabels N T.Y '' A = Φ '' (pr '' A) := by
    rw [Set.image_image]; rfl
  let c1 : V → Mom d := fun v => if v = T.w then -∑ u ∈ T.Y, c u else c v
  let β1 : ℕ → V → ℝ := fun j v =>
    if v = T.w then -∑ u ∈ T.Y, β u - T.Y.card * τ + (2 * j + 1) * τ else β v
  let E : ℕ → Set (Degen.RetainedDart N (N.atoms \ W) → (Fin d → ℤ)) := fun j =>
    {q | (piece N W).IsDecoration L 0 c1 q ∧ (piece N W).IsRestricted L γ δ 0 (β1 j) (fun z => k0 z.val) q ∧
      lgAdm (piece N W) L γ η P q}
  have hK : 1 ≤ T.Y.card := card_pos.mpr ⟨_, T.atom_x⟩
  have hsub : pr '' A ⊆ ⋃ j ∈ range T.Y.card, E j := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨hdec, hres, hadm⟩ := hκ
    have hbc : ∑ v ∈ T.Y, c v = ∑ x ∈ crossDarts N T.Y, N.dartSign x • Molecule.kvec L 0 κ x :=
      sum_charges_eq_cross hdec T.sub
    have hbe : ∑ v ∈ T.Y, N.Gamma L 0 κ v = ∑ x ∈ crossDarts N T.Y, N.dartSign x * ‖Molecule.kvec L 0 κ x‖ ^ 2 :=
      sum_gamma_eq_cross N L 0 hdec.1 T.Y
    have hGw : (piece N W).Gamma L 0 (pr κ) T.w = -∑ v ∈ T.Y, N.Gamma L 0 κ v := by
      have hdef : (piece N W).Gamma L 0 (pr κ) T.w =
          ∑ z ∈ (piece N W).dartsAt T.w, N.dartSign z.val * ‖Molecule.kvec L 0 κ z.val‖ ^ 2 := rfl
      rw [hdef, sum_piece_w hloop T.sub T.w_notMem T.hX (fun z => N.dartSign z * ‖Molecule.kvec L 0 κ z‖ ^ 2), hbe,
        ← sum_neg_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [dartSign_mate]
      have : Molecule.kvec L 0 κ (N.mate x) = Molecule.kvec L 0 κ x := by simp [Molecule.kvec, hdec.1 x]
      rw [this]; ring
    have hwin : |(piece N W).Gamma L 0 (pr κ) T.w - (-∑ v ∈ T.Y, β v)| ≤ T.Y.card * τ := by
      rw [hGw, show -∑ v ∈ T.Y, N.Gamma L 0 κ v - -∑ v ∈ T.Y, β v =
        -(∑ v ∈ T.Y, N.Gamma L 0 κ v - ∑ v ∈ T.Y, β v) by ring, abs_neg, ← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      rw [← nsmul_eq_mul]
      exact sum_le_card_nsmul _ _ _ fun v hv => hres.1 v (T.sub hv)
    obtain ⟨j, hj, hjw⟩ := exists_window hτ hK hwin
    refine Set.mem_biUnion hj ⟨⟨fun z => hdec.1 z.val, fun o ho => ?_⟩, ⟨fun o ho => ?_, fun z => hres.2 z.val⟩, ?_⟩
    · rw [piece_atoms hWsub] at ho
      by_cases how : o = T.w
      · subst how
        change ∑ z ∈ (piece N W).dartsAt T.w, N.dartSign z.val • Molecule.kvec L 0 κ z.val = c1 T.w
        rw [sum_piece_w hloop T.sub T.w_notMem T.hX (fun z => N.dartSign z • Molecule.kvec L 0 κ z)]
        simp only [c1, if_true]
        rw [hbc, ← sum_neg_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [dartSign_mate]
        have : Molecule.kvec L 0 κ (N.mate x) = Molecule.kvec L 0 κ x := by simp [Molecule.kvec, hdec.1 x]
        rw [this, neg_smul]
      · have hoY : o ∈ T.Y := by
          rcases mem_insert.mp ho with h | h
          · exact absurd h how
          · exact h
        change ∑ z ∈ (piece N W).dartsAt o, N.dartSign z.val • Molecule.kvec L 0 κ z.val = c1 o
        rw [sum_piece_Y T.sub T.w_notMem T.hX hoY (fun z => N.dartSign z • Molecule.kvec L 0 κ z)]
        simp only [c1, if_neg how]
        exact hdec.2 o (T.sub hoY)
    · rw [piece_atoms hWsub] at ho
      by_cases how : o = T.w
      · subst how
        simp only [β1, if_true]
        exact hjw
      · have hoY : o ∈ T.Y := by
          rcases mem_insert.mp ho with h | h
          · exact absurd h how
          · exact h
        change |∑ z ∈ (piece N W).dartsAt o, N.dartSign z.val * ‖Molecule.kvec L 0 κ z.val‖ ^ 2 - β1 j o| ≤ _
        rw [sum_piece_Y T.sub T.w_notMem T.hX hoY (fun z => N.dartSign z * ‖Molecule.kvec L 0 κ z‖ ^ 2)]
        simp only [β1, if_neg how]
        exact hres.1 o (T.sub hoY)
    · exact ⟨MoleProp.largeGap_erase N L γ η 0 _ hadm.1, MoleProp.cellGapRestriction_erase N L 0 _ P _ hadm.2⟩
  rw [himg]
  have hprfin : (pr '' A).Finite := hAfin.image pr
  calc ((Φ '' (pr '' A)).ncard : ℕ∞) ≤ ((pr '' A).ncard : ℕ∞) := by
        exact_mod_cast Set.ncard_image_le hprfin
    _ = (pr '' A).encard := hprfin.cast_ncard_eq
    _ ≤ (⋃ j ∈ range T.Y.card, E j).encard := Set.encard_mono hsub
    _ ≤ ∑ j ∈ range T.Y.card, (E j).encard := encard_biUnion_le _ _
    _ ≤ ∑ _j ∈ range T.Y.card, MoleProp.countEFree (piece N W) L γ δ (0 : Mom d) (lgAdm (piece N W) L γ η P) :=
        sum_le_sum fun j _ => MoleProp.encard_le_countEFree (piece N W) L γ δ 0 _ _ _ (fun z => k0 z.val)
          (fun z => hk0 z.val)
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

end Cut2

end WaveTurbulence.FinalCountG8
