/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.PinchSplit
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.OneExitBound
import Mathlib.Tactic

/-! # Removing a pinched set (DH23 ylem2, (Y1) case 3, L1952)

`𝔄(N) ≤ 𝔄(N ∖ Y)`: the removed labels are decorations of the contracted molecule, with charge `−∑_Y c` and energy known
up to `|Y| τ` at the new atom; DH23 Prop 10.1 bounds them with constant `C₁/2`, and `|Y| (1/2)^{χ(aux)} ≤ 1`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace Pinch
variable {N : Molecule V D} (T : Pinch N)

/-- The charges of the contracted molecule. -/
noncomputable def auxCharge {d : ℕ} (c : V → Mom d) : Option V → Mom d := fun o =>
  match o with
  | some v => c v
  | none => -∑ v ∈ T.Y, c v

/-- The energy centers of the contracted molecule (window `j` at the new atom). -/
noncomputable def auxEnergy (β : V → ℝ) (τ : ℝ) (j : ℕ) : Option V → ℝ := fun o =>
  match o with
  | some v => β v
  | none => -∑ v ∈ T.Y, β v - T.Y.card * τ + (2 * j + 1) * τ

theorem kvec_deleted {d : ℕ} (L : ℝ) (κ : D → (Fin d → ℤ)) (z : MoleProp.DeletedDart N T.Y) :
    Molecule.kvec L 0 (MoleProp.deletedLabels N T.Y κ) z = Molecule.kvec L 0 κ z.val := rfl

theorem dartSign_mate_x : N.dartSign (N.mate T.x) = -1 := by
  unfold Molecule.dartSign; rw [N.out_mate, T.out_x]; rfl

theorem dartSign_mate_y : N.dartSign (N.mate T.y) = 1 := by
  unfold Molecule.dartSign; rw [N.out_mate, T.out_y]; rfl

/-- **The removed labels are decorations of the contracted molecule.** -/
theorem deleted_mem {d : ℕ} {L γ δ η : ℝ} (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) {c : V → Mom d}
    {β : V → ℝ} {k0 : D → Mom d} {P : Finset V → ℝ} {κ : D → (Fin d → ℤ)} (hdec : N.IsDecoration L 0 c κ)
    (hres : N.IsRestricted L γ δ 0 β k0 κ) (hadm : lgAdm N L γ η P κ) (hτ : 0 < δ⁻¹ * L ^ (-2 * γ)) :
    ∃ j ∈ range T.Y.card, T.aux.IsDecoration L 0 (T.auxCharge c) (MoleProp.deletedLabels N T.Y κ) ∧
      T.aux.IsRestricted L γ δ 0 (T.auxEnergy β (δ⁻¹ * L ^ (-2 * γ)) j) (fun z => k0 z.val)
        (MoleProp.deletedLabels N T.Y κ) ∧ lgAdm T.aux L γ η (auxScale P) (MoleProp.deletedLabels N T.Y κ) := by
  set τ := δ⁻¹ * L ^ (-2 * γ)
  have hK : 1 ≤ T.Y.card := card_pos.mpr ⟨_, T.atom_x⟩
  have hmx : Molecule.kvec L 0 κ (N.mate T.x) = Molecule.kvec L 0 κ T.x := by simp [Molecule.kvec, hdec.1]
  have hmy : Molecule.kvec L 0 κ (N.mate T.y) = Molecule.kvec L 0 κ T.y := by simp [Molecule.kvec, hdec.1]
  -- the boundary identities
  have hbc : ∑ v ∈ T.Y, c v = Molecule.kvec L 0 κ T.x - Molecule.kvec L 0 κ T.y := by
    rw [sum_charges_eq_cross hdec T.sub, T.cross, sum_pair T.ne]
    unfold Molecule.dartSign; rw [T.out_x, T.out_y]
    simp only [ite_true, Bool.false_eq_true, ite_false, one_smul, neg_one_smul]; abel
  have hbe : ∑ v ∈ T.Y, N.Gamma L 0 κ v = ‖Molecule.kvec L 0 κ T.x‖ ^ 2 - ‖Molecule.kvec L 0 κ T.y‖ ^ 2 := by
    rw [sum_gamma_eq_cross N L 0 hdec.1 T.Y, T.cross, sum_pair T.ne]
    unfold Molecule.dartSign; rw [T.out_x, T.out_y]
    simp only [ite_true, Bool.false_eq_true, ite_false, one_mul, neg_one_mul]; ring
  -- the energy at the new atom
  have hGnone : T.aux.Gamma L 0 (MoleProp.deletedLabels N T.Y κ) none = -∑ v ∈ T.Y, N.Gamma L 0 κ v := by
    rw [hbe]
    unfold Molecule.Gamma
    rw [show (∑ z ∈ T.aux.dartsAt none, T.aux.dartSign z *
        ‖Molecule.kvec L 0 (MoleProp.deletedLabels N T.Y κ) z‖ ^ 2) =
      ∑ z ∈ T.aux.dartsAt none, (fun z => N.dartSign z * ‖Molecule.kvec L 0 κ z‖ ^ 2) z.val from rfl,
      T.aux_sum_none (fun z => N.dartSign z * ‖Molecule.kvec L 0 κ z‖ ^ 2), T.dartSign_mate_x,
      T.dartSign_mate_y, hmx, hmy]
    ring
  have hwin : |T.aux.Gamma L 0 (MoleProp.deletedLabels N T.Y κ) none - (-∑ v ∈ T.Y, β v)| ≤ T.Y.card * τ := by
    rw [hGnone, show -∑ v ∈ T.Y, N.Gamma L 0 κ v - -∑ v ∈ T.Y, β v =
      -(∑ v ∈ T.Y, N.Gamma L 0 κ v - ∑ v ∈ T.Y, β v) by ring, abs_neg, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    rw [← nsmul_eq_mul]
    exact sum_le_card_nsmul _ _ _ fun v hv => hres.1 v (T.sub hv)
  obtain ⟨j, hj, hjw⟩ := exists_window hτ hK hwin
  refine ⟨j, hj, ⟨fun z => hdec.1 z.val, fun o ho => ?_⟩, ⟨fun o ho => ?_, fun z => hres.2 z.val⟩, ?_, ?_⟩
  · -- charges
    rcases T.mem_aux_atoms.mp ho with rfl | ⟨v, hv, rfl⟩
    · change ∑ z ∈ T.aux.dartsAt none, (fun z => N.dartSign z • Molecule.kvec L 0 κ z) z.val = _
      rw [T.aux_sum_none (fun z => N.dartSign z • Molecule.kvec L 0 κ z), T.dartSign_mate_x, T.dartSign_mate_y,
        hmx, hmy]
      change _ = -∑ v ∈ T.Y, c v
      rw [hbc]; simp only [neg_one_smul, one_smul]; abel
    · change ∑ z ∈ T.aux.dartsAt (some v), (fun z => N.dartSign z • Molecule.kvec L 0 κ z) z.val = c v
      rw [T.aux_sum_some hv (fun z => N.dartSign z • Molecule.kvec L 0 κ z)]; exact hdec.2 v (T.sub hv)
  · -- energies
    rcases T.mem_aux_atoms.mp ho with rfl | ⟨v, hv, rfl⟩
    · exact hjw
    · change |∑ z ∈ T.aux.dartsAt (some v), (fun z => N.dartSign z * ‖Molecule.kvec L 0 κ z‖ ^ 2) z.val - β v| ≤ _
      rw [T.aux_sum_some hv (fun z => N.dartSign z * ‖Molecule.kvec L 0 κ z‖ ^ 2)]; exact hres.1 v (T.sub hv)
  · -- large gaps
    intro z₁ z₂ hat hout
    rw [T.kvec_deleted, T.kvec_deleted]
    by_cases h1 : N.atom z₁.val ∈ T.Y
    · have e1 := T.aux_atom_some.mpr ⟨rfl, h1⟩
      rw [e1] at hat
      have e2 := (T.aux_atom_some.mp hat.symm).1
      exact hadm.1 z₁.val z₂.val e2.symm hout
    · have e1 := T.aux_atom_none.mpr h1
      have hz1 : z₁ ∈ T.aux.dartsAt none := mem_filter.mpr ⟨mem_univ _, e1⟩
      have hz2 : z₂ ∈ T.aux.dartsAt none := mem_filter.mpr ⟨mem_univ _, hat ▸ e1⟩
      rw [T.aux_dartsAt_none] at hz1 hz2
      simp only [mem_insert, mem_singleton] at hz1 hz2
      have hw : N.atom (N.mate T.x) = N.atom (N.mate T.y) := T.same
      have hox : N.out (N.mate T.x) ≠ N.out (N.mate T.y) := by rw [N.out_mate, N.out_mate, T.out_x, T.out_y]; decide
      rcases hz1 with rfl | rfl <;> rcases hz2 with rfl | rfl
      · exact absurd rfl hout
      · exact hadm.1 _ _ hw hox
      · exact hadm.1 _ _ hw.symm hox.symm
      · exact absurd rfl hout
  · exact T.aux_cgr hloop hadm.2

/-- **Counting inequality** for a pinched removal. -/
theorem countEFree_le (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) {d : ℕ} {L γ δ η : ℝ} (hL : 0 < L)
    (hδ : 0 < δ) (P : Finset V → ℝ) :
    MoleProp.countEFree N L γ δ (0 : Mom d) (lgAdm N L γ η P) ≤
      (T.Y.card : ℕ∞) * MoleProp.countEFree T.aux L γ δ (0 : Mom d) (lgAdm T.aux L γ η (auxScale P)) *
        MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N T.Y (lgAdm N L γ η P)) := by
  classical
  have hτ : 0 < δ⁻¹ * L ^ (-2 * γ) := by positivity
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ lgAdm N L γ η P κ}
  have hAfin : A.Finite := (Mole.finite_restricted N hL γ δ 0 β k0).subset fun _ h => h.2.1
  have hmain := MoleProp.encard_le_deletedImage_mul_post N T.Y hL γ δ 0 (lgAdm N L γ η P) c β k0 hk0
  refine hmain.trans (mul_le_mul' ?_ le_rfl)
  let E : ℕ → Set (MoleProp.DeletedDart N T.Y → (Fin d → ℤ)) := fun j =>
    {q | T.aux.IsDecoration L 0 (T.auxCharge c) q ∧
      T.aux.IsRestricted L γ δ 0 (T.auxEnergy β (δ⁻¹ * L ^ (-2 * γ)) j) (fun z => k0 z.val) q ∧
      lgAdm T.aux L γ η (auxScale P) q}
  have hsub : MoleProp.deletedLabels N T.Y '' A ⊆ ⋃ j ∈ range T.Y.card, E j := by
    rintro _ ⟨κ, hκ, rfl⟩
    obtain ⟨j, hj, h1, h2, h3⟩ := T.deleted_mem hloop hκ.1 hκ.2.1 hκ.2.2 hτ
    exact Set.mem_biUnion hj ⟨h1, h2, h3⟩
  have hfin : (MoleProp.deletedLabels N T.Y '' A).Finite := hAfin.image _
  have hE : ∀ j, (E j).encard ≤ MoleProp.countEFree T.aux L γ δ (0 : Mom d) (lgAdm T.aux L γ η (auxScale P)) :=
    fun j => MoleProp.encard_le_countEFree T.aux L γ δ 0 _ _ _ (fun z => k0 z.val) (fun z => hk0 z.val)
  calc ((MoleProp.deletedLabels N T.Y '' A).ncard : ℕ∞) = (MoleProp.deletedLabels N T.Y '' A).encard :=
        hfin.cast_ncard_eq
    _ ≤ (⋃ j ∈ range T.Y.card, E j).encard := Set.encard_mono hsub
    _ ≤ ∑ j ∈ range T.Y.card, (E j).encard := encard_biUnion_le _ _
    _ ≤ ∑ _j ∈ range T.Y.card, MoleProp.countEFree T.aux L γ δ (0 : Mom d) (lgAdm T.aux L γ η (auxScale P)) :=
        sum_le_sum fun j _ => hE j
    _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]

end Pinch

/-- If no cell straddles `Y`, the ladder factors of `N` split into those of the piece and of the rest. -/
theorem cellProduct_split {N : Molecule V D} {Y : Finset V}
    (hsplit : ∀ S, MoleProp.IsLadderCell N S → S ⊆ Y ∨ Disjoint S Y) (hY : Y ⊆ N.atoms) (L γ δ : ℝ)
    (P : Finset V → ℝ) :
    MoleProp.cellProduct N L γ δ P =
      MoleProp.cellProduct (piece N Y) L γ δ P * MoleProp.cellProduct (Degen.eraseAtoms N Y) L γ δ P := by
  classical
  unfold MoleProp.cellProduct
  rw [← prod_filter_mul_prod_filter_not (MoleProp.ladderCells N) (fun S => S ⊆ Y)]
  have h1 : MoleProp.ladderCells (piece N Y) = (MoleProp.ladderCells N).filter (fun S => S ⊆ Y) := by
    ext S
    simp only [MoleProp.ladderCells, mem_filter, mem_powerset, isLadderCell_piece_iff, piece_atoms hY]
    constructor
    · rintro ⟨hSY, hc, _⟩; exact ⟨⟨hSY.trans hY, hc⟩, hSY⟩
    · rintro ⟨⟨_, hc⟩, hSY⟩; exact ⟨hSY, hc, hSY⟩
  have h2 : MoleProp.ladderCells (Degen.eraseAtoms N Y) = (MoleProp.ladderCells N).filter (fun S => ¬ S ⊆ Y) := by
    ext S
    simp only [MoleProp.ladderCells, mem_filter, mem_powerset, MoleProp.isLadderCell_erase_iff]
    constructor
    · rintro ⟨hSA, hc, hdis⟩
      refine ⟨⟨hSA.trans sdiff_subset, hc⟩, fun hsub => ?_⟩
      obtain ⟨u, v, _, rfl⟩ := hc
      have hmem : u 0 ∈ Molecule.ladderAtoms u v := mem_union_left _ (mem_image_of_mem _ (mem_univ 0))
      exact disjoint_left.mp hdis hmem (hsub hmem)
    · rintro ⟨⟨hSA, hc⟩, hnsub⟩
      have hdis := (hsplit S hc).resolve_left hnsub
      exact ⟨fun a ha => mem_sdiff.mpr ⟨hSA ha, disjoint_left.mp hdis ha⟩, hc, hdis⟩
  rw [h1, h2]

end WaveTurbulence.MoleProp4
