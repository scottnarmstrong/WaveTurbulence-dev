/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Algorithm.Prop102
public import WaveTurbulence.Foundations.FinalCount.Algorithm.CountAFreeBridge
public import WaveTurbulence.Foundations.FinalCount.G8R.Prop104One
public import WaveTurbulence.Foundations.FinalCount.G8R.Step0Y1c3
import Mathlib.Tactic

/-! # Bridge 1: appb `Problem` / `dh23_prop_10_2` to the relaxed count `AFree` of MOLEPROP4

APPB's `Problem.value` is `appbLinkCountA`, which equals G6's `countAFree` by `rfl`
(`appbLinkCountA_eq_countAFree`). What is left is the typing data of a `Problem`:
* admissibility with decoration mate-labels (`Adm'` below: `lgAdm` plus `κ (mate x) = κ x`, which
  every decoration satisfies, so the count is unchanged);
* the cell scales only on cells: `P' S = P S` on `ladderCells`, `0` elsewhere (`AFree` depends only on cells);
* `largeGap`, `validLinkScales` (with `c = 2`) and `noLoops` come from one admissible decoration; with
  none the count is `0`.

**Deviation (recorded).** `dh23_prop_10_2` carries the size bound `atoms ≤ (1 + log L)^m` (appb `GraphOk`);
`Prop102Input` of MOLEPROP4 has none. So the bridge gives the size-bounded inputs `Prop102Input`,
`Prop102SecondInput`, not `Prop102Input`. Also `4 * 1440061 * η ≤ 1` (appb's reading of "η small").
-/

@[expose] public section
set_option autoImplicit false
open Finset Set
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
universe u v

open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.Mole.AppbAlgorithm

section Aux
variable {V : Type*} {D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem exists_dart_of_bondsBetween (M : Molecule V D) {a b : V} (h : 0 < M.bondsBetween a b) :
    ∃ x, M.ends x = s(a, b) ∧ M.atom x = a := by
  unfold Molecule.bondsBetween at h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp h
  have hx' := (Finset.mem_filter.mp hx).2
  unfold Molecule.ends at hx'
  rcases Sym2.eq_iff.mp hx' with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact ⟨x, by simp [Molecule.ends, *], h1⟩
  · refine ⟨M.mate x, ?_, h2⟩
    simp only [Molecule.ends, M.mate_mate]
    rw [h1, h2, Sym2.eq_swap]

/-- The gap of a length-one cell exists for every labelling. -/
theorem exists_cell_gap (M : Molecule V D) {d : ℕ} (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ))
    (u v : Fin 2 → V) (h : Degen.SourceLadder (m := 1) M u v) :
    ∃ r, M.IsLadderGap L w κ u v (by decide) r := by
  have h1 := (h.2.2.2.2 0).1
  have h2 := (h.2.2.2.2 0).2.1
  obtain ⟨x, hx1, hx2⟩ := exists_dart_of_bondsBetween M (a := u 0) (b := u ⟨1, by omega⟩) (by
    have h1' : M.bondsBetween (u 0) (u ⟨1, by omega⟩) = 1 := h1
    omega)
  obtain ⟨y, hy1, hy2⟩ := exists_dart_of_bondsBetween M (a := v 0) (b := v ⟨1, by omega⟩) (by
    have h2' : M.bondsBetween (v 0) (v ⟨1, by omega⟩) = 1 := h2
    omega)
  exact ⟨_, x, y, hx1, hy1, hx2, hy2, rfl⟩

theorem countEFree_congr (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (A B : (D → (Fin d → ℤ)) → Prop)
    (h : ∀ κ, (∀ x, κ (M.mate x) = κ x) → (A κ ↔ B κ)) :
    countEFree M L γ δ w A = countEFree M L γ δ w B := by
  unfold countEFree
  refine iSup_congr fun c => iSup_congr fun β => iSup_congr fun k0 => iSup_congr fun hk => ?_
  congr 1
  ext κ
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (h κ h1.1).1 h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (h κ h1.1).2 h3⟩

theorem countEFree_eq_zero (M : Molecule V D) {d : ℕ} (L γ δ : ℝ) (w : Mom d)
    (A : (D → (Fin d → ℤ)) → Prop) (h : ∀ κ, (∀ x, κ (M.mate x) = κ x) → ¬ A κ) :
    countEFree M L γ δ w A = 0 := by
  unfold countEFree
  refine le_antisymm (iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk => ?_) bot_le
  have : {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ A κ} = ∅ := by
    ext κ
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro h1 _ h3
    exact h κ h1.1 h3
  rw [this]; simp

end Aux

section Main
variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The scale function restricted to cells. -/
noncomputable def cellScale (M : Molecule V D) (P : Finset V → ℝ) : Finset V → ℝ := by
  classical
  exact fun S => if S ∈ MoleProp.ladderCells M then P S else 0

/-- Admissibility of the `Problem`: `lgAdm` plus the mate labels of a decoration. -/
def probAdm (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (P : Finset V → ℝ) (κ : D → (Fin d → ℤ)) : Prop :=
  lgAdm M L γ η P κ ∧ ∀ x, κ (M.mate x) = κ x

theorem cellProduct_cellScale (M : Molecule V D) (L γ δ : ℝ) (P : Finset V → ℝ) :
    MoleProp.cellProduct M L γ δ (cellScale M P) = MoleProp.cellProduct M L γ δ P := by
  classical
  unfold MoleProp.cellProduct
  refine Finset.prod_congr rfl fun S hS => ?_
  simp [cellScale, hS]

/-- **Bridge:** `AFree` is the `value` of the corresponding appb count (equal by definition once the scale
function is restricted to cells and the mate labels are added to the admissibility). -/
theorem afree_eq_link (M : Molecule V D) (d : ℕ) (L γ δ η C1 : ℝ) (P : Finset V → ℝ) :
    AFree M d L γ δ η C1 P =
      WaveTurbulence.Mole.appbLinkCountA M L γ δ C1 (0 : Mom d) (probAdm M L γ η P) (cellScale M P) := by
  rw [WaveTurbulence.Mole.AppbAlgorithm.appbLinkCountA_eq_countAFree]
  unfold AFree MoleProp.countAFree
  rw [cellProduct_cellScale]
  congr 2
  refine countEFree_congr M L γ δ 0 _ _ fun κ hκ => ?_
  unfold probAdm
  exact ⟨fun h => ⟨h, hκ⟩, fun h => h.1⟩


theorem gapScale_cases {L P r : ℝ} (hL : 1 ≤ L) (h : GapScale L P r) :
    (P = 0 ∨ P ∈ Icc L⁻¹ 1) ∧ (0 < P → 2⁻¹ * P ≤ r) := by
  have hL1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · exact ⟨Or.inl h1, fun hp => by linarith⟩
  · exact ⟨Or.inr ⟨h1, h2.le⟩, fun _ => by linarith⟩
  · exact ⟨Or.inr ⟨by rw [h1]; exact hL1, h1.le⟩, fun _ => by rw [h1]; linarith⟩

theorem cellScale_ladder (M : Molecule V D) (P : Finset V → ℝ) (u v : Fin 2 → V)
    (h : Degen.SourceLadder M u v) :
    cellScale M P (Molecule.ladderAtoms u v) = P (Molecule.ladderAtoms u v) := by
  classical
  have : Molecule.ladderAtoms u v ∈ MoleProp.ladderCells M := by
    unfold MoleProp.ladderCells
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨MoleProp.isLadderCell_subset_atoms M ⟨u, v, h, rfl⟩, ⟨u, v, h, rfl⟩⟩
  simp [cellScale, this]

section Fields
variable (M : Molecule V D) {d : ℕ} {L γ η : ℝ} (hL : 1 ≤ L) (P : Finset V → ℝ)
  (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) (κ0 : D → (Fin d → ℤ)) (h0 : probAdm M L γ η P κ0)

include hL h0 in
theorem pf_noLoops : ∀ x, M.atom x ≠ M.atom (M.mate x) := by
  intro x hx
  have hLpos : 0 < L := by linarith
  have hout : M.out x ≠ M.out (M.mate x) := by rw [M.out_mate]; cases M.out x <;> simp
  have := h0.1.1 x (M.mate x) hx hout
  have hk : Molecule.kvec L (0 : Mom d) κ0 (M.mate x) = Molecule.kvec L (0 : Mom d) κ0 x := by
    rw [Molecule.kvec, Molecule.kvec, h0.2 x]
  rw [hk, sub_self, norm_zero] at this
  exact absurd this (not_le.mpr (Real.rpow_pos_of_pos hLpos _))

include hP in
theorem pf_nonneg : ∀ S, 0 ≤ cellScale M P S := by
  classical
  intro S
  by_cases hS : S ∈ MoleProp.ladderCells M
  · simp [cellScale, hS, hP S hS]
  · simp [cellScale, hS]

include hL h0 in
theorem pf_valid :
    WaveTurbulence.Mole.AppbValidLinkScales M L (0 : Mom d) (probAdm M L γ η P) 2 (cellScale M P) := by
  refine ⟨fun S hS => ?_, fun u v h κ hκ g hg hpos => ?_⟩
  · obtain ⟨u, v, h, rfl⟩ := hS
    obtain ⟨r, hr⟩ := exists_cell_gap M L 0 κ0 u v h
    have := (gapScale_cases hL (h0.1.2 u v h r hr)).1
    rw [cellScale_ladder M P u v h]
    exact this
  · have := gapScale_cases hL (hκ.1.2 u v h g hg)
    rw [cellScale_ladder M P u v h] at hpos ⊢
    have h2 := this.2 hpos
    linarith [h2]

theorem pf_largeGap : ∀ κ, probAdm M L γ η P κ →
    WaveTurbulence.Mole.AppbLargeGap M L (0 : Mom d) κ (L ^ (-γ + η)) := by
  intro κ hκ v hv x hx y hy hxy hyx
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  exact hκ.1.1 x y (hx'.trans hy'.symm) hxy

end Fields

/-- From one admissible decoration, the `Problem` of the molecule. -/
noncomputable def mkProblem (M : Molecule V D) (hM : M.IsMolecule) {d : ℕ} {L γ η : ℝ} (hL : 1 ≤ L)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) (κ0 : D → (Fin d → ℤ))
    (h0 : probAdm M L γ η P κ0) :
    Problem.{v, u} V d L 0 2 (L ^ (-γ + η)) where
  state := ofMolecule M
  admissible := probAdm M L γ η P
  scales := cellScale M P
  molecule := hM
  noLoops := pf_noLoops M hL P κ0 h0
  scales_nonneg := pf_nonneg M P hP
  validLinkScales := pf_valid M hL P κ0 h0
  mateLabels := fun _ h => h.2
  largeGap := pf_largeGap M P


/-- Common step: transfer a bound on every `Problem` to `AFree`, with count zero when no decoration. -/
theorem afree_le_of_problem (M : Molecule V D) (hM : M.IsMolecule) {d : ℕ} {L γ δ η C1 : ℝ} (hL : 1 ≤ L)
    (P : Finset V → ℝ) (hP : ∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) (B : ℝ≥0∞)
    (h : ∀ κ0 : D → (Fin d → ℤ), probAdm M L γ η P κ0 →
      WaveTurbulence.Mole.appbLinkCountA M L γ δ C1 (0 : Mom d) (probAdm M L γ η P) (cellScale M P) ≤ B) :
    AFree M d L γ δ η C1 P ≤ B := by
  by_cases hex : ∃ κ0 : D → (Fin d → ℤ), probAdm M L γ η P κ0
  · obtain ⟨κ0, h0⟩ := hex
    rw [afree_eq_link]
    exact h κ0 h0
  · push Not at hex
    have : AFree M d L γ δ η C1 P = 0 := by
      rw [afree_eq_link]
      unfold WaveTurbulence.Mole.appbLinkCountA
      rw [show WaveTurbulence.Mole.appbCountE M L γ δ (0 : Mom d) (probAdm M L γ η P) = 0 from
        countEFree_eq_zero M L γ δ 0 _ fun κ _ => hex κ]
      simp
    rw [this]; exact bot_le

end Main

/-- **Bridge theorem (first statement).** APPB's `dh23_prop_10_2` gives the size-bounded input. -/
theorem prop102InputSz (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1 - γ)) (hηs : 4 * 1440061 * η ≤ 1) :
    Prop102Input.{u, v} d γ η := by
  obtain ⟨C₀, hC₀, h⟩ := dh23_prop_10_2.{v, u} d hd γ η hγ hη hηγ hηs 2 (by norm_num)
  refine ⟨C₀, hC₀, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := h m δ hδ C1 hC1
  refine ⟨max L₀ 1, fun L hL V D _ _ _ M hM hconn hbb hE hsz P hP => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLL : L ≥ L₀ := le_trans (le_max_left _ _) hL
  refine afree_le_of_problem M hM hL1 P hP _ fun κ0 h0 => ?_
  have hne : M.atoms.Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty] at h'
    have h0' : M.bonds.card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro x _
      have := M.atom_mem x
      rw [h'] at this
      simp at this
    rw [h0', h'] at hE
    simp at hE
  have key := ((hL₀ V 0 L hLL).1 (mkProblem M hM hL1 P hP κ0 h0)
    ⟨fun a _ b _ _ => hbb a b, hsz⟩ hconn hne).1 hE
  have e : -3 * min γ (1 - γ) / 5 = -(3 / 5 * min γ (1 - γ)) := by ring
  rw [e] at key
  exact key


/-- **Bridge theorem (second statement).** -/
theorem prop102SecondInputSz (d : ℕ) (hd : 3 ≤ d) (γ η : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) (hη : 0 < η)
    (hηγ : η ≤ min γ (1 - γ)) (hηs : 4 * 1440061 * η ≤ 1) :
    Prop102SecondInput.{u, v} d γ η := by
  obtain ⟨C₀, hC₀, h⟩ := dh23_prop_10_2.{v, u} d hd γ η hγ hη hηγ hηs 2 (by norm_num)
  refine ⟨C₀, hC₀, fun m C1 hC1 δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := h m δ hδ C1 hC1
  refine ⟨max L₀ 1, fun L hL V D _ _ _ M hM hconn hbb hE hpos hsz P hP => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLL : L ≥ L₀ := le_trans (le_max_left _ _) hL
  refine afree_le_of_problem M hM hL1 P hP _ fun κ0 h0 => ?_
  have hne : M.atoms.Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty] at h'
    have h0' : M.bonds.card = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_of_forall_notMem
      intro x _
      have := M.atom_mem x
      rw [h'] at this
      simp at this
    omega
  have key := ((hL₀ V 0 L hLL).1 (mkProblem M hM hL1 P hP κ0 h0)
    ⟨fun a _ b _ _ => hbb a b, hsz⟩ hconn hne).2 hE hpos
  have e : -η / 3 = -(η / 3) := by ring
  rw [e] at key
  exact key

end WaveTurbulence.FinalCountG8
