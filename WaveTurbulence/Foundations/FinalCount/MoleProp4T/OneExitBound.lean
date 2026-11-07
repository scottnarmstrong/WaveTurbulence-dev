/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.OneExit
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitNorm
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitScaleFamily
public import WaveTurbulence.Foundations.FinalCount.MoleProp.MoleculeCount
public import WaveTurbulence.Foundations.FinalCount.MoleProp.LargeGapLoops
public import WaveTurbulence.Foundations.FinalCount.MoleProp.EmptyMolecule
import Mathlib.Tactic

/-! # Removing a set attached by one bond (DH23 ylem2, (Y1) case 2, L1952)

`𝔄(N) ≤ 𝔄(N ∖ Y)` when `Y` is attached by a single bond and `N[Y]` is connected: the removed labels are counted by
the piece (DH23 Prop 10.1), whose charges are fixed because the exit label is (boundary identity); the circuit ranks
and the ladder factors split.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace OneExit
variable {N : Molecule V D} (T : OneExit N)

omit [DecidableEq D] in
theorem kvec_x_eq {d : ℕ} {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hκ : N.IsDecoration L w c κ) : N.dartSign T.x • Molecule.kvec L w κ T.x = ∑ v ∈ T.Y, c v := by
  rw [sum_charges_eq_cross hκ T.sub, T.cross, sum_singleton]

omit [DecidableEq D] in
theorem label_x_eq {d : ℕ} {L : ℝ} (hL : L ≠ 0) {c : V → Mom d} {κ κ₀ : D → (Fin d → ℤ)}
    (hκ : N.IsDecoration L 0 c κ) (hκ₀ : N.IsDecoration L 0 c κ₀) : κ T.x = κ₀ T.x := by
  have h1 := T.kvec_x_eq hκ
  have h2 := T.kvec_x_eq hκ₀
  rw [← h2] at h1
  have hs : N.dartSign T.x ≠ 0 := by unfold Molecule.dartSign; split_ifs <;> norm_num
  have := smul_right_injective (Mom d) hs h1
  simp only [Molecule.kvec, zero_add] at this
  exact latticePoint_injective hL this

omit [DecidableEq D] in
/-- The residual data of the piece are fixed on `Y`. -/
theorem residual_eq {d : ℕ} {L : ℝ} {c : V → Mom d} {β : V → ℝ} {κ κ₀ : D → (Fin d → ℤ)}
    (hx : κ T.x = κ₀ T.x) {v : V}
    (hv : v ∈ T.Y) :
    Degen.residualMomentum N (N.atoms \ T.Y) L 0 c κ v = Degen.residualMomentum N (N.atoms \ T.Y) L 0 c κ₀ v ∧
      Degen.residualEnergy N (N.atoms \ T.Y) L 0 β κ v = Degen.residualEnergy N (N.atoms \ T.Y) L 0 β κ₀ v := by
  have hz : ∀ z ∈ Degen.removedDartsAt N (N.atoms \ T.Y) v, κ z = κ₀ z := by
    intro z hz
    simp only [Degen.removedDartsAt, Molecule.dartsAt, mem_filter, mem_univ, true_and, mem_sdiff] at hz
    have := T.eq_of_cross (z := z) (hz.1 ▸ hv) hz.2.2
    rw [this, hx]
  constructor
  · unfold Degen.residualMomentum
    congr 1
    exact sum_congr rfl fun z h => by simp only [Molecule.kvec, hz z h]
  · unfold Degen.residualEnergy
    congr 1
    exact sum_congr rfl fun z h => by simp only [Molecule.kvec, hz z h]

/-- **Counting inequality** for a one-exit removal. -/
theorem countEFree_le {d : ℕ} {L γ δ : ℝ} (hL : 0 < L) (Adm : (D → (Fin d → ℤ)) → Prop) :
    MoleProp.countEFree N L γ δ (0 : Mom d) Adm ≤
      MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) *
        MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility N T.Y Adm) := by
  classical
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ}
  have hAfin : A.Finite := (Mole.finite_restricted N hL γ δ 0 β k0).subset fun _ h => h.2.1
  have hmain := MoleProp.encard_le_deletedImage_mul_post N T.Y hL γ δ 0 Adm c β k0 hk0
  refine hmain.trans (mul_le_mul_left ?_ _)
  rcases A.eq_empty_or_nonempty with hA | ⟨κ₀, hκ₀⟩
  · show ((MoleProp.deletedLabels N T.Y '' A).ncard : ℕ∞) ≤ _
    rw [hA, Set.image_empty, Set.ncard_empty, Nat.cast_zero]
    exact bot_le
  -- the piece restriction
  let pr : (D → (Fin d → ℤ)) → (Degen.RetainedDart N (N.atoms \ T.Y) → (Fin d → ℤ)) := fun κ z => κ z.val
  let Φ : (Degen.RetainedDart N (N.atoms \ T.Y) → (Fin d → ℤ)) → (MoleProp.DeletedDart N T.Y → (Fin d → ℤ)) :=
    fun p z => if h : N.atom z.val ∈ T.Y ∧ N.atom (N.mate z.val) ∈ T.Y then p (pieceDart N T.Y z.val h)
      else κ₀ z.val
  have himg : MoleProp.deletedLabels N T.Y '' A = Φ '' (pr '' A) := by
    rw [Set.image_image]
    refine Set.image_congr fun κ hκ => ?_
    funext ⟨z, hz⟩
    simp only [Φ, pr, MoleProp.deletedLabels]
    split_ifs with h
    · rfl
    · have hx := T.label_x_eq hL.ne' hκ.1 hκ₀.1
      rcases T.dart_cases z with h' | h' | rfl | rfl
      · exact absurd h' h
      · exact absurd h' hz
      · exact hx
      · rw [hκ.1.1, hκ₀.1.1]; exact hx
  have hprfin : (pr '' A).Finite := hAfin.image pr
  have hsub : pr '' A ⊆ {p | (piece N T.Y).IsDecoration L 0 (Degen.residualMomentum N (N.atoms \ T.Y) L 0 c κ₀) p ∧
      (piece N T.Y).IsRestricted L γ δ 0 (Degen.residualEnergy N (N.atoms \ T.Y) L 0 β κ₀) (fun z => k0 z.val) p ∧
      MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm p} := by
    rintro _ ⟨κ, hκ, rfl⟩
    have hx := T.label_x_eq hL.ne' hκ.1 hκ₀.1
    have hres := fun (v : V) (hv : v ∈ T.Y) => T.residual_eq (β := β) (c := c) (L := L) (v := v) hx hv
    have hdec := Degen.isDecoration_eraseAtoms N (N.atoms \ T.Y) hκ.1
    have hrst := Degen.isRestricted_eraseAtoms N (N.atoms \ T.Y) hκ.2.1
    refine ⟨⟨hdec.1, fun v hv => ?_⟩, ⟨fun v hv => ?_, hrst.2⟩, ⟨κ, hκ.2.2, hκ.1.1, rfl⟩⟩
    · have hvY : v ∈ T.Y := by rw [← piece_atoms T.sub]; exact hv
      rw [← (hres v hvY).1]; exact hdec.2 v hv
    · have hvY : v ∈ T.Y := by rw [← piece_atoms T.sub]; exact hv
      rw [← (hres v hvY).2]; exact hrst.1 v hv
  rw [himg]
  calc ((Φ '' (pr '' A)).ncard : ℕ∞) ≤ ((pr '' A).ncard : ℕ∞) := by
        exact_mod_cast Set.ncard_image_le hprfin
    _ = (pr '' A).encard := hprfin.cast_ncard_eq
    _ ≤ _ := Set.encard_mono hsub
    _ ≤ _ := MoleProp.encard_le_countEFree (piece N T.Y) L γ δ 0 _ _ _ (fun z => k0 z.val) (fun z => hk0 z.val)

theorem ladderCells_eq_union :
    MoleProp.cellProduct N = fun L γ δ P =>
      MoleProp.cellProduct (piece N T.Y) L γ δ P * MoleProp.cellProduct (Degen.eraseAtoms N T.Y) L γ δ P := by
  classical
  funext L γ δ P
  unfold MoleProp.cellProduct
  rw [← prod_filter_mul_prod_filter_not (MoleProp.ladderCells N) (fun S => S ⊆ T.Y)]
  have h1 : MoleProp.ladderCells (piece N T.Y) = (MoleProp.ladderCells N).filter (fun S => S ⊆ T.Y) := by
    ext S
    simp only [MoleProp.ladderCells, mem_filter, mem_powerset, isLadderCell_piece_iff, piece_atoms T.sub]
    constructor
    · rintro ⟨hSY, hc, _⟩; exact ⟨⟨hSY.trans T.sub, hc⟩, hSY⟩
    · rintro ⟨⟨_, hc⟩, hSY⟩; exact ⟨hSY, hc, hSY⟩
  have h2 : MoleProp.ladderCells (Degen.eraseAtoms N T.Y) =
      (MoleProp.ladderCells N).filter (fun S => ¬ S ⊆ T.Y) := by
    ext S
    simp only [MoleProp.ladderCells, mem_filter, mem_powerset, MoleProp.isLadderCell_erase_iff]
    constructor
    · rintro ⟨hSA, hc, hdis⟩
      refine ⟨⟨hSA.trans sdiff_subset, hc⟩, fun hsub => ?_⟩
      obtain ⟨u, v, _, rfl⟩ := hc
      have hmem : u 0 ∈ Molecule.ladderAtoms u v := mem_union_left _ (mem_image_of_mem _ (mem_univ 0))
      exact disjoint_left.mp hdis hmem (hsub hmem)
    · rintro ⟨⟨hSA, hc⟩, hnsub⟩
      have hdis := (T.cell_sub_or_disjoint hc).resolve_left hnsub
      refine ⟨fun a ha => mem_sdiff.mpr ⟨hSA ha, disjoint_left.mp hdis ha⟩, hc, hdis⟩
  rw [h1, h2]

end OneExit

/-- **The one-exit removal bound** (DH23 ylem2, (Y1) case 2). -/
theorem oneExit_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ 2 * Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (N : Molecule V D),
      (∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) → ∀ T : OneExit N,
      (∀ u ∈ T.Y, ∀ v ∈ T.Y, (piece N T.Y).SameComponent u v) →
      ∀ P : Finset V → ℝ, (∀ S ∈ MoleProp.ladderCells N, 0 ≤ P S) →
        MoleProp.countAFree N L γ δ C1 (0 : Mom d) (lgAdm N L γ η P) P ≤
          MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d)
            (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) P := by
  obtain ⟨Cstar, hCstar, h101⟩ := MoleProp.molecule_count_bound d hd γ hγ η hη hηmax
  refine ⟨Cstar, hCstar, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := h101 (C1 / 2) (by linarith) δ hδ
  refine ⟨max R (Real.exp 1), fun L hL => ?_⟩
  intro V D _ _ _ N hcap T hconn P hP
  classical
  have hLR : R ≤ L := (le_max_left _ _).trans hL
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hLp : 0 < L := (Real.exp_pos 1).trans_le hLe
  have hL1 : 1 ≤ L := (Real.one_le_exp (by norm_num)).trans hLe
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le hLp).mpr hLe
  have hlog0 : 0 < Real.log L ^ 2 := by positivity
  set Adm := lgAdm (d := d) N L γ η P
  -- the piece is a molecule
  have hxdeg : (piece N T.Y).deg (N.atom T.x) ≠ 4 := by
    have h := deg_eraseAtoms_add (N := N) (N.atoms \ T.Y) (fun h => (mem_sdiff.mp h).2 T.atom_x)
    have hx : T.x ∈ Degen.removedDartsAt N (N.atoms \ T.Y) (N.atom T.x) :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
        Finset.mem_sdiff.mpr ⟨N.atom_mem _, T.c_notMem⟩⟩
    have hpos := card_pos.mpr ⟨_, hx⟩
    have h4 := hcap _ (N.atom_mem T.x)
    have hsum := Mole.outdeg_add_indeg N (N.atom T.x)
    change (Degen.eraseAtoms N (N.atoms \ T.Y)).deg (N.atom T.x) ≠ 4
    omega
  have hmol := piece_isMolecule T.sub hcap hconn T.atom_x hxdeg
  have hPpiece : ∀ S ∈ MoleProp.ladderCells (piece N T.Y), 0 ≤ P S := fun S hS => by
    have := (mem_filter.mp hS).2
    exact hP S (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N
      ((isLadderCell_piece_iff S).mp this).1), ((isLadderCell_piece_iff S).mp this).1⟩)
  have hPerase : ∀ S ∈ MoleProp.ladderCells (Degen.eraseAtoms N T.Y), 0 ≤ P S := fun S hS => by
    have := (MoleProp.isLadderCell_erase_iff N T.Y S).mp (mem_filter.mp hS).2
    exact hP S (mem_filter.mpr ⟨mem_powerset.mpr (MoleProp.isLadderCell_subset_atoms N this.1), this.1⟩)
  have hpiece := hR L hLR (piece N T.Y) hmol (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) P
    (fun κ h => by obtain ⟨κ0, ⟨hLG, _⟩, _, rfl⟩ := h; exact MoleProp.largeGap_erase N L γ η 0 _ hLG)
    (fun κ h => by obtain ⟨κ0, ⟨_, hC⟩, _, rfl⟩ := h; exact MoleProp.cellGapRestriction_erase N L 0 _ P _ hC)
    hPpiece
  -- counting
  have hcount := T.countEFree_le (d := d) (γ := γ) (δ := δ) hLp Adm
  have hmono : MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility N T.Y Adm) ≤
      MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d) (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) :=
    MoleProp.countEFree_mono _ L γ δ 0 fun κ h => by
      obtain ⟨κ0, ⟨hLG, hC⟩, _, rfl⟩ := h
      exact ⟨MoleProp.largeGap_erase N L γ η 0 _ hLG, MoleProp.cellGapRestriction_erase N L 0 _ P _ hC⟩
  -- normalization
  have hFp : (piece N T.Y).numComponents = 1 := Mole.numComponents_eq_one (piece N T.Y)
    (by rw [piece_atoms T.sub]; exact ⟨N.atom T.x, T.atom_x⟩) (by rw [piece_atoms T.sub]; exact hconn)
  have hrank := T.circuitRank_identity
  have hFle := T.erase_numComponents_le
  have np := MoleProp.freeNormalization_pos (piece N T.Y) (d := d) (γ := γ) hLp hδ.1 (by linarith : (0 : ℝ) < C1 / 2)
    hlog0 P hPpiece
  have ne := MoleProp.freeNormalization_pos (Degen.eraseAtoms N T.Y) (d := d) (γ := γ) hLp hδ.1
    (by linarith : (0 : ℝ) < C1) hlog0 P hPerase
  have hcells := T.ladderCells_eq_union
  have hratio : MoleProp.freeNormalization N (d := d) L γ δ C1 P ≤
      MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ (C1 / 2) P *
        MoleProp.freeNormalization (Degen.eraseAtoms N T.Y) (d := d) L γ δ C1 P *
          ((1 / 2 : ℝ) ^ (piece N T.Y).circuitRank * 1) := by
    unfold MoleProp.freeNormalization
    have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
    refine norm_ratio hL1 (by linarith [hγ.2]) hδ.1 hδ.2 (by linarith) (by linarith)
      (by rw [hFp] at hrank; omega) (MoleProp.circuitRank_nonneg _)
      (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPpiece).le
      (MoleProp.cellProduct_pos _ hLp.le hδ.1.le hlog0 P hPerase).le zero_le_one ?_
    rw [hcells, mul_one]
  have hhalf : (1 / 2 : ℝ) ^ (piece N T.Y).circuitRank * 1 ≤ 1 := by
    rw [mul_one]
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (MoleProp.circuitRank_nonneg (piece N T.Y))
    rw [hn, zpow_natCast]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [MoleProp.countAFree_eq_normalization]
  calc (MoleProp.countEFree N L γ δ (0 : Mom d) Adm : ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization N (d := d) L γ δ C1 P)
      ≤ ((MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d) (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) *
          MoleProp.countEFree (Degen.eraseAtoms N T.Y) L γ δ (0 : Mom d) (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) : ℕ∞) :
            ℝ≥0∞) * ENNReal.ofReal (MoleProp.freeNormalization (piece N T.Y) (d := d) L γ δ (C1 / 2) P *
              MoleProp.freeNormalization (Degen.eraseAtoms N T.Y) (d := d) L γ δ C1 P *
                ((1 / 2 : ℝ) ^ (piece N T.Y).circuitRank * 1)) := by
        refine mul_le_mul' (ENat.toENNReal_mono (hcount.trans (mul_le_mul' le_rfl hmono)))
          (ENNReal.ofReal_le_ofReal hratio)
    _ = (MoleProp.countAFree (piece N T.Y) L γ δ (C1 / 2) (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) Adm) P) *
        (MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d) (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) P) *
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (piece N T.Y).circuitRank * 1) := by
        rw [MoleProp.countAFree_eq_normalization, MoleProp.countAFree_eq_normalization, ENat.toENNReal_mul,
          ENNReal.ofReal_mul (mul_nonneg np.le ne.le), ENNReal.ofReal_mul np.le]
        ring
    _ ≤ 1 * (MoleProp.countAFree (Degen.eraseAtoms N T.Y) L γ δ C1 (0 : Mom d)
          (lgAdm (Degen.eraseAtoms N T.Y) L γ η P) P) * 1 := by
        exact mul_le_mul' (mul_le_mul' hpiece le_rfl) (ENNReal.ofReal_le_one.mpr hhalf)
    _ = _ := by ring

end WaveTurbulence.MoleProp4
