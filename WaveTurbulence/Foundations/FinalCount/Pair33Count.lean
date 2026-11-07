/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.Pair33
import Mathlib.Tactic

/-! # The `(3,3)` single-pair label count from `system12345_bound` -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4 WaveTurbulence.MoleProp WaveTurbulence.CountLemmas
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- The unit sign of a dart. -/
def sgn (M : Molecule V D) (z : D) : ℤˣ := if M.out z = true then 1 else -1

theorem sgn_cast (M : Molecule V D) (z : D) : ((sgn M z : ℤˣ) : ℤ) = doubleSign (M.out z) := by
  unfold sgn doubleSign; cases M.out z <;> simp

theorem sgn_cast_real (M : Molecule V D) (z : D) : (((sgn M z : ℤˣ) : ℤ) : ℝ) = M.dartSign z := by
  rw [sgn_cast]; exact doubleSign_out_cast M z

theorem sgn_eq_iff (M : Molecule V D) (x y : D) : sgn M x = sgn M y ↔ M.out x = M.out y := by
  unfold sgn; cases M.out x <;> cases M.out y <;> simp

/-- The five labels of a `(3,3)` single pair. -/
def prof5 (m e2 e3 f4 f5 : D) {K : Type*} (κ : D → K) : Fin 5 → K := ![κ m, κ e2, κ e3, κ f4, κ f5]

theorem pair33_count_bound (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (1 / 2 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D), M.IsMolecule → ∀ a ∈ M.atoms, ∀ b ∈ M.atoms,
      a ≠ b → M.deg a = 3 → M.deg b = 3 → M.bondsBetween a b = 1 →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {a, b}) L γ δ (0 : Mom d) (erasedFreeAdmissibility M {a, b} Adm) := by
  classical
  obtain ⟨C, hC, hB⟩ := system12345_bound d hd γ hγ
  refine ⟨C, hC, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hB δ hδ
  refine ⟨max L₀ 1, fun L hL V D _ _ _ M hM a ha b hb hab hda hdb hbb Adm => ?_⟩
  have hLR : L₀ ≤ L := (le_max_left _ _).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right _ _).trans hL)
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  obtain ⟨m, e2, e3, f4, f5, h12, h13, h23, h45, h46, h56, hma, hmb, hA, hB'⟩ := stars33 M hab hda hdb hbb
  have hcapA := not_all_out_equal_of_triple_star M hM ha h12 h13 h23 hA
  have hcapB := not_all_out_equal_of_triple_star M hM hb h45 h46 h56 hB'
  let e : Fin 5 → D := ![m, e2, e3, f4, f5]
  have hcover : ∀ z : DeletedDart M {a, b}, ∃ i : Fin 5, z.val = e i ∨ z.val = M.mate (e i) := by
    apply deleted_cover_of_incident_cover
    intro z hz
    rcases mem_insert.mp hz with hz | hz
    · have hmem : z ∈ M.dartsAt a := (Mole.mem_dartsAt M a z).mpr hz
      rw [hA] at hmem
      rcases mem_insert.mp hmem with h | hmem
      · exact ⟨0, Or.inl h⟩
      · rcases mem_insert.mp hmem with h | h
        · exact ⟨1, Or.inl h⟩
        · exact ⟨2, Or.inl (mem_singleton.mp h)⟩
    · have hmem : z ∈ M.dartsAt b := (Mole.mem_dartsAt M b z).mpr (mem_singleton.mp hz)
      rw [hB'] at hmem
      rcases mem_insert.mp hmem with h | hmem
      · exact ⟨0, Or.inr h⟩
      · rcases mem_insert.mp hmem with h | h
        · exact ⟨3, Or.inl h⟩
        · exact ⟨4, Or.inl (mem_singleton.mp h)⟩
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hLp γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let F := hf.toFinset
  have hmem (κ) : κ ∈ F ↔ κ ∈ A := hf.mem_toFinset
  by_cases hne : A.Nonempty
  · obtain ⟨κ0, hκ0⟩ := hne
    set εA : Fin 3 → ℤˣ := ![sgn M m, sgn M e2, sgn M e3] with hεA
    set εB : Fin 3 → ℤˣ := ![sgn M (M.mate m), sgn M f4, sgn M f5] with hεB
    set nA : Fin d → ℤ := doubleSign (M.out m) • κ0 m + doubleSign (M.out e2) • κ0 e2 + doubleSign (M.out e3) • κ0 e3
    set nB : Fin d → ℤ := doubleSign (M.out (M.mate m)) • κ0 m + doubleSign (M.out f4) • κ0 f4 +
      doubleSign (M.out f5) • κ0 f5
    let a5 : Fin 5 → Mom d := ![k0 m, k0 e2, k0 e3, k0 f4, k0 f5]
    let Q := F.image (localLabels M e)
    have hQS : ∀ q ∈ Q, q ∈ system12345Set L a5 εA εB nA nB (β a) (β b) (δ⁻¹ * L ^ (-2 * γ)) := by
      intro q hq
      obtain ⟨κ, hκ, rfl⟩ := mem_image.mp hq
      have hκA := (hmem κ).mp hκ
      have hκA0 := hκA.1
      have hmA := momentum_of_dartsAt_triple M L ha h12 h13 h23 hA hκA.1
      have hm0A := momentum_of_dartsAt_triple M L ha h12 h13 h23 hA hκ0.1
      have hmB := momentum_of_dartsAt_triple M L hb h45 h46 h56 hB' hκA.1
      have hm0B := momentum_of_dartsAt_triple M L hb h45 h46 h56 hB' hκ0.1
      have hEA := energy_of_dartsAt_triple M L γ δ ha h12 h13 h23 hA hκA.2.1
      have hEB := energy_of_dartsAt_triple M L γ δ hb h45 h46 h56 hB' hκA.2.1
      refine ⟨fun t => ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · fin_cases t
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 m : ‖latticePoint L (κ m) - k0 m‖ ≤ 1)
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 e2 : ‖latticePoint L (κ e2) - k0 e2‖ ≤ 1)
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 e3 : ‖latticePoint L (κ e3) - k0 e3‖ ≤ 1)
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 f4 : ‖latticePoint L (κ f4) - k0 f4‖ ≤ 1)
        · exact (by simpa only [Molecule.kvec, zero_add] using hκA.2.1.2 f5 : ‖latticePoint L (κ f5) - k0 f5‖ ≤ 1)
      · have key : doubleSign (M.out m) • κ m + doubleSign (M.out e2) • κ e2 + doubleSign (M.out e3) • κ e3 = nA := by
          apply latticePointHom_injective hLp.ne'
          simp only [nA, map_add, map_zsmul, latticePointHom_apply, doubleSign_out_smul]
          exact hmA.trans hm0A.symm
        simpa [Fin.sum_univ_three, localLabels, e, hεA, sgn_cast] using key
      · simpa [Fin.sum_univ_three, localLabels, e, hεA, sgn_cast_real] using hEA
      · have key : doubleSign (M.out (M.mate m)) • κ m + doubleSign (M.out f4) • κ f4 + doubleSign (M.out f5) • κ f5 = nB := by
          apply latticePointHom_injective hLp.ne'
          simp only [nB, map_add, map_zsmul, latticePointHom_apply, doubleSign_out_smul]
          rw [hκA.1.1 m] at hmB
          rw [hκ0.1.1 m] at hm0B
          exact hmB.trans hm0B.symm
        simpa [Fin.sum_univ_three, localLabels, e, hεB, sgn_cast] using key
      · rw [hκA.1.1 m] at hEB
        simpa [Fin.sum_univ_three, localLabels, e, hεB, sgn_cast_real] using hEB
    have hcA : ¬ (εA 0 = εA 1 ∧ εA 1 = εA 2) := fun ⟨h1, h2⟩ =>
      hcapA ⟨(sgn_eq_iff M m e2).mp (by simpa [hεA] using h1), (sgn_eq_iff M e2 e3).mp (by simpa [hεA] using h2)⟩
    have hcB : ¬ (εB 0 = εB 1 ∧ εB 1 = εB 2) := fun ⟨h1, h2⟩ =>
      hcapB ⟨(sgn_eq_iff M (M.mate m) f4).mp (by simpa [hεB] using h1), (sgn_eq_iff M f4 f5).mp (by simpa [hεB] using h2)⟩
    have hbound := hL₀ L hLR a5 εA εB hcA hcB nA nB (β a) (β b)
    have hfin : (system12345Set L a5 εA εB nA nB (β a) (β b) (δ⁻¹ * L ^ (-2 * γ))).Finite := by
      refine (Set.Finite.pi (t := fun t => {n : Fin d → ℤ | NearLattice L (a5 t) n})
        (fun t => finite_nearLattice hLp (a5 t))).subset ?_
      intro n hn t _
      exact hn.1 t
    have hQcard : (Q.card : ℝ) ≤ C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - kappaHalf γ) := by
      refine le_trans ?_ hbound
      have := Set.ncard_le_ncard (show (Q : Set (Fin 5 → Fin d → ℤ)) ⊆ _ from hQS) hfin
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this
    have hlocal := card_deletedLabels_image_le_localLabels_image M {a, b} e hcover F
      (fun κ hκ => ((hmem κ).mp hκ).1.1)
    have hImage : (deletedLabels M {a, b} '' A).ncard = (F.image (deletedLabels M {a, b})).card := by
      have he : deletedLabels M {a, b} '' A = (F.image (deletedLabels M {a, b}) : Set _) := by
        rw [Finset.coe_image, hf.coe_toFinset]
      rw [he, Set.ncard_coe_finset]
    have hκ : 0 < kappaHalf γ := kappaHalf_pos hγ
    have hmin : min γ (1 - γ) = 1 - γ := min_eq_right (by linarith [hγ.1])
    have hpow : L ^ (3 * ((d : ℝ) - γ) - (1 - γ) - kappaHalf γ) ≤ L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by rw [hmin]; linarith)
    have hreal : ((deletedLabels M {a, b} '' A).ncard : ℝ) ≤ C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ)) := by
      rw [hImage]
      have hh : ((F.image (deletedLabels M {a, b})).card : ℝ) ≤ Q.card := by exact_mod_cast hlocal
      refine hh.trans (hQcard.trans ?_)
      have : 0 ≤ C * δ⁻¹ ^ 2 := by have := hδ.1; positivity
      exact mul_le_mul_of_nonneg_left hpow this |>.trans_eq' (by ring) |>.trans_eq (by ring)
    have hnat : (deletedLabels M {a, b} '' A).ncard ≤ ⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    have hEN : ((deletedLabels M {a, b} '' A).ncard : ℕ∞) ≤
        (⌈C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))⌉₊ : ℕ∞) := by exact_mod_cast hnat
    exact (encard_le_deletedImage_mul_post M {a, b} hLp γ δ (0 : Mom d) Adm c β k0 hk0).trans
      (mul_le_mul_of_nonneg_right hEN bot_le)
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he, Set.encard_empty]
    exact bot_le

end WaveTurbulence.FinalCountG8
