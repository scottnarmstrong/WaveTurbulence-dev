/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.Domain
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTHval
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the valley property from weak monotonicity (the parent-chain argument)

o73 Prop 18.1: "the source two-monotone-subsequence assertion remains true by taking limits from the legal strict
time domains". In Lean this is a direct argument. If along every parent step out of the interior rungs strictly
between `i` and `l` the time does not decrease, then the rung maxima satisfy `y j ≤ max (y i) (y l)` for
`i < j < l` (`rung_valley`). Follow the parent chain from the maximal atom of rung `j`. It never meets rungs `i` or
`l`, and it moves by at most one rung per step (`parent_mem_interior`). So it stays among finitely many atoms while
its depth decreases: a contradiction.

On the contracted domain every parent step is weakly monotone (`mono_on_Om0`), except at a *bad pin*: a pinned branch
whose pinned parent has a smaller pin time (`splicedTimeDomainFace` does not order two pinned branches). -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LadderDisjoint WaveTurbulence.Mole
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w : ℕ} {G : Garden w}

/-- A pinned branch whose pinned parent has a smaller pin time. -/
def BadPin (fix : GBranch G.tree → Option ℝ) (a : GBranch G.tree) : Prop :=
  ∃ p, a.IsChildOf p ∧ fix a ≠ none ∧ fix p ≠ none ∧ pinVal fix p < pinVal fix a

variable {fix : GBranch G.tree → Option ℝ} {face : GBranch G.tree → Option (GBranch G.tree)}

/-- **Weak monotonicity on the contracted domain**, except at bad pins. -/
theorem mono_on_Om0 (hF : FaceOK fix face) {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ}
    {τ : Iv fix face → ℝ}
    (hτ : τ ∈ Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face))
    {a p : GBranch G.tree} (hch : a.IsChildOf p) (hgood : ¬ BadPin fix a) :
    extendFixFace G fix face τ a ≤ extendFixFace G fix face τ p := by
  have hrep : ∀ b (h : fix b = none), extendFixFace G fix face τ b = τ (repI hF b h) := fun b h => by
    rw [extendFixFace_unpin τ h, ttv_repV hF τ h]
  by_cases ha : fix a = none <;> by_cases hp : fix p = none
  · rw [hrep a ha, hrep p hp]
    by_cases he : repI hF a ha = repI hF p hp
    · rw [he]
    · exact (hτ.2.2 _ _ ⟨he, a, p, hch, ha, hp, rfl, rfl⟩).le
  · rw [hrep a ha, extendFixFace_pin τ hp]
    have hmem : p ∈ capSrc fix face (repI hF a ha) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp, a, hch, ha, rfl⟩
    exact ((hτ.2.1 _).trans_le (capF_le_pin layer rootTime hmem)).le
  · rw [extendFixFace_pin τ ha, hrep p hp]
    have hmem : a ∈ floorSrc fix face (repI hF p hp) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, p, hch, hp, rfl⟩
    exact (pin_le_lsF hτ hmem).trans (hτ.1 _).1
  · rw [extendFixFace_pin τ ha, extendFixFace_pin τ hp]
    by_contra hlt
    exact hgood ⟨p, hch, ha, hp, not_le.mp hlt⟩

/-- The parent of an interior ladder atom lies in a neighbouring rung (or is its rung partner). -/
theorem parent_in_rungs {m : ℕ} {u v : Fin (m + 1) → GBranch G.tree} (hL : G.molecule.IsLadder u v)
    {k : ℕ} (hk1 : 1 ≤ k) (hkm : k < m) {a : GBranch G.tree} (ha : a = rowN u k ∨ a = rowN v k) :
    ∃ p, a.IsChildOf p ∧ ∃ k', (k' = k - 1 ∨ k' = k ∨ k' = k + 1) ∧ (p = rowN u k' ∨ p = rowN v k') := by
  have hkm1 : k - 1 + 1 = k := by omega
  have hl := ladderN_rail G.molecule hL (show k - 1 < m by omega)
  rw [hkm1] at hl
  have hr := ladderN_rail G.molecule hL hkm
  have hkle : k ≤ m := hkm.le
  have hd1 : k - 1 ≤ m := by omega
  have hd2 : k + 1 ≤ m := by omega
  have hl1 : G.molecule.bondsBetween (rowN u k) (rowN u (k - 1)) = 1 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hl.1
  have hl2 : G.molecule.bondsBetween (rowN v k) (rowN v (k - 1)) = 1 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hl.2.1
  have hrung := ladderN_rung G.molecule hL hkle
  have hrung' : G.molecule.bondsBetween (rowN v k) (rowN u k) = 2 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hrung
  rcases ha with rfl | rfl
  · obtain ⟨hc, hp⟩ := parent_mem_interior G (a := rowN u k) (b := rowN v k) (c := rowN u (k - 1))
      (e := rowN u (k + 1)) (ladderN_uv G.molecule hL hkle hkle) (ladderN_uu G.molecule hL hkle hd1 (by omega))
      (ladderN_uu G.molecule hL hkle hd2 (by omega)) (Ne.symm (ladderN_uv G.molecule hL hd1 hkle))
      (Ne.symm (ladderN_uv G.molecule hL hd2 hkle)) (ladderN_uu G.molecule hL hd1 hd2 (by omega))
      hrung hl1 hr.1
    refine ⟨_, isChildOf_parent (rowN u k) hc, ?_⟩
    rcases hp with hp | hp | hp
    · exact ⟨k, Or.inr (Or.inl rfl), Or.inr hp⟩
    · exact ⟨k - 1, Or.inl rfl, Or.inl hp⟩
    · exact ⟨k + 1, Or.inr (Or.inr rfl), Or.inl hp⟩
  · obtain ⟨hc, hp⟩ := parent_mem_interior G (a := rowN v k) (b := rowN u k) (c := rowN v (k - 1))
      (e := rowN v (k + 1)) (Ne.symm (ladderN_uv G.molecule hL hkle hkle))
      (ladderN_vv G.molecule hL hkle hd1 (by omega)) (ladderN_vv G.molecule hL hkle hd2 (by omega))
      (ladderN_uv G.molecule hL hkle hd1) (ladderN_uv G.molecule hL hkle hd2)
      (ladderN_vv G.molecule hL hd1 hd2 (by omega)) hrung' hl2 hr.2.1
    refine ⟨_, isChildOf_parent (rowN v k) hc, ?_⟩
    rcases hp with hp | hp | hp
    · exact ⟨k, Or.inr (Or.inl rfl), Or.inl hp⟩
    · exact ⟨k - 1, Or.inl rfl, Or.inr hp⟩
    · exact ⟨k + 1, Or.inr (Or.inr rfl), Or.inr hp⟩

theorem isChildOf_length_succ {a p : GBranch G.tree} (h : a.IsChildOf p) : a.1.2.length = p.1.2.length + 1 := by
  obtain ⟨_, i, hi⟩ := h
  rw [hi]; simp

/-- **The valley property between two rungs**, from weak monotonicity at the atoms strictly between them. -/
theorem rung_valley {m : ℕ} {u v : Fin (m + 1) → GBranch G.tree} (hL : G.molecule.IsLadder u v)
    (t : GBranch G.tree → ℝ) (Good : GBranch G.tree → Prop)
    (hmono : ∀ a p, Good a → a.IsChildOf p → t a ≤ t p) {i j l : ℕ} (hij : i < j) (hjl : j < l) (hlm : l ≤ m)
    (hgood : ∀ k, i < k → k < l → Good (rowN u k) ∧ Good (rowN v k)) :
    max (t (rowN u j)) (t (rowN v j)) ≤
      max (max (t (rowN u i)) (t (rowN v i))) (max (t (rowN u l)) (t (rowN v l))) := by
  by_contra hcon
  set M := max (max (t (rowN u i)) (t (rowN v i))) (max (t (rowN u l)) (t (rowN v l))) with hM
  have hlt : M < max (t (rowN u j)) (t (rowN v j)) := not_le.mp hcon
  obtain ⟨a₀, ha₀, hta₀⟩ : ∃ a₀, (a₀ = rowN u j ∨ a₀ = rowN v j) ∧ M < t a₀ := by
    rcases le_total (t (rowN v j)) (t (rowN u j)) with h | h
    · exact ⟨rowN u j, Or.inl rfl, by rwa [max_eq_left h] at hlt⟩
    · exact ⟨rowN v j, Or.inr rfl, by rwa [max_eq_right h] at hlt⟩
  have key : ∀ n : ℕ, ∃ k a, i < k ∧ k < l ∧ (a = rowN u k ∨ a = rowN v k) ∧ M < t a ∧
      a.1.2.length + n ≤ a₀.1.2.length := by
    intro n
    induction n with
    | zero => exact ⟨j, a₀, hij, hjl, ha₀, hta₀, le_rfl⟩
    | succ n ih =>
      obtain ⟨k, a, hik, hkl, ha, hta, hlen⟩ := ih
      obtain ⟨p, hch, k', hk', hp⟩ := parent_in_rungs hL (by omega) (by omega) ha
      have hga : Good a := by rcases ha with rfl | rfl; exacts [(hgood k hik hkl).1, (hgood k hik hkl).2]
      have htp : M < t p := hta.trans_le (hmono a p hga hch)
      have hli := isChildOf_length_succ hch
      have hne_i : k' ≠ i := by
        rintro rfl
        have : t p ≤ M := by
          rcases hp with rfl | rfl
          · exact (le_max_left _ _).trans (le_max_left _ _)
          · exact (le_max_right _ _).trans (le_max_left _ _)
        linarith
      have hne_l : k' ≠ l := by
        rintro rfl
        have : t p ≤ M := by
          rcases hp with rfl | rfl
          · exact (le_max_left _ _).trans (le_max_right _ _)
          · exact (le_max_right _ _).trans (le_max_right _ _)
        linarith
      refine ⟨k', p, ?_, ?_, hp, htp, by omega⟩
      · rcases hk' with rfl | rfl | rfl <;> omega
      · rcases hk' with rfl | rfl | rfl <;> omega
  obtain ⟨k, a, -, -, -, -, hlen⟩ := key (a₀.1.2.length + 1)
  omega

end WaveTurbulence.Flower.FinalMKPin
