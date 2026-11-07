/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Final3f
/-! # FLOWER-P5: the no-peak property and the paired-atom data under a child-free ordering hypothesis

Copies of `no_peak` (`MolTree`) and `CD.hval` (`Glue4`) with the global order hypothesis weakened to children in a
predicate `Fr` (the free clocks), which contains all ladder atoms; and the dependence of `CD.hXf` on the ladder atoms
only. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP5
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.LadderDisjoint WaveTurbulence.Mole Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w}

theorem no_peak_fr (G : Garden w) (Fr : GBranch G.tree → Prop) {m : ℕ} {u v : Fin (m + 1) → GBranch G.tree}
    (hL : G.molecule.IsLadder u v) (hFr : ∀ j, Fr (rowN u j) ∧ Fr (rowN v j)) (t : GBranch G.tree → ℝ)
    (ht : ∀ b' b : GBranch G.tree, b'.IsChildOf b → Fr b' → t b' < t b) {j : ℕ} (hj1 : 1 ≤ j) (hjm : j < m) :
    max (t (rowN u j)) (t (rowN v j)) < max (t (rowN u (j - 1))) (t (rowN v (j - 1))) ∨
    max (t (rowN u j)) (t (rowN v j)) < max (t (rowN u (j + 1))) (t (rowN v (j + 1))) := by
  have hjm1 : j - 1 + 1 = j := by omega
  have hl := ladderN_rail G.molecule hL (show j - 1 < m by omega)
  rw [hjm1] at hl
  have hr := ladderN_rail G.molecule hL hjm
  have hjle : j ≤ m := hjm.le
  have hd1 : j - 1 ≤ m := by omega
  have hd2 : j + 1 ≤ m := by omega
  have hl1 : G.molecule.bondsBetween (rowN u j) (rowN u (j - 1)) = 1 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hl.1
  have hl2 : G.molecule.bondsBetween (rowN v j) (rowN v (j - 1)) = 1 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hl.2.1
  have hrung := ladderN_rung G.molecule hL hjle
  have hrung' : G.molecule.bondsBetween (rowN v j) (rowN u j) = 2 := by
    rw [LadderDisjoint.bondsBetween_comm]; exact hrung
  by_cases hcase : t (rowN v j) ≤ t (rowN u j)
  · have hmax : max (t (rowN u j)) (t (rowN v j)) = t (rowN u j) := max_eq_left hcase
    rw [hmax]
    obtain ⟨hc, hp⟩ := parent_mem_interior G (a := rowN u j) (b := rowN v j) (c := rowN u (j - 1))
      (e := rowN u (j + 1)) (ladderN_uv G.molecule hL hjle hjle) (ladderN_uu G.molecule hL hjle hd1 (by omega))
      (ladderN_uu G.molecule hL hjle hd2 (by omega)) (Ne.symm (ladderN_uv G.molecule hL hd1 hjle))
      (Ne.symm (ladderN_uv G.molecule hL hd2 hjle)) (ladderN_uu G.molecule hL hd1 hd2 (by omega))
      hrung hl1 hr.1
    have hlt := ht _ _ (isChildOf_parent (rowN u j) hc) (hFr j).1
    rcases hp with hp | hp | hp
    · rw [hp] at hlt; exact absurd hlt (not_lt.mpr hcase)
    · left; rw [hp] at hlt; exact lt_of_lt_of_le hlt (le_max_left _ _)
    · right; rw [hp] at hlt; exact lt_of_lt_of_le hlt (le_max_left _ _)
  · have hcase' : t (rowN u j) < t (rowN v j) := not_le.mp hcase
    have hmax : max (t (rowN u j)) (t (rowN v j)) = t (rowN v j) := max_eq_right hcase'.le
    rw [hmax]
    obtain ⟨hc, hp⟩ := parent_mem_interior G (a := rowN v j) (b := rowN u j) (c := rowN v (j - 1))
      (e := rowN v (j + 1)) (Ne.symm (ladderN_uv G.molecule hL hjle hjle))
      (ladderN_vv G.molecule hL hjle hd1 (by omega)) (ladderN_vv G.molecule hL hjle hd2 (by omega))
      (ladderN_uv G.molecule hL hjle hd1) (ladderN_uv G.molecule hL hjle hd2)
      (ladderN_vv G.molecule hL hd1 hd2 (by omega)) hrung' hl2 hr.2.1
    have hlt := ht _ _ (isChildOf_parent (rowN v j) hc) (hFr j).2
    rcases hp with hp | hp | hp
    · rw [hp] at hlt; exact absurd hlt (not_lt.mpr hcase'.le)
    · left; rw [hp] at hlt; exact lt_of_lt_of_le hlt (le_max_right _ _)
    · right; rw [hp] at hlt; exact lt_of_lt_of_le hlt (le_max_right _ _)


theorem rowN_mem_ladderAtoms {V : Type*} [DecidableEq V] {m : ℕ} (u v : Fin (m + 1) → V) (j : ℕ) :
    rowN u j ∈ Molecule.ladderAtoms u v ∧ rowN v j ∈ Molecule.ladderAtoms u v := by
  unfold Molecule.ladderAtoms rowN
  exact ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)),
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))⟩

variable {D : SplicedKernelData G d} {L γ δ : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)}
  {hp : G.IsPlain} {π0 : PF G} {εS : LQ G → ℝ}

theorem CD.hval_fr (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (Fr : GBranch G.tree → Prop) (hFr : ∀ S j, Fr (rowN (π0.u S) j) ∧ Fr (rowN (π0.v S) j))
    (t : GBranch G.tree → ℝ) (ht : ∀ b' b : GBranch G.tree, b'.IsChildOf b → Fr b' → t b' < t b)
    (S : LQ G) :
    NP (fun j : Fin (cd.Kn isSmall S) =>
      max (t (cd.ua isSmall ⟨S, j⟩)) (t (cd.va isSmall ⟨S, j⟩))) := by
  have hP : ∀ j, 1 ≤ j → j < π0.m S →
      max (t (rowN (π0.u S) j)) (t (rowN (π0.v S) j)) <
        max (t (rowN (π0.u S) (j - 1))) (t (rowN (π0.v S) (j - 1))) ∨
      max (t (rowN (π0.u S) j)) (t (rowN (π0.v S) j)) <
        max (t (rowN (π0.u S) (j + 1))) (t (rowN (π0.v S) (j + 1))) :=
    fun j h1 h2 => no_peak_fr G Fr (π0.ladder S) (hFr S) t ht h1 h2
  exact NP_sub (fun j => max (t (rowN (π0.u S) j)) (t (rowN (π0.v S) j))) (π0.m S) hP
    (cd.enum isSmall S) (cd.enum_strictMono isSmall S) (cd.enum_le isSmall S)

theorem CD.hXf_dep_fr (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (hinj : Function.Injective (Sum.elim (cd.ua isSmall) (cd.va isSmall)))
    (Fr : GBranch G.tree → Prop) (hFr : ∀ S b i, Fr (atomAt π0 S b i))
    (θ : Jr (cd.Kn isSmall) → Bool) (x : GBranch G.tree) (β β' : GBranch G.tree → ℝ)
    (h : ∀ b, b ∉ Finset.univ.image (xθ (cd.ua isSmall) (cd.va isSmall) θ) → Fr b → β b = β' b) :
    cd.hXf isSmall θ x β = cd.hXf isSmall θ x β' := by
  unfold CD.hXf
  by_cases hx : ∃ s, xθ (cd.ua isSmall) (cd.va isSmall) θ s = x
  · have hy : ∀ s, Fr (yθ (cd.ua isSmall) (cd.va isSmall) θ s) := by
      intro s; unfold yθ; split_ifs <;> exact hFr _ _ _
    rw [dif_pos hx, dif_pos hx]
    have h1 : ∀ l b, β (atomAt π0 hx.choose.1 b (cd.r' hx.choose.1 l)) = β' (atomAt π0 hx.choose.1 b (cd.r' hx.choose.1 l)) :=
      fun l b => h _ (cd.sel_not_X isSmall θ _ l b) (hFr _ _ _)
    have h2 : β (yθ (cd.ua isSmall) (cd.va isSmall) θ hx.choose) = β' (yθ (cd.ua isSmall) (cd.va isSmall) θ hx.choose) := by
      refine h _ (fun hmem => ?_) ?_
      · obtain ⟨s', _, hs'⟩ := Finset.mem_image.mp hmem
        exact yθ_ne_xθ (cd.ua isSmall) (cd.va isSmall) hinj θ _ _ hs'.symm
      · exact hy _
    simp only [h1, h2]
  · rw [dif_neg hx, dif_neg hx]

end WaveTurbulence.FlowerP5
