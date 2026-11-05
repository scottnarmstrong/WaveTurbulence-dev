/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import Mathlib
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
public import WaveTurbulence.Foundations.Spine.LadderBridge
public import WaveTurbulence.Foundations.Spine.LadderTime
/-! # Finite support of the local ladder weights (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Set

lemma finite_lattice_ball {d : ℕ} {L : ℝ} (hL : 0 < L) (v0 : Mom d) :
    Set.Finite {n : Fin d → ℤ | ‖v0 + latticePoint L n‖ ≤ 1} := by
  have hsub : {n : Fin d → ℤ | ‖v0 + latticePoint L n‖ ≤ 1} ⊆
      Set.pi univ (fun j : Fin d => Set.Icc (-⌈L * (1 + |v0 j|)⌉) ⌈L * (1 + |v0 j|)⌉) := by
    intro n hn j _
    have hj : |(v0 + latticePoint L n) j| ≤ 1 :=
      (PiLp.norm_apply_le (v0 + latticePoint L n) j).trans hn
    have hj' : |v0 j + (n j : ℝ) / L| ≤ 1 := by simpa [latticePoint] using hj
    have h1 : |(n j : ℝ) / L| ≤ 1 + |v0 j| := by
      have := abs_sub (v0 j + (n j : ℝ) / L) (v0 j)
      have h2 : |(n j : ℝ) / L| = |v0 j + (n j : ℝ) / L - v0 j| := by ring_nf
      rw [h2]
      linarith [this, hj']
    have h3 : |(n j : ℝ)| ≤ L * (1 + |v0 j|) := by
      rw [abs_div, abs_of_pos hL, div_le_iff₀ hL] at h1
      linarith
    have h4 : |n j| ≤ ⌈L * (1 + |v0 j|)⌉ := by
      have : ((|n j| : ℤ) : ℝ) ≤ ⌈L * (1 + |v0 j|)⌉ :=
        (by push_cast; exact h3.trans (Int.le_ceil _))
      exact_mod_cast this
    exact ⟨by linarith [neg_abs_le (n j)], le_trans (le_abs_self _) h4⟩
  exact (Set.Finite.pi (fun j => Set.finite_Icc _ _)).subset hsub


variable {w d : ℕ} {G : Garden w}

lemma bondIndex_injective (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (z z' : GenDecoration G d roots 0)
    (h : bondIndex G z.1 = bondIndex G z'.1) : z = z' := by
  have inj := latticePoint_injective (d := d) hL
  have hrest : ∀ y : GenDecoration G d roots 0, Mole.restrictLabels G (fun a => base + latticePoint L (y.1 a)) =
      Molecule.kvec L base (bondIndex G y.1) := by
    intro y; funext x; rw [bondIndex_eq_restrict]; rfl
  have he : Mole.restrictLabels G (fun a => base + latticePoint L (z.1 a)) =
      Mole.restrictLabels G (fun a => base + latticePoint L (z'.1 a)) := by
    rw [hrest z, hrest z', h]
  have := Mole.garden_vectors_determined_by_bonds G hP (rootVec L base roots)
    (fun a => base + latticePoint L (z.1 a)) (fun a => base + latticePoint L (z'.1 a))
    (isDecoration_coset L base z.2.1) (isDecoration_coset L base z'.2.1)
    (fun i => by rw [z.2.2.1 i]; rfl) (fun i => by rw [z'.2.2.1 i]; rfl) he
  apply Subtype.ext
  funext a
  have := congrFun this a
  exact inj (add_left_cancel this)


open Classical in
theorem weight_support_finite (hP : G.IsPlain) {L : ℝ} (hL : 0 < L) (base : Mom d)
    (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D) (S : Finset (GBranch G.tree))
    (γ η : ℝ) (roots : Fin w → (Fin d → ℤ)) (boundary : GardenDart G → (Fin d → ℤ)) :
    Set.Finite {z : ↥(localLadderDecorations G S roots boundary) |
      ladderWeight D S L γ η base z.1.1 ≠ 0} := by
  let ball : Mom d → Set (Fin d → ℤ) := fun c => {n | ‖(base - c) + latticePoint L n‖ ≤ 1}
  let F : GardenDart G → Set (Fin d → ℤ) := fun x =>
    if G.molecule.InGroup S x then
      (if G.molecule.out x = true then ball (D.center x) else ball (D.center (G.molecule.mate x)))
    else {boundary x}
  have hF : ∀ x, (F x).Finite := by
    intro x
    unfold F
    split_ifs
    · exact finite_lattice_ball hL _
    · exact finite_lattice_ball hL _
    · exact Set.finite_singleton _
  have hK : (Set.pi Set.univ F).Finite := Set.Finite.pi (fun x => hF x)
  refine Set.Finite.of_injOn (f := fun z => bondIndex G z.1.1) (t := Set.pi Set.univ F) ?_ ?_ hK
  · intro z hz x _
    have hzw : ladderWeight D S L γ η base z.1.1 ≠ 0 := hz
    have hamp : ∀ y ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
        ‖base + latticePoint L (bondIndex G z.1.1 y) - D.center y‖ ≤ 1 := by
      intro y hy
      have hne : D.edgeAmplitude y (base + latticePoint L (bondIndex G z.1.1 y)) ≠ 0 := by
        intro h0
        apply hzw
        unfold ladderWeight
        have : (∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup S),
            D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1.1 x))) = 0 :=
          Finset.prod_eq_zero hy h0
        rw [this, mul_zero]
      by_contra hcon
      push Not at hcon
      exact hne ((hD.2.1 y (Finset.mem_filter.mp hy).1).2 _ hcon)
    have hmate : bondIndex G z.1.1 (G.molecule.mate x) = bondIndex G z.1.1 x := by
      rw [bondIndex_eq_restrict]
      exact Mole.restrictLabels_mate G z.1.1 z.1.2.1.2 x
    simp only [Set.mem_univ] at *
    show bondIndex G z.1.1 x ∈ F x
    unfold F
    by_cases hg : G.molecule.InGroup S x
    · rw [ite_eq_left hg]
      by_cases ho : G.molecule.out x = true
      · rw [ite_eq_left ho]
        have := hamp x (Finset.mem_filter.mpr ⟨by simp [Molecule.bonds, ho], hg⟩)
        show ‖(base - D.center x) + latticePoint L (bondIndex G z.1.1 x)‖ ≤ 1
        have e : (base - D.center x) + latticePoint L (bondIndex G z.1.1 x) =
            base + latticePoint L (bondIndex G z.1.1 x) - D.center x := by abel
        rw [e]; exact this
      · rw [ite_eq_right ho]
        have hom : G.molecule.out (G.molecule.mate x) = true := by
          rw [G.molecule.out_mate]; simpa using ho
        have hgm : G.molecule.InGroup S (G.molecule.mate x) := by
          refine ⟨hg.2, ?_⟩; rw [G.molecule.mate_mate]; exact hg.1
        have := hamp _ (Finset.mem_filter.mpr ⟨by simp [Molecule.bonds, hom], hgm⟩)
        rw [hmate] at this
        show ‖(base - D.center (G.molecule.mate x)) + latticePoint L (bondIndex G z.1.1 x)‖ ≤ 1
        have e : (base - D.center (G.molecule.mate x)) + latticePoint L (bondIndex G z.1.1 x) =
            base + latticePoint L (bondIndex G z.1.1 x) - D.center (G.molecule.mate x) := by abel
        rw [e]; exact this
    · rw [ite_eq_right hg]
      exact z.2 x hg
  · intro z _ z' _ h
    apply Subtype.ext
    exact bondIndex_injective hP hL.ne' base roots z.1 z'.1 h

end WaveTurbulence.LadderDecay
