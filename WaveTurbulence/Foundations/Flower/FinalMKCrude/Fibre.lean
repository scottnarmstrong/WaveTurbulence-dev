/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.Assembly3

/-! # C2 FINALMK-CRUDE: weighted fibre factorisation

Copy-thread of main's `Spine/FibreFactor.lean` (`fibre_factor`) for a decoration weight `φ` that factors over the
fibre as `r * ∏ i, φi i z`, with `φi i` local to the atoms of the `i`-th ladder. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Flower.FinalMKCrude
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.CoarseSpliced Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The weighted local lattice sum of the `i`-th ladder at fixed times. -/
noncomputable def LamW (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (φi : ι → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (L γ η δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (z₀ : GenDecoration G d roots 0)
    (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1))) (i : ι)
    (s : S i → ℝ) : ℂ :=
  ∑ ζ ∈ T i, φi i ζ.1.1 * ladderWeight D (S i) L γ η base ζ.1.1 * ladderPhase D (S i) L γ δ base ζ.1.1 s

/-- **Fibre factorisation.** -/
theorem fibre_factorW (hP : G.IsPlain) (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (hH : ∀ i, Disjoint (S i) D.hinges)
    {L : ℝ} (hL : L ≠ 0) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z₀ : GenDecoration G d roots 0) (Zc : Finset (GenDecoration G d roots 0))
    (φ : (GNode G.tree → (Fin d → ℤ)) → ℂ) (r : ℂ) (φi : ι → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (hφ : ∀ z : GenDecoration G d roots 0, AgreeOff S z z₀ → φ z.1 = r * ∏ i, φi i z.1)
    (hφi : ∀ i (z z' : GenDecoration G d roots 0),
      (∀ x, G.molecule.atom x ∈ S i → bondIndex G z.1 x = bondIndex G z'.1 x) → φi i z.1 = φi i z'.1)
    (hZ : ∀ z, AgreeOff S z z₀ → splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 → z ∈ Zc)
    (hZ' : ∀ z ∈ Zc, AgreeOff S z z₀)
    (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1)))
    (hT : ∀ i ζ, ζ ∉ T i → ladderWeight D (S i) L γ η base ζ.1.1 = 0)
    (t : GBranch G.tree → ℝ) :
    ∑ z ∈ Zc, φ z.1 * (splicedMomentumAmplitude G D L γ η base z.1 * globalPhase D L γ δ base z.1 t) =
      (r * (restAmp D S L γ η base z₀.1 *
        ∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z₀.1 v * t v : ℝ) * Complex.I))) *
        ∏ i, LamW D S φi L γ η δ base z₀ T i (fun v : S i => t v.1) := by
  -- gluing map
  have hglue : ∀ g : (∀ i, ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1))),
      ∃ z : GenDecoration G d roots 0,
        (∀ i x, G.molecule.atom x ∈ S i → bondIndex G z.1 x = bondIndex G (g i).1.1 x) ∧
        (∀ x, G.molecule.atom x ∉ Uni S → bondIndex G z.1 x = bondIndex G z₀.1 x) := by
    intro g
    refine exists_glue hP hL base roots z₀ S hS (fun i => (g i).1) ?_
    intro i x _ hx
    exact (g i).2 x hx
  choose gl hgl1 hgl2 using hglue
  have hgl3 : ∀ g, AgreeOff S (gl g) z₀ := by
    intro g x hx
    by_cases ha : G.molecule.atom x ∈ Uni S
    · obtain ⟨i, -, hi⟩ := mem_biUnion.mp ha
      rw [hgl1 g i x hi]
      exact (g i).2 x (fun hh => hx ⟨i, hh⟩)
    · exact hgl2 g x ha
  -- the term factors
  have hterm : ∀ g, φ (gl g).1 * (splicedMomentumAmplitude G D L γ η base (gl g).1 *
      globalPhase D L γ δ base (gl g).1 t) =
      (r * (restAmp D S L γ η base z₀.1 *
        ∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z₀.1 v * t v : ℝ) * Complex.I))) *
      ∏ i, (φi i (g i).1.1 * ladderWeight D (S i) L γ η base (g i).1.1 *
        ladderPhase D (S i) L γ δ base (g i).1.1 (fun v : S i => t v.1)) := by
    intro g
    rw [hφ (gl g) (hgl3 g)]
    have h4 : ∀ i, φi i (gl g).1 = φi i (g i).1.1 :=
      fun i => hφi i (gl g) (g i).1 (fun x hx => hgl1 g i x hx)
    rw [momAmp_factor D S hS hH, globalPhase_factor D S hS,
      restAmp_congr hP D S hH L γ η base roots (gl g) z₀ (hgl3 g)]
    have h1 : ∀ i, ladderWeight D (S i) L γ η base (gl g).1 = ladderWeight D (S i) L γ η base (g i).1.1 :=
      fun i => ladderWeight_congr hP D (S i) L γ η base roots (gl g) (g i).1 (fun x hx => hgl1 g i x hx)
    have h2 : ∀ i, ladderPhase D (S i) L γ δ base (gl g).1 = ladderPhase D (S i) L γ δ base (g i).1.1 :=
      fun i => ladderPhase_congr hP D (S i) L γ δ base roots (gl g) (g i).1 (fun x hx => hgl1 g i x hx)
    have h3 : ∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base (gl g).1 v * t v : ℝ) * Complex.I) =
        ∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z₀.1 v * t v : ℝ) * Complex.I) := by
      apply prod_congr rfl
      intro v hv
      rw [splicedFrequency_rest hP D S L γ δ base roots (gl g) z₀ (hgl3 g) v (mem_sdiff.mp hv).2]
    simp_rw [h1, h2, h4]
    rw [h3]
    simp only [Finset.prod_mul_distrib]
    ring
  -- injectivity of gluing
  have hinj : ∀ g g', gl g = gl g' → g = g' := by
    intro g g' h
    funext i
    apply Subtype.ext
    apply bondIndex_injective G hP roots
    funext x
    show bondIndex G (g i).1.1 x = bondIndex G (g' i).1.1 x
    by_cases hx : G.molecule.InGroup (S i) x
    · have h1 := hgl1 g i x hx.1
      have h2 := hgl1 g' i x hx.1
      rw [← h1, ← h2, h]
    · rw [(g i).2 x hx, (g' i).2 x hx]
  -- reindex the sum over the glue image
  have hsum : ∑ z ∈ Zc, φ z.1 * (splicedMomentumAmplitude G D L γ η base z.1 * globalPhase D L γ δ base z.1 t) =
      ∑ g ∈ Fintype.piFinset T, φ (gl g).1 * (splicedMomentumAmplitude G D L γ η base (gl g).1 *
        globalPhase D L γ δ base (gl g).1 t) := by
    symm
    refine Finset.sum_bij_ne_zero (fun g _ _ => gl g) ?_ ?_ ?_ ?_
    · intro g _ hne
      apply hZ _ (hgl3 g)
      intro h0
      apply hne
      rw [h0, zero_mul, mul_zero]
    · intro g _ _ g' _ _ h
      exact hinj g g' h
    · intro z hz hne
      have hAg := hZ' z hz
      have hm : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 := by
        intro h0; apply hne; rw [h0, zero_mul, mul_zero]
      have hfac := momAmp_factor D S hS hH L γ η base z.1
      have hw : ∀ i, ladderWeight D (S i) L γ η base z.1 ≠ 0 := by
        intro i h0
        apply hm
        rw [hfac]
        have : ∏ j, ladderWeight D (S j) L γ η base z.1 = 0 := Finset.prod_eq_zero (mem_univ i) h0
        rw [this, mul_zero]
      -- hybrid decorations
      have hyb : ∀ i, ∃ h : GenDecoration G d roots 0,
          (∀ x, G.molecule.atom x ∈ S i → bondIndex G h.1 x = bondIndex G z.1 x) ∧
          (∀ x, ¬ G.molecule.InGroup (S i) x → bondIndex G h.1 x = bondIndex G z₀.1 x) := by
        intro i
        obtain ⟨h, h1, h2⟩ := exists_glue hP hL base roots z₀ S hS
          (fun j => if j = i then z else z₀) (by
            intro j x hxj hxn
            by_cases hji : j = i
            · subst hji
              simp only [ite_true]
              exact hAg x (fun ⟨k, hk⟩ => by
                by_cases hkj : k = j
                · subst hkj; exact hxn hk
                · exact Finset.disjoint_left.mp (hS k j hkj) hk.1 hxj)
            · simp only [hji, ite_false])
        refine ⟨h, fun x hx => by rw [h1 i x hx]; simp, fun x hx => ?_⟩
        by_cases ha : G.molecule.atom x ∈ Uni S
        · obtain ⟨j, -, hj⟩ := mem_biUnion.mp ha
          rw [h1 j x hj]
          by_cases hji : j = i
          · subst hji
            simp only [ite_true]
            exact hAg x (fun ⟨k, hk⟩ => by
              by_cases hkj : k = j
              · subst hkj; exact hx hk
              · exact Finset.disjoint_left.mp (hS k j hkj) hk.1 hj)
          · simp only [hji, ite_false]
        · rw [h2 x ha]
      choose hh hh1 hh2 using hyb
      let g : ∀ i, ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1)) :=
        fun i => ⟨hh i, fun x hx => hh2 i x hx⟩
      have hgT : g ∈ Fintype.piFinset T := by
        rw [Fintype.mem_piFinset]
        intro i
        by_contra hni
        apply hw i
        have := hT i (g i) hni
        rw [← this]
        exact (ladderWeight_congr hP D (S i) L γ η base roots z (hh i)
          (fun x hx => (hh1 i x hx).symm))
      have hgz : gl g = z := by
        apply bondIndex_injective G hP roots
        funext x
        show bondIndex G (gl g).1 x = bondIndex G z.1 x
        by_cases ha : G.molecule.atom x ∈ Uni S
        · obtain ⟨i, -, hi⟩ := mem_biUnion.mp ha
          rw [hgl1 g i x hi]
          exact hh1 i x hi
        · rw [hgl2 g x ha]
          exact (hAg x (not_intDart_of_atom_notMem S x ha)).symm
      refine ⟨g, hgT, ?_, hgz⟩
      rw [hgz]; exact hne
    · intro g _ _
      rfl
  rw [hsum]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  congr 1
  simp only [LamW]
  rw [Finset.prod_univ_sum]

/-- Pointwise (in the times) bound of the weighted fibre sums by the product of the weighted local lattice sums. -/
theorem fibre_norm_leW (hP : G.IsPlain) (D : SplicedKernelData G d) (hD : SplicedAmplitudeBounds G D)
    (S : ι → Finset (GBranch G.tree))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (hH : ∀ i, Disjoint (S i) D.hinges)
    {L : ℝ} (hL : 0 < L) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z₀ : GenDecoration G d roots 0) (Zc : Finset (GenDecoration G d roots 0))
    (φ : (GNode G.tree → (Fin d → ℤ)) → ℂ) (r : ℂ) (hr : ‖r‖ ≤ 1)
    (φi : ι → (GNode G.tree → (Fin d → ℤ)) → ℂ)
    (hφ : ∀ z : GenDecoration G d roots 0, AgreeOff S z z₀ → φ z.1 = r * ∏ i, φi i z.1)
    (hφi : ∀ i (z z' : GenDecoration G d roots 0),
      (∀ x, G.molecule.atom x ∈ S i → bondIndex G z.1 x = bondIndex G z'.1 x) → φi i z.1 = φi i z'.1)
    (hZ : ∀ z, AgreeOff S z z₀ → splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 → z ∈ Zc)
    (hZ' : ∀ z ∈ Zc, AgreeOff S z z₀)
    (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1)))
    (hT : ∀ i ζ, ζ ∉ T i → ladderWeight D (S i) L γ η base ζ.1.1 = 0)
    (t : GBranch G.tree → ℝ) :
    ‖∑ z ∈ Zc, φ z.1 * (splicedMomentumAmplitude G D L γ η base z.1 * globalPhase D L γ δ base z.1 t)‖ ≤
      ∏ i, ‖LamW D S φi L γ η δ base z₀ T i (fun v : S i => t v.1)‖ := by
  rw [fibre_factorW hP D S hS hH hL.ne' γ η δ base roots z₀ Zc φ r φi hφ hφi hZ hZ' T hT t, norm_mul, norm_mul, norm_mul]
  have h1 : ‖restAmp D S L γ η base z₀.1‖ ≤ 1 := norm_restAmp_le_one D hD S L γ η base z₀.1
  have h2 : ‖∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z₀.1 v * t v : ℝ) *
      Complex.I)‖ = 1 := by
    rw [norm_prod]
    exact Finset.prod_eq_one (fun v _ => Complex.norm_exp_ofReal_mul_I _)
  rw [h2, mul_one, norm_prod]
  have h3 : ‖r‖ * ‖restAmp D S L γ η base z₀.1‖ ≤ 1 := by
    calc _ ≤ 1 * 1 := mul_le_mul hr h1 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  exact mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) h3

end WaveTurbulence.Flower.FinalMKCrude
