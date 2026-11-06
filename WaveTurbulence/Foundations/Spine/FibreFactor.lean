/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue
/-! # Factorisation of a fibre sum over disjoint ladders (S3c) -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay Finset
open scoped Classical

variable {w d : ℕ} {G : Garden w} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The global time phase of a decoration. -/
noncomputable def globalPhase (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (t : GBranch G.tree → ℝ) : ℂ :=
  ∏ v : GBranch G.tree, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z v * t v : ℝ) * Complex.I)

/-- The local lattice sum of the `i`-th ladder at fixed times. -/
noncomputable def Lam (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (L γ η δ : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)} (z₀ : GenDecoration G d roots 0)
    (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1))) (i : ι)
    (s : S i → ℝ) : ℂ :=
  ∑ ζ ∈ T i, ladderWeight D (S i) L γ η base ζ.1.1 * ladderPhase D (S i) L γ δ base ζ.1.1 s

theorem globalPhase_factor (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (t : GBranch G.tree → ℝ) :
    globalPhase D L γ δ base z t =
      (∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z v * t v : ℝ) * Complex.I)) *
        ∏ i, ladderPhase D (S i) L γ δ base z (fun v : S i => t v.1) := by
  unfold globalPhase
  simp_rw [ladderPhase_eq_prod]
  rw [← Finset.prod_biUnion (pairwiseDisjoint_S (G := G) S hS)]
  rw [← Uni]
  exact (Finset.prod_sdiff (Finset.subset_univ (Uni S))).symm

/-- **Fibre factorisation.** -/
theorem fibre_factor (hP : G.IsPlain) (D : SplicedKernelData G d) (S : ι → Finset (GBranch G.tree))
    (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j)) (hH : ∀ i, Disjoint (S i) D.hinges)
    {L : ℝ} (hL : L ≠ 0) (γ η δ : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z₀ : GenDecoration G d roots 0) (Zc : Finset (GenDecoration G d roots 0))
    (hZ : ∀ z, AgreeOff S z z₀ → splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 → z ∈ Zc)
    (hZ' : ∀ z ∈ Zc, AgreeOff S z z₀)
    (T : ∀ i, Finset ↥(localLadderDecorations G (S i) roots (bondIndex G z₀.1)))
    (hT : ∀ i ζ, ζ ∉ T i → ladderWeight D (S i) L γ η base ζ.1.1 = 0)
    (t : GBranch G.tree → ℝ) :
    ∑ z ∈ Zc, splicedMomentumAmplitude G D L γ η base z.1 * globalPhase D L γ δ base z.1 t =
      (restAmp D S L γ η base z₀.1 *
        ∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z₀.1 v * t v : ℝ) * Complex.I)) *
        ∏ i, Lam D S L γ η δ base z₀ T i (fun v : S i => t v.1) := by
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
  have hterm : ∀ g, splicedMomentumAmplitude G D L γ η base (gl g).1 *
      globalPhase D L γ δ base (gl g).1 t =
      (restAmp D S L γ η base z₀.1 *
        ∏ v ∈ univ \ Uni S, Complex.exp ((Real.pi * splicedFrequency G D L γ δ base z₀.1 v * t v : ℝ) * Complex.I)) *
      ∏ i, (ladderWeight D (S i) L γ η base (g i).1.1 *
        ladderPhase D (S i) L γ δ base (g i).1.1 (fun v : S i => t v.1)) := by
    intro g
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
    simp_rw [h1, h2]
    rw [h3, Finset.prod_mul_distrib]
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
  have hsum : ∑ z ∈ Zc, splicedMomentumAmplitude G D L γ η base z.1 * globalPhase D L γ δ base z.1 t =
      ∑ g ∈ Fintype.piFinset T, splicedMomentumAmplitude G D L γ η base (gl g).1 *
        globalPhase D L γ δ base (gl g).1 t := by
    symm
    refine Finset.sum_bij_ne_zero (fun g _ _ => gl g) ?_ ?_ ?_ ?_
    · intro g _ hne
      apply hZ _ (hgl3 g)
      intro h0
      apply hne
      rw [h0, zero_mul]
    · intro g _ _ g' _ _ h
      exact hinj g g' h
    · intro z hz hne
      have hAg := hZ' z hz
      have hm : splicedMomentumAmplitude G D L γ η base z.1 ≠ 0 := by
        intro h0; apply hne; rw [h0, zero_mul]
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
              simp only [if_true]
              exact hAg x (fun ⟨k, hk⟩ => by
                by_cases hkj : k = j
                · subst hkj; exact hxn hk
                · exact Finset.disjoint_left.mp (hS k j hkj) hk.1 hxj)
            · simp only [hji, if_false])
        refine ⟨h, fun x hx => by rw [h1 i x hx]; simp, fun x hx => ?_⟩
        by_cases ha : G.molecule.atom x ∈ Uni S
        · obtain ⟨j, -, hj⟩ := mem_biUnion.mp ha
          rw [h1 j x hj]
          by_cases hji : j = i
          · subst hji
            simp only [if_true]
            exact hAg x (fun ⟨k, hk⟩ => by
              by_cases hkj : k = j
              · subst hkj; exact hx hk
              · exact Finset.disjoint_left.mp (hS k j hkj) hk.1 hj)
          · simp only [hji, if_false]
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
  simp only [Lam]
  rw [Finset.prod_univ_sum]

end WaveTurbulence.CoarseSpliced
