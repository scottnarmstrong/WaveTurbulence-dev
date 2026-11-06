/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FrechetDecay
public import WaveTurbulence.Foundations.Spine.LeafwiseMajorant
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
/-! Summable local majorants for every derivative of the finite leaf product. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Finset

noncomputable def leafJetMajorant {w d : ℕ} (L : ℝ) (LG : LayeredGarden w)
    (C : (Fin w × TTree.Path) → NNReal) (A : ℕ) (k₀ : Mom d)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) : ℝ :=
  ∏ l ∈ inputLeaves LG.garden,
    ((d : ℝ) ^ A * (C l.1 : ℝ) * (Real.sqrt 2 * (2 + ‖k₀‖)) ^ (d + 1)) *
      jbr (latticePoint L (κ.1 l.toNode)) ^ (-((d : ℝ) + 1))

theorem summable_leafJetMajorant {w d : ℕ} {L : ℝ} (hL : 1 ≤ L) (LG : LayeredGarden w)
    (C : (Fin w × TTree.Path) → NNReal) (A : ℕ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1) :
    Summable (leafJetMajorant L LG C A k₀ (nroot := nroot) (nfl := nfl)) := by
  classical
  let ι := {l : GLeaf LG.garden.tree // l ∈ inputLeaves LG.garden}
  let f : ι → (Fin d → ℤ) → ℝ := fun l z =>
    ((d : ℝ) ^ A * (C l.1.1 : ℝ) * (Real.sqrt 2 * (2 + ‖k₀‖)) ^ (d + 1)) *
      jbr (latticePoint L z) ^ (-((d : ℝ) + 1))
  have hf : Summable (fun z : ι → (Fin d → ℤ) => ∏ l, f l (z l)) :=
    summable_pi_prod f (fun l z => by
      dsimp only [f]
      apply mul_nonneg
      · exact mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) A) (NNReal.coe_nonneg _))
          (pow_nonneg (by positivity) _)
      · exact Real.rpow_nonneg (jbr_pos _).le _)
      (fun l => (summable_jbr_rpow_neg hL).mul_left _)
  have h := hf.comp_injective (genDecoration_input_injective LG nroot nfl hlone)
  apply h.congr
  intro κ
  unfold leafJetMajorant
  rw [← prod_coe_sort]
  rfl

/-- The finite combinatorial coefficient is only used for local smoothness, not for the
oscillatory decay estimate. All momentum dependence remains in a summable product. -/
noncomputable def leafLeibnizCount {w : ℕ} (LG : LayeredGarden w) (r : ℕ) : ℝ :=
  ∑ p ∈ (inputLeaves LG.garden).sym r, ((p : Multiset (GLeaf LG.garden.tree)).countPerms : ℝ)

theorem norm_leafProduct_frechet_le {w d A B r : ℕ} (hd : 1 ≤ d) (hB : d + 1 ≤ B)
    (L : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (C : (Fin w × TTree.Path) → NNReal)
    (hcont : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ A (fun x => (H l.1 x : ℂ)))
    (hbound : ∀ l ∈ inputLeaves LG.garden, SNormR A B (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ))
    (hr : r ≤ A) (k k₀ : Mom d) (hk : k ∈ Metric.closedBall k₀ 1)
    {nroot : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration LG.garden d nroot nfl) :
    ‖iteratedFDeriv ℝ r (fun x => ∏ l ∈ inputLeaves LG.garden,
      (H l.1 (x + latticePoint L (κ.1 l.toNode)) : ℂ)) k‖ ≤
      leafLeibnizCount LG r * leafJetMajorant L LG C A k₀ κ := by
  classical
  let f : GLeaf LG.garden.tree → Mom d → ℂ :=
    fun l x => (H l.1 (x + latticePoint L (κ.1 l.toNode)) : ℂ)
  have hf : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ A (f l) := by
    intro l hl
    exact (hcont l hl).comp (contDiff_id.add contDiff_const)
  have he := norm_iteratedFDeriv_prod_le (𝕜 := ℝ) hf (n := r) (x := k) (by exact_mod_cast hr)
  apply he.trans
  change (∑ p ∈ (inputLeaves LG.garden).sym r,
      ((p : Multiset (GLeaf LG.garden.tree)).countPerms : ℝ) *
        ∏ l ∈ inputLeaves LG.garden, ‖iteratedFDeriv ℝ ((p : Multiset _).count l) (f l) k‖) ≤ _
  unfold leafLeibnizCount
  rw [sum_mul]
  apply sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold leafJetMajorant
  apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro l hl
  have hp : (p : Multiset (GLeaf LG.garden.tree)).count l ≤ A :=
    ((Multiset.count_le_card l (p : Multiset _)).trans_eq (show (p : Multiset (GLeaf LG.garden.tree)).card = r from Sym.card_coe)).trans hr
  dsimp only [f]
  let g : Mom d → ℂ := fun x => (H l.1 x : ℂ)
  change ‖iteratedFDeriv ℝ ((p : Multiset _).count l)
    (fun x => g (x + latticePoint L (κ.1 l.toNode))) k‖ ≤ _
  rw [iteratedFDeriv_comp_add_right (f := g)]
  exact local_frechet_coset_bound hd hB _ (hcont l hl) _ (NNReal.coe_nonneg _)
    (hbound l hl) hp L k k₀ hk (κ.1 l.toNode)

end WaveTurbulence.LGSpine
