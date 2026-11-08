/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.FinalMKCrude.Classes
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Crude

/-! # C2 FINALMK-CRUDE: the atom weight factors over a ladder family

`atomW = (∏ a, filtFac a) * ind`. Off the ladders, the factors are constant along a class (they read only bond
labels at non-ladder atoms and at the atoms of `split`); on the ladders they are local. Also a fixed Schwartz
bump equal to `1` on `[-1, 1]` (for unfiltered ladder atoms). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Flower.FinalMKCrude
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDecay WaveTurbulence.CoarseSpliced
  WaveTurbulence.FlowerP5 Finset MeasureTheory Set
open WaveTurbulence.Flower.MkDefs (SplicedKernelDataMK splicedKernelMK splicedTimeIntegralMK)
open scoped Classical

/-- A Schwartz function equal to `1` on `[-1, 1]`. -/
theorem exists_bump : ∃ ψ₀ : SchwartzMap ℝ ℂ, ∀ x : ℝ, |x| ≤ 1 → ψ₀ x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc : HasCompactSupport (fun x : ℝ => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => ((b x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (b.contDiff)
  refine ⟨hc.toSchwartzMap hs, fun x hx => ?_⟩
  change ((b x : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (by simpa [Metric.mem_closedBall, b] using hx)]
  simp

variable {w d : ℕ} {G : Garden w}

/-- The factor of one atom in `atomW`. -/
noncomputable def filtFac (D : SplicedKernelDataMK G d) (k : GNode G.tree → Mom d) (a : GBranch G.tree) : ℂ :=
  (D.filt a).elim 1 fun q => q.2 (omegaNode G k a / q.1)

theorem atomW_eq (D : SplicedKernelDataMK G d) (k : GNode G.tree → Mom d) :
    D.atomW k = (∏ a : GBranch G.tree, filtFac D k a) * (D.ind k : ℂ) := rfl

theorem norm_filtFac_le (D : SplicedKernelDataMK G d) (hq : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1)
    (k : GNode G.tree → Mom d) (a : GBranch G.tree) : ‖filtFac D k a‖ ≤ 1 := by
  unfold filtFac
  cases h : D.filt a with
  | none => simp
  | some q => exact hq a q h _

theorem omegaNode_congr {roots : Fin w → (Fin d → ℤ)} (hP : G.IsPlain) (L : ℝ) (base : Mom d)
    (z z' : GenDecoration G d roots 0) (a : GBranch G.tree)
    (h : ∀ x, G.molecule.atom x = a → bondIndex G z.1 x = bondIndex G z'.1 x) :
    omegaNode G (cosetDecoration G L base z.1) a = omegaNode G (cosetDecoration G L base z'.1) a := by
  obtain ⟨hr, h0, h1, h2⟩ := slot_eq_of_atom hP roots z z' a h
  unfold omegaNode resFactor cosetDecoration
  rw [hr, h0, h1, h2]

/-- The local weight of the `i`-th ladder. -/
noncomputable def ladW (D : SplicedKernelDataMK G d) (S : Finset (GBranch G.tree)) (L : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) : ℂ :=
  ∏ a ∈ S, filtFac D (cosetDecoration G L base z) a

theorem ladW_congr {roots : Fin w → (Fin d → ℤ)} (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (S : Finset (GBranch G.tree)) (L : ℝ) (base : Mom d) (z z' : GenDecoration G d roots 0)
    (h : ∀ x, G.molecule.atom x ∈ S → bondIndex G z.1 x = bondIndex G z'.1 x) :
    ladW D S L base z.1 = ladW D S L base z'.1 := by
  unfold ladW
  refine Finset.prod_congr rfl (fun a ha => ?_)
  unfold filtFac
  rw [omegaNode_congr hP L base z z' a (fun x hx => h x (by rw [hx]; exact ha))]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The factorisation of `atomW` along a fibre of the class map. -/
theorem atomW_factor {roots : Fin w → (Fin d → ℤ)} (hP : G.IsPlain) (D : SplicedKernelDataMK G d)
    (S : ι → Finset (GBranch G.tree)) (hS : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (split : Finset (GBranch G.tree)) (hsplit : ∀ a ∈ split, a ∉ Uni S)
    (hind : ∀ k k' : GNode G.tree → Mom d,
      (∀ a ∈ split, ∀ i : Fin 3, k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → D.ind k = D.ind k')
    (L : ℝ) (base : Mom d) (z₀ : GenDecoration G d roots 0) :
    ∀ z : GenDecoration G d roots 0, AgreeOff S z z₀ →
      D.atomW (cosetDecoration G L base z.1) =
        ((∏ a ∈ univ \ Uni S, filtFac D (cosetDecoration G L base z₀.1) a) *
          (D.ind (cosetDecoration G L base z₀.1) : ℂ)) * ∏ i, ladW D (S i) L base z.1 := by
  intro z hAg
  have hout : ∀ a, a ∉ Uni S → ∀ x, G.molecule.atom x = a → bondIndex G z.1 x = bondIndex G z₀.1 x := by
    intro a ha x hx
    exact hAg x (not_intDart_of_atom_notMem S x (by rw [hx]; exact ha))
  rw [atomW_eq, ← Finset.prod_sdiff (Finset.subset_univ (Uni S))]
  have h1 : ∏ a ∈ univ \ Uni S, filtFac D (cosetDecoration G L base z.1) a =
      ∏ a ∈ univ \ Uni S, filtFac D (cosetDecoration G L base z₀.1) a := by
    refine Finset.prod_congr rfl (fun a ha => ?_)
    unfold filtFac
    rw [omegaNode_congr hP L base z z₀ a (hout a (Finset.mem_sdiff.mp ha).2)]
  have h2 : D.ind (cosetDecoration G L base z.1) = D.ind (cosetDecoration G L base z₀.1) := by
    refine hind _ _ (fun a ha i => ?_)
    obtain ⟨hr, h0, h1, h2⟩ := slot_eq_of_atom hP roots z z₀ a (hout a (hsplit a ha))
    unfold cosetDecoration
    fin_cases i
    · exact ⟨by simp [h0], by simp [hr]⟩
    · exact ⟨by simp [h1], by simp [hr]⟩
    · exact ⟨by simp [h2], by simp [hr]⟩
  have h3 : ∏ a ∈ Uni S, filtFac D (cosetDecoration G L base z.1) a = ∏ i, ladW D (S i) L base z.1 := by
    unfold Uni ladW
    rw [Finset.prod_biUnion (pairwiseDisjoint_S (G := G) S hS)]
  rw [h1, h2, h3]
  ring

theorem norm_rest_le_one (D : SplicedKernelDataMK G d) (hq : ∀ a q, D.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1)
    (hi : ∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) (S : Finset (GBranch G.tree)) (k : GNode G.tree → Mom d) :
    ‖(∏ a ∈ S, filtFac D k a) * (D.ind k : ℂ)‖ ≤ 1 := by
  rw [norm_mul, norm_prod]
  have h1 : ∏ a ∈ S, ‖filtFac D k a‖ ≤ 1 :=
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun a _ => norm_filtFac_le D hq k a)).trans (by simp)
  have h2 : ‖(D.ind k : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hi k).1]; exact (hi k).2
  calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end WaveTurbulence.Flower.FinalMKCrude
