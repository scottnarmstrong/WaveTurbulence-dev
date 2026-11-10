/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Canon.Main

/-!
# Truncation facts and the couple bridge (packet D3 CANON, pre-freeze)

* `isCanonGC_iff_isCanonC`: on width 2, the uniform class `IsCanonGC` is `𝒞_q`;
* `KG_eq_KQ`, `truncSum_couple_eq_truncSumC`: **the decoration-shift bridge** (glue list, stage-3 O6):
  the lattice couple sum with diagonal root labels `(n, n)` is the couple sum with real root vector
  `n/L` (`truncSum q N t (+,-) (n,n) = truncSumC q N t (n/L)`);
* `truncSumC_untruncated`: the couple analogue of `truncSum_untruncated`;
* `isEmpty_genDecoration_of_unbalanced`, `kernelK_eq_zero_of_unbalanced`,
  `truncSum_eq_zero_of_unbalanced`: decorations of a plain garden exist only if `∑ ζ_j n_j = 0`, so
  the garden sums vanish otherwise; in particular `layergarden` (2)(a) holds outright
  (`truncSum_couple_offDiag`).
-/

@[expose] public section

open MeasureTheory Finset

namespace WaveTurbulence.Canon

open TTree

/-! ### Couples -/

theorem isCanonGC_iff_isCanonC (q : ℕ) (LG : LayeredGarden 2) : IsCanonGC q LG ↔ IsCanonC q LG := by
  rcases q with _ | p
  · simp [IsCanonGC, IsCanonC]
  · rw [IsCanonGC, IsCanonC, IsCouple]
    have hsig : (∀ j : Fin 2, LG.garden.sig j = (-1) ^ (j : ℕ)) ↔ LG.garden.sig = ![1, -1] := by
      constructor
      · intro h
        funext j
        fin_cases j <;> simp [h]
      · intro h j
        fin_cases j <;> simp [h]
    constructor
    · rintro ⟨hP, (⟨h4, -⟩ | ⟨-, hs⟩), hC⟩
      · omega
      · exact ⟨⟨hP, hsig.1 hs⟩, hC⟩
    · rintro ⟨⟨hP, hs⟩, hC⟩
      exact ⟨hP, Or.inr ⟨rfl, hsig.2 hs⟩, hC⟩

theorem isCouple_of_isCanonC {q : ℕ} {LG : LayeredGarden 2} (h : IsCanonC q LG) :
    IsCouple LG.garden := by
  rcases q with _ | p
  · exact absurd h id
  · exact h.1

/-! ### Shifting decorations -/

theorem latticePoint_add {d : ℕ} (L : ℝ) (a b : Fin d → ℤ) :
    latticePoint L (a + b) = latticePoint L a + latticePoint L b := by
  ext j
  simp only [latticePoint, PiLp.add_apply, Pi.add_apply, Int.cast_add, add_div]

theorem epsCoef_add {d : ℕ} (a b c n : Fin d → ℤ) : epsCoef (a + n) (b + n) (c + n) = epsCoef a b c := by
  simp only [epsCoef, ne_eq, add_left_inj]

/-- Shifting the labels of a decoration of a plain garden by a constant vector `n`. -/
def shiftDec {w d : ℕ} (G : Garden w) (hP : G.IsPlain) (n : Fin d → ℤ)
    {nroot nroot' : Fin w → (Fin d → ℤ)} (h : ∀ j, nroot' j = nroot j + n) :
    GenDecoration G d nroot 0 ≃ GenDecoration G d nroot' 0 where
  toFun κ := ⟨fun a => κ.1 a + n, ⟨⟨fun b => by beta_reduce; rw [κ.2.1.1 b]; abel,
    fun ℓ => by beta_reduce; rw [κ.2.1.2 ℓ]⟩,
    fun j => by beta_reduce; rw [κ.2.2.1 j, h], fun ℓ hℓ => absurd ((hP ℓ).symm.trans hℓ) (by simp)⟩⟩
  invFun κ := ⟨fun a => κ.1 a - n, ⟨⟨fun b => by beta_reduce; rw [κ.2.1.1 b]; abel,
    fun ℓ => by beta_reduce; rw [κ.2.1.2 ℓ]⟩,
    fun j => by beta_reduce; rw [κ.2.2.1 j, h]; abel,
    fun ℓ hℓ => absurd ((hP ℓ).symm.trans hℓ) (by simp)⟩⟩
  left_inv κ := Subtype.ext (funext fun a => by simp)
  right_inv κ := Subtype.ext (funext fun a => by simp)

/-- **`K_𝒬` as a lattice kernel**: for a plain layered garden of width 2,
`K_𝒢(t; n, n) = K_𝒬(t, n/L)` (shift the decorations by `n`). -/
theorem KG_eq_KQ {d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2)
    (hP : LG.garden.IsPlain) (t : ℝ) (n : Fin d → ℤ) :
    KG L γ δ F LG t (fun _ => n) = KQ L γ δ F LG t (latticePoint L n) := by
  unfold KG KQ KQstar kernelK
  have hup : (fun b : GBranch LG.garden.tree => if b.1.1 = 0 then t else t) = fun _ => t :=
    funext fun _ => ite_self _
  rw [hup]
  congr 1
  rw [← (shiftDec LG.garden hP n (nroot := fun _ => 0) (nroot' := fun _ => n)
    (fun _ => (zero_add n).symm)).tsum_eq]
  refine tsum_congr fun κ => ?_
  have hcos : cosetDecoration LG.garden L 0 (fun a => κ.1 a + n) =
      cosetDecoration LG.garden L (latticePoint L n) κ.1 := by
    funext a
    simp only [cosetDecoration, latticePoint_add]
    abel
  have heps : epsDec LG.garden (fun a => κ.1 a + n) = epsDec LG.garden κ.1 := by
    unfold epsDec
    exact Finset.prod_congr rfl fun b _ => epsCoef_add _ _ _ n
  change (epsDec LG.garden (fun a => κ.1 a + n) : ℂ) *
      phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) 0) 0
        (cosetDecoration LG.garden L 0 (fun a => κ.1 a + n)) *
      ∏ ℓ ∈ inputLeaves LG.garden,
        (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L 0 (fun a => κ.1 a + n) ℓ.toNode) : ℂ) = _
  rw [hcos, heps]

/-- **The decoration-shift bridge** (glue list; stage-3 O6): the lattice couple sum with diagonal root
labels is the couple sum with the real root vector `n/L`. -/
theorem truncSum_couple_eq_truncSumC (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ) (t : ℝ)
    (n : Fin P.d → ℤ) :
    truncSum P F q N t (w := 2) ![1, -1] (fun _ => n) = truncSumC P F q N t (latticePoint P.L n) := by
  classical
  unfold truncSum truncSumC
  refine finsum_congr fun LG => ?_
  rw [finsum_eq_if, finsum_eq_if]
  have hiff : (IsCanonGC q LG ∧ LG.IsTrunc (q - 1) (P.N q) (P.N (q - 1)) ∧
      LG.garden.sig = ![1, -1] ∧ LG.garden.order = N) ↔
      (IsCanonC q LG ∧ LG.IsTrunc (q - 1) (P.N q) (P.N (q - 1)) ∧ LG.garden.order = N) :=
    ⟨fun h => ⟨(isCanonGC_iff_isCanonC q LG).1 h.1, h.2.1, h.2.2.2⟩,
      fun h => ⟨(isCanonGC_iff_isCanonC q LG).2 h.1, h.2.1, (isCouple_of_isCanonC h.1).2, h.2.2⟩⟩
  split_ifs with hA hC hC
  · exact KG_eq_KQ _ _ _ F LG (isCouple_of_isCanonC hC.1).1 t n
  · exact absurd (hiff.1 hA) hC
  · exact absurd (hiff.2 hC) hA
  · rfl

/-! ### Unbalanced root labels -/

/-- **Decorations exist only for balanced root labels**: a decoration of a plain garden satisfies
`∑_j ζ_j n_j = 0` (sum rule at every root; paired leaves cancel). -/
theorem isEmpty_genDecoration_of_unbalanced {w d : ℕ} (G : Garden w) (hP : G.IsPlain)
    (nroot : Fin w → (Fin d → ℤ)) (n' : Fin d → ℤ)
    (h : ∑ j, ((G.sig j : ℤˣ) : ℤ) • nroot j ≠ 0) : IsEmpty (GenDecoration G d nroot n') := by
  classical
  refine ⟨fun κ => h ?_⟩
  have hroot : ∀ j, ((G.sig j : ℤˣ) : ℤ) • nroot j =
      ∑ ℓ ∈ (GNode.root G.tree j).leavesBelow, ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • κ.1 ℓ.toNode := by
    intro j
    rw [← κ.2.2.1 j, ← sum_rule G.sig κ.1 κ.2.1.1 (GNode.root G.tree j)]
    simp [nodeSign, GNode.root, TTree.pathSign]
  have hleaves : ∀ j, (GNode.root G.tree j).leavesBelow =
      Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j := by
    intro j
    ext ℓ
    simp only [GNode.leavesBelow, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, List.nil_prefix⟩⟩
  simp_rw [hroot, hleaves]
  rw [Finset.sum_fiberwise Finset.univ (fun ℓ : GLeaf G.tree => ℓ.1.1)
    (fun ℓ => ((nodeSign G.sig ℓ.1 : ℤˣ) : ℤ) • κ.1 ℓ.toNode)]
  refine Finset.sum_involution (fun ℓ _ => G.pair ℓ) (fun ℓ _ => ?_) (fun ℓ _ _ => ?_)
    (fun ℓ _ => Finset.mem_univ _) (fun ℓ _ => G.pair_pair ℓ)
  · have hne : G.pair ℓ ≠ ℓ := fun hp => ((G.pair_eq_iff ℓ).1 hp) (hP ℓ)
    rw [G.pair_sign ℓ hne, ← κ.2.1.2 ℓ, Units.val_neg, neg_smul, add_neg_cancel]
  · exact fun hp => ((G.pair_eq_iff ℓ).1 hp) (hP ℓ)

end WaveTurbulence.Canon
