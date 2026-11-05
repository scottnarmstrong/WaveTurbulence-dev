/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerIdentity
public import WaveTurbulence.Foundations.XChain.TreeLeafCard
public import WaveTurbulence.Foundations.XChain.TopTimePrefactorBounds
public import WaveTurbulence.Foundations.XChain.CplDraft.InputMoments

/-!
# X2E-1, step 5: the random flower kernel and its `2P`-th moments

**Statements.**
1. `flowerKernelGen_eq_flowerTerm`: X2's flower kernel `flowerKernelGen` (one flower tree, pattern, `†`, cutoffs) is
   the generic flower term with the coefficient `fkCoef = (prefactor) ε_κ · (weights) · (time integral)` (X3's
   `flowerKernelGen_eq`, `TIpat`). `norm_fkCoef_le`: `|fkCoef| ≤ 1` (X3's `norm_TIpat_le_one`,
   `abs_treeWeight_le_one`).
2. `randFlowerKernel_eq_famFlowerTerm`: the random kernel `𝒦` of `flowerest1` is the family `famFlowerTerm` over its
   flower trees `kernelTrees` (kind, flower sign `ζ`, valid pattern).
3. `integral_norm_famFlowerTerm_pow_eq`: for a finite family `S` of non-trivial flower trees of order `≤ M`, with
   `2P(2M+1) ≤ 2R_p`,
   `𝔼_p |famFlowerTerm|^{2P} = ∑_{(F_j) ∈ S^{2P}} ∑_Q (∑'_κ flowerKer + flowerError)`,
   with the alternating signs `altSig P` (`|z|^{2P} = ∏_{j<P} z ∏_{j<P} z̄`), roots `k` and flowers `k'`. Also
   `integrable_norm_famFlowerTerm_pow`.
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset MeasureTheory Filter Topology Induct SysAPI Cpl
open scoped ENNReal Classical

variable {d : ℕ}

/-! ## The flower kernel as a flower term -/

section Kernel

variable (L γ δ : ℝ) (p : ℕ) (pat : FixPat) (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ) (t s : ℝ)

/-- The coefficient of `flowerKernelGen`. -/
noncomputable def fkCoef (F : FTree) : TreeCoef d F.toTree := fun κ =>
  if hF : F = FTree.flower then 0 else
    treePrefactor L γ δ d F.toTree * (epsProd F.toTree κ * (treeWeight L F hF dagger cut1 cut2 κ : ℂ) *
      Fixedpt.TIpat L γ δ hF p (if dagger.isSome then {F.flowerParent hF} else ∅) κ pat t s)

theorem flowerKernelGen_eq_flowerTerm (F : FTree) (aP : (Fin d → ℤ) → ℂ) (k k' : Fin d → ℤ) :
    flowerKernelGen L γ δ p F aP pat dagger cut1 cut2 t s k k' =
      flowerTerm F (fkCoef L γ δ p pat dagger cut1 cut2 t s F) aP k k' := by
  by_cases hF : F = FTree.flower
  · have h0 : flowerKernelGen L γ δ p F aP pat dagger cut1 cut2 t s k k' = 0 := by
      unfold flowerKernelGen
      exact dite_eq_left hF
    rw [h0]
    unfold flowerTerm flowerSummand fkCoef
    simp [hF]
  · rw [Fixedpt.flowerKernelGen_eq L γ δ hF p aP pat dagger cut1 cut2 t s k k', ← tsum_mul_left]
    unfold flowerTerm flowerSummand fkCoef
    refine tsum_congr fun κ => ?_
    rw [dite_eq_right hF]
    ring

theorem norm_fkCoef_le (hc : |coupling d L γ δ| ≤ 1) (F : FTree) (κ : GNode (single F.toTree) → (Fin d → ℤ)) :
    ‖fkCoef L γ δ p pat dagger cut1 cut2 t s F κ‖ ≤ 1 := by
  unfold fkCoef
  by_cases hF : F = FTree.flower
  · rw [dite_eq_left hF, norm_zero]
    exact zero_le_one
  · rw [dite_eq_right hF, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := norm_treePrefactor_le_one L γ δ F.toTree hc
    have h2 := norm_epsProd_le F.toTree κ
    have h3 := Fixedpt.abs_treeWeight_le_one L hF dagger cut1 cut2 κ
    have h4 := Fixedpt.norm_TIpat_le_one L γ δ hF p (if dagger.isSome then {F.flowerParent hF} else ∅) κ pat t s
    calc _ ≤ 1 * (1 * 1 * 1) := mul_le_mul h1 (mul_le_mul (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one) h4
          (norm_nonneg _) (by positivity)) (by positivity) zero_le_one
      _ = 1 := by norm_num

/-- The flower trees of the random kernel: of kind `kind`, with flower sign `ζ` and a valid pattern. -/
noncomputable def kernelTrees (Ntr : ℕ) (kind : FlowerKind) (ζ : ℤˣ) : Finset FTree :=
  (kindTrees Ntr kind).filter (fun F => F.sign = ζ ∧ ∃ hF : F ≠ FTree.flower, treePatValid F hF pat)

/-- A family of flower terms. -/
noncomputable def famFlowerTerm (S : Finset FTree) (coefOf : (F : FTree) → TreeCoef d F.toTree)
    (b : (Fin d → ℤ) → ℂ) (k k' : Fin d → ℤ) : ℂ :=
  ∑ F ∈ S, flowerTerm F (coefOf F) b k k'

theorem randFlowerKernel_eq_famFlowerTerm (Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (kind : FlowerKind) (ζ : ℤˣ)
    (k k' : Fin d → ℤ) :
    randFlowerKernel L γ δ p Ntr aP kind pat dagger cut1 cut2 ζ t s k k' =
      famFlowerTerm (kernelTrees pat Ntr kind ζ) (fkCoef L γ δ p pat dagger cut1 cut2 t s) aP k k' := by
  unfold randFlowerKernel famFlowerTerm kernelTrees
  exact sum_congr rfl fun F _ => flowerKernelGen_eq_flowerTerm L γ δ p pat dagger cut1 cut2 t s F aP k k'

theorem ne_flower_of_mem_kernelTrees {Ntr : ℕ} {kind : FlowerKind} {ζ : ℤˣ} {F : FTree}
    (h : F ∈ kernelTrees pat Ntr kind ζ) : F ≠ FTree.flower := by
  obtain ⟨-, -, hF, -⟩ := mem_filter.mp h
  exact hF

end Kernel

/-! ## Non-trivial flower forests -/

theorem one_le_order_toTree {F : FTree} (hF : F ≠ FTree.flower) : 1 ≤ F.toTree.order := by
  cases F with
  | flower => exact absurd rfl hF
  | node i F T₁ T₂ =>
    simp only [FTree.toTree]
    split_ifs <;> simp [TTree.order]

theorem erase_flowerLeaf_nonempty {F : FTree} (hF : F ≠ FTree.flower) : (univ.erase F.flowerLeaf).Nonempty := by
  rw [← card_pos, card_erase_of_mem (mem_univ _), card_univ]
  have h := forest_card_leaves_eq (single F.toTree)
  simp only [Finset.univ_unique, Fin.default_eq_zero, sum_singleton] at h
  have h1 := one_le_order_toTree hF
  change 0 < Fintype.card (GLeaf (single F.toTree)) - 1
  have he : (single F.toTree : Fin 1 → TTree) 0 = F.toTree := rfl
  rw [he] at h
  omega

theorem nfLeaves_nonempty {w : ℕ} (tops : Fin w → FTree) (hF : ∀ j, tops j ≠ FTree.flower) (j₀ : Fin w) :
    (nfLeaves tops).Nonempty := by
  obtain ⟨ℓ, hℓ⟩ := erase_flowerLeaf_nonempty (hF j₀)
  exact ⟨singleLeafToForest (ftop tops) j₀ ℓ,
    (singleLeafToForest_mem_nfLeaves_iff tops j₀ ℓ).mpr (mem_erase.mp hℓ).1⟩

/-! ## The `2P`-th moments of a family -/

theorem zpowSign_sum {ι : Type*} (σ : ℤˣ) (s : Finset ι) (f : ι → ℂ) :
    zpowSign σ (∑ i ∈ s, f i) = ∑ i ∈ s, zpowSign σ (f i) := by
  unfold zpowSign
  split_ifs
  · rfl
  · exact map_sum _ _ _

/-- `|famFlowerTerm|^{2P}` as a sum over the `2P`-tuples of trees. -/
theorem norm_famFlowerTerm_pow_eq (S : Finset FTree) (coefOf : (F : FTree) → TreeCoef d F.toTree)
    (b : (Fin d → ℤ) → ℂ) (k k' : Fin d → ℤ) (Pm : ℕ) :
    (((‖famFlowerTerm S coefOf b k k'‖ ^ (2 * Pm) : ℝ)) : ℂ) =
      ∑ tops : Fin (Pm + Pm) → ↥S, ∏ j, zpowSign (altSig Pm j)
        (flowerTerm (tops j).1 (coefOf (tops j).1) b k k') := by
  rw [← prod_altSig]
  unfold famFlowerTerm
  rw [← sum_coe_sort S]
  simp_rw [zpowSign_sum]
  exact Fintype.prod_sum _

section Family

variable (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (g : (Fin P.d → ℤ) → Ω → ℂ) (hG : IsGaussianData μ g)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
    (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ)
    (ha : AnsatzAt P μ g a Fev R E Et p)
    (hrapid : ∀ ω ∈ Fev p, IsRapidDecay (initialCoeff P.L P.φin g ω))
    (hL : 1 ≤ P.L) (hδ : 0 < P.δ) (hsmall : P.δ ^ P.ν ≤ 1 / 2) (C : ℝ) (hC : 2 ≤ C)
    (hF : ∀ n, |inputsF P R p (latticePoint P.L n)| ≤
      C * jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)))
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2)
    (S : Finset FTree) (hS : ∀ F ∈ S, F ≠ FTree.flower) (M : ℕ) (hM : ∀ F ∈ S, F.toTree.order ≤ M)
    (coefOf : (F : FTree) → TreeCoef P.d F.toTree) (hcoef : ∀ F κ, ‖coefOf F κ‖ ≤ 1)
    (Pm : ℕ) (hPm : 1 ≤ Pm) (hNR : (Pm + Pm) * (2 * M + 1) ≤ 2 * P.R p)

include hM hNR in
theorem tuple_nfLeaves_card_le (tops : Fin (Pm + Pm) → ↥S) :
    (nfLeaves (fun j => (tops j).1)).card ≤ 2 * P.R p :=
  (nfLeaves_card_le (fun j => (tops j).1) (fun j => hM _ (tops j).2)).trans hNR

include hS hPm in
theorem tuple_nfLeaves_nonempty (tops : Fin (Pm + Pm) → ↥S) : (nfLeaves (fun j => (tops j).1)).Nonempty :=
  nfLeaves_nonempty (fun j => (tops j).1) (fun j => hS _ (tops j).2) ⟨0, by omega⟩

include hG ha hrapid hL hδ hsmall hC hF hΛ hS hM hcoef hPm hNR in
theorem integrable_norm_famFlowerTerm_pow (k k' : Fin P.d → ℤ) :
    Integrable (fun ω => ‖famFlowerTerm S coefOf (a ω p) k k'‖ ^ (2 * Pm)) (μ.restrict (Fev p)) := by
  have hc : Integrable (fun ω => (((‖famFlowerTerm S coefOf (a ω p) k k'‖ ^ (2 * Pm) : ℝ)) : ℂ))
      (μ.restrict (Fev p)) := by
    simp_rw [norm_famFlowerTerm_pow_eq]
    exact integrable_finsetSum _ fun tops _ =>
      integrable_prod_flowerTerms P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
        (fun j => (tops j).1) (fun j => coefOf (tops j).1) (fun j => hcoef _) (altSig Pm)
        (tuple_nfLeaves_nonempty S hS Pm hPm tops) (tuple_nfLeaves_card_le P p S M hM Pm hNR tops)
        (fun _ => k) (fun _ => k')
  exact hc.re.congr (ae_of_all _ fun ω => Complex.ofReal_re _)

include hG ha hrapid hL hδ hsmall hC hF hΛ hS hM hcoef hPm hNR in
/-- **The `2P`-th moment identity of a family of flower terms, under `AnsatzAt`.** -/
theorem integral_norm_famFlowerTerm_pow_eq (k k' : Fin P.d → ℤ) :
    (((∫ ω in Fev p, ‖famFlowerTerm S coefOf (a ω p) k k'‖ ^ (2 * Pm) ∂μ : ℝ)) : ℂ) =
      ∑ tops : Fin (Pm + Pm) → ↥S, ∑ Q : Finpartition (nfLeaves (fun j => (tops j).1)),
        ((∑' κ : FlowerForestDec (fun j => (tops j).1) P.d (fun _ => k) (fun _ => k'),
            flowerKerIntegrand P.L P.γ P.δ (inputsF P R) (altSig Pm) (fun j => (tops j).1)
              (fun j => coefOf (tops j).1) Q p (P.N p) κ) +
          flowerError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) (altSig Pm) (fun j => (tops j).1)
            (fun j => coefOf (tops j).1) Q (fun ω => a ω p) p (P.N p) (fun _ => k) (fun _ => k')) := by
  have hI (tops : Fin (Pm + Pm) → ↥S) : Integrable (fun ω => ∏ j, zpowSign (altSig Pm j)
      (flowerTerm (tops j).1 (coefOf (tops j).1) (a ω p) k k')) (μ.restrict (Fev p)) :=
    integrable_prod_flowerTerms P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
      (fun j => (tops j).1) (fun j => coefOf (tops j).1) (fun j => hcoef _) (altSig Pm)
      (tuple_nfLeaves_nonempty S hS Pm hPm tops) (tuple_nfLeaves_card_le P p S M hM Pm hNR tops)
      (fun _ => k) (fun _ => k')
  have h1 : (fun ω => (((‖famFlowerTerm S coefOf (a ω p) k k'‖ ^ (2 * Pm) : ℝ)) : ℂ)) =
      fun ω => ∑ tops : Fin (Pm + Pm) → ↥S, ∏ j, zpowSign (altSig Pm j)
        (flowerTerm (tops j).1 (coefOf (tops j).1) (a ω p) k k') :=
    funext fun ω => norm_famFlowerTerm_pow_eq S coefOf (a ω p) k k' Pm
  rw [← integral_complex_ofReal, h1, integral_finsetSum _ fun tops _ => hI tops]
  refine sum_congr rfl fun tops _ => ?_
  have h := integral_prod_flowerTerms_eq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
    (fun j => (tops j).1) (fun j => coefOf (tops j).1) (fun j => hcoef _) (altSig Pm)
    (tuple_nfLeaves_nonempty S hS Pm hPm tops) (tuple_nfLeaves_card_le P p S M hM Pm hNR tops)
    (fun _ => k) (fun _ => k')
  exact h

end Family

end WaveTurbulence.X2E
