/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerGateSum

/-!
# X2E-3: the `2P`-th moment of `𝒦` as B1.12's flower sums

**Width `2P`.** `prod_altFlowerSig`: `∏_{j < 2P} z^{(−1)^j} = |z|^{2P}`; X2E-1's moment identity restated with the
gate's signature `altFlowerSig` on `Fin (2P)` (`integral_norm_randK_pow_eqW`).

**Orders.** `flowerSum_eq_finsum`: B1.12's `flowerSum_N` (constant pattern and `†` labels) is the gate garden sum
restricted to order `N`; `sum_flowerSum_eq`: `∑_{N ≤ M} flowerSum_N` is the index sum over orders `≤ M`.

**Statement** (`integral_norm_randK_pow_eq_flowerSum`, patterns `plain`/`dRoot`, `p ≤ s, t`, cutoff weights
identified):
`𝔼_p|𝒦|^{2P} = ∑_{N ≤ M} flowerSum_N + flowerTail_M + flowerErr`, where `flowerTail_M` is the index sum over the
flower gardens of order `> M` and `flowerErr = ∑_{(F_j)} ∑_Q flowerError` is X2E-1's input error.
-/

@[expose] public section

open WaveTurbulence.X2E
namespace WaveTurbulence.X2E

open Finset MeasureTheory Induct SysAPI Cpl
open scoped Classical

/-! ## Width `2P` -/

theorem prod_altFlowerSig (q : ℕ) (z : ℂ) :
    ∏ j : Fin (2 * q), zpowSign (altFlowerSig q j) z = ((‖z‖ ^ (2 * q) : ℝ) : ℂ) := by
  let e : Fin q × Fin 2 ≃ Fin (2 * q) := finProdFinEquiv.trans (finCongr (mul_comm q 2))
  have hv : ∀ x : Fin q × Fin 2, ((e x : Fin (2 * q)) : ℕ) = x.2 + 2 * x.1 := fun x => by
    simp [e, finProdFinEquiv_apply_val]
  have hs : ∀ x : Fin q × Fin 2, altFlowerSig q (e x) = (-1) ^ (x.2 : ℕ) := fun x => by
    change (-1 : ℤˣ) ^ ((e x : Fin (2 * q)) : ℕ) = _
    rw [hv, pow_add, pow_mul]
    simp
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hpair : ∀ a : Fin q, ∏ b : Fin 2, zpowSign (altFlowerSig q (e (a, b))) z = z * (starRingEnd ℂ) z := by
    intro a
    rw [Fin.prod_univ_two, hs, hs]
    simp [zpowSign, hne]
  rw [← e.prod_comp, Fintype.prod_prod_type]
  simp only [hpair, prod_const, card_univ, Fintype.card_fin]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
  push_cast
  rfl

/-- `|famFlowerTerm|^{2P}` as a sum over the `2P`-tuples of trees, with the signature `(−1)^j`. -/
theorem norm_famFlowerTerm_pow_eqW {d : ℕ} (S : Finset FTree) (coefOf : (F : FTree) → TreeCoef d F.toTree)
    (b : (Fin d → ℤ) → ℂ) (k k' : Fin d → ℤ) (Pm : ℕ) :
    (((‖famFlowerTerm S coefOf b k k'‖ ^ (2 * Pm) : ℝ)) : ℂ) =
      ∑ tops : Fin (2 * Pm) → ↥S, ∏ j, zpowSign (altFlowerSig Pm j)
        (flowerTerm (tops j).1 (coefOf (tops j).1) b k k') := by
  rw [← prod_altFlowerSig]
  unfold famFlowerTerm
  rw [← sum_coe_sort S]
  simp_rw [zpowSign_sum]
  exact Fintype.prod_sum _

section RandKW

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
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2) (hc : |coupling P.d P.L P.γ P.δ| ≤ 1)
    (kind : FlowerKind) (pat : FixPat) (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ)
    (t s : ℝ) (n n' : Fin P.d → ℤ) (Pm : ℕ) (hPm : 1 ≤ Pm)
    (hNR : (2 * Pm) * (2 * (3 * P.N (p + 1) + 1) + 1) ≤ 2 * P.R p)

include hG ha hrapid hL hδ hsmall hC hF hΛ hc hPm hNR in
/-- **X2E-1 at width `2P`**: the `2P`-th moment of `𝒦` with the gate's signature. -/
theorem integral_norm_randK_pow_eqW :
    (((∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ : ℝ)) : ℂ) =
      ∑ tops : Fin (2 * Pm) → ↥(kernelTrees pat (P.N (p + 1)) kind ζ),
        ∑ Q : Finpartition (nfLeaves (fun j => (tops j).1)),
          ((∑' κ : FlowerForestDec (fun j => (tops j).1) P.d (fun _ => n) (fun _ => n'),
              flowerKerIntegrand P.L P.γ P.δ (inputsF P R) (altFlowerSig Pm) (fun j => (tops j).1)
                (fun j => fkCoef P.L P.γ P.δ p pat dagger cut1 cut2 t s (tops j).1) Q p (P.N p) κ) +
            flowerError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) (altFlowerSig Pm) (fun j => (tops j).1)
              (fun j => fkCoef P.L P.γ P.δ p pat dagger cut1 cut2 t s (tops j).1) Q (fun ω => a ω p) p (P.N p)
              (fun _ => n) (fun _ => n')) := by
  set S := kernelTrees pat (P.N (p + 1)) kind ζ
  set coefOf := fkCoef P.L P.γ P.δ p pat dagger cut1 cut2 t s
  have hS : ∀ F ∈ S, F ≠ FTree.flower := fun F hF => ne_flower_of_mem_kernelTrees pat hF
  have hM : ∀ F ∈ S, F.toTree.order ≤ 3 * P.N (p + 1) + 1 := fun F hF => order_toTree_le_of_mem_kernelTrees hF
  have hcoef := norm_fkCoef_le P.L P.γ P.δ p pat dagger cut1 cut2 t s hc
  have hne (tops : Fin (2 * Pm) → ↥S) : (nfLeaves (fun j => (tops j).1)).Nonempty :=
    nfLeaves_nonempty (fun j => (tops j).1) (fun j => hS _ (tops j).2) ⟨0, by omega⟩
  have hcard (tops : Fin (2 * Pm) → ↥S) : (nfLeaves (fun j => (tops j).1)).card ≤ 2 * P.R p :=
    (nfLeaves_card_le (fun j => (tops j).1) (fun j => hM _ (tops j).2)).trans hNR
  have hI (tops : Fin (2 * Pm) → ↥S) : Integrable (fun ω => ∏ j, zpowSign (altFlowerSig Pm j)
      (flowerTerm (tops j).1 (coefOf (tops j).1) (a ω p) n n')) (μ.restrict (Fev p)) :=
    integrable_prod_flowerTerms P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
      (fun j => (tops j).1) (fun j => coefOf (tops j).1) (fun j => hcoef _) (altFlowerSig Pm)
      (hne tops) (hcard tops) (fun _ => n) (fun _ => n')
  have h1 : (fun ω => (((‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) : ℝ)) : ℂ)) =
      fun ω => ∑ tops : Fin (2 * Pm) → ↥S, ∏ j, zpowSign (altFlowerSig Pm j)
        (flowerTerm (tops j).1 (coefOf (tops j).1) (a ω p) n n') :=
    funext fun ω => by
      rw [randK_eq_famFlowerTerm]
      exact norm_famFlowerTerm_pow_eqW S coefOf (a ω p) n n' Pm
  rw [← integral_complex_ofReal, h1, integral_finsetSum _ fun tops _ => hI tops]
  refine sum_congr rfl fun tops _ => ?_
  exact integral_prod_flowerTerms_eq P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ
    (fun j => (tops j).1) (fun j => coefOf (tops j).1) (fun j => hcoef _) (altFlowerSig Pm)
    (hne tops) (hcard tops) (fun _ => n) (fun _ => n')

end RandKW

/-! ## Orders -/

section Orders

variable (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p : ℕ) (kind : FlowerKind) (pat : FixPat)
    (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (Pm : ℕ)

/-- **`flowerSum_N` is the gate garden sum at order `N`.** -/
theorem flowerSum_eq_finsum (N : ℕ) :
    flowerSum P F p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c) cut1 cut2 ζ t s n n' =
      ∑ᶠ (LG : LayeredGarden (2 * Pm)) (_ : GateCond (P.N p) (P.N (p + 1)) pat kind ζ (p := p) LG),
        if LG.garden.order = N then gateSummand P.L P.γ P.δ F p pat dagger cut1 cut2 t s n n' LG else 0 := by
  unfold flowerSum
  refine finsum_congr fun LG => ?_
  rw [finsum_eq_if, finsum_eq_if]
  by_cases h1 : GateCond (P.N p) (P.N (p + 1)) pat kind ζ (p := p) LG
  · have ⟨hH, hatt, hk, hs, hp⟩ := h1
    by_cases h2 : LG.garden.order = N
    · exact (ite_eq_left ⟨hH, hatt, h2, hk, hs, hp⟩).trans ((ite_eq_left h1).trans (ite_eq_left h2)).symm
    · exact (ite_eq_right fun h => h2 h.2.2.1).trans ((ite_eq_left h1).trans (ite_eq_right h2)).symm
  · exact (ite_eq_right fun h => h1 ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩).trans (ite_eq_right h1).symm

variable (hpat : pat = .plain ∨ pat = .dRoot)

include hpat in
/-- **The flower sums up to order `M`** as an index sum. -/
theorem sum_flowerSum_eq (M : ℕ) :
    ∑ N ∈ range (M + 1),
        flowerSum P F p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c) cut1 cut2 ζ t s n n' =
      ∑ x : FlIdx (P.N p) (P.N (p + 1)) pat kind ζ Pm p,
        if (flIdxGraft (P.N p) (P.N (p + 1)) pat kind ζ x).garden.order ≤ M then
          gateSummand P.L P.γ P.δ F p pat dagger cut1 cut2 t s n n' (flIdxGraft (P.N p) (P.N (p + 1)) pat kind ζ x)
        else 0 := by
  simp_rw [flowerSum_eq_finsum]
  simp_rw [← sum_flIdx_eq_finsum (P.N p) (P.N (p + 1)) pat kind ζ hpat]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_ite_eq]
  simp only [mem_range, Nat.lt_succ_iff]

end Orders

/-! ## The `2P`-th moment as flower sums -/

/-- The flower gardens of order `> M`. -/
noncomputable def flowerTail (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p : ℕ) (kind : FlowerKind) (pat : FixPat)
    (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) (Pm M : ℕ) :
    ℂ :=
  ∑ x : FlIdx (P.N p) (P.N (p + 1)) pat kind ζ Pm p,
    if (flIdxGraft (P.N p) (P.N (p + 1)) pat kind ζ x).garden.order ≤ M then 0 else
      gateSummand P.L P.γ P.δ F p pat dagger cut1 cut2 t s n n' (flIdxGraft (P.N p) (P.N (p + 1)) pat kind ζ x)

/-- X2E-1's input error. -/
noncomputable def flowerErr (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ) (p : ℕ) (kind : FlowerKind)
    (pat : FixPat) (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ)
    (n n' : Fin P.d → ℤ) (Pm : ℕ) : ℂ :=
  ∑ tops : Fin (2 * Pm) → ↥(kernelTrees pat (P.N (p + 1)) kind ζ),
    ∑ Q : Finpartition (nfLeaves (fun j => (tops j).1)),
      flowerError (μ.restrict (Fev p)) P.L P.γ P.δ (inputsF P R) (altFlowerSig Pm) (fun j => (tops j).1)
        (fun j => fkCoef P.L P.γ P.δ p pat dagger cut1 cut2 t s (tops j).1) Q (fun ω => a ω p) p (P.N p)
        (fun _ => n) (fun _ => n')

section Main

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
    (hsumF : ∀ q, Summable fun m : Fin P.d → ℤ => |inputsF P R q (latticePoint P.L m)|)
    (hΛ : (P.d : ℝ) + 1 ≤ (P.Lambda p : ℝ) / 2) (hc : |coupling P.d P.L P.γ P.δ| ≤ 1)
    (kind : FlowerKind) (pat : FixPat) (hpat : pat = .plain ∨ pat = .dRoot)
    (dagger : Option (Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ) (ζ : ℤˣ)
    (t s : ℝ) (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin P.d → ℤ) (Pm : ℕ) (hPm : 1 ≤ Pm)
    (hNR : (2 * Pm) * (2 * (3 * P.N (p + 1) + 1) + 1) ≤ 2 * P.R p)
    (hcut : ∀ x : FlIdx (P.N p) (P.N (p + 1)) pat kind ζ Pm p, CutWeightsOK P.L (d := P.d)
      (fun j => ne_flower_of_mem_kernelTrees pat (x.1 j).2) (mkFlowerAt x.2.1.1 x.2.1.2 x.2.2)
      (fun j => kernelTrees_sign (P.N (p + 1)) pat kind ζ (x.1 j).2) cut1 cut2)

include hG ha hrapid hL hδ hsmall hC hF hsumF hΛ hc hpat hpt hps hPm hNR hcut in
/-- **X2E-3: the `2P`-th moment of `𝒦` as B1.12's flower sums**, with the tail of orders `> M` and the input
error. -/
theorem integral_norm_randK_pow_eq_flowerSum (M : ℕ) :
    (((∫ ω in Fev p, ‖randK P a p kind pat dagger cut1 cut2 ζ t s n n' ω‖ ^ (2 * Pm) ∂μ : ℝ)) : ℂ) =
      ∑ N ∈ range (M + 1),
          flowerSum P (inputsF P R) p N (w := 2 * Pm) kind (fun _ => pat) (dagger.map fun c _ => c) cut1 cut2
            ζ t s n n' +
        flowerTail P (inputsF P R) p kind pat dagger cut1 cut2 ζ t s n n' Pm M +
        flowerErr P μ a Fev R p kind pat dagger cut1 cut2 ζ t s n n' Pm := by
  rw [integral_norm_randK_pow_eqW P μ g hG a Fev R E Et p ha hrapid hL hδ hsmall C hC hF hΛ hc kind pat dagger
    cut1 cut2 ζ t s n n' Pm hPm hNR]
  simp only [sum_add_distrib]
  rw [sum_flowerKer_eq_finsum_gate (P.N p) (P.N (p + 1)) pat kind ζ P.L P.γ P.δ (inputsF P R) hsumF hpat dagger
    cut1 cut2 hcut hpt hps n n', ← sum_flIdx_eq_finsum (P.N p) (P.N (p + 1)) pat kind ζ hpat,
    sum_flowerSum_eq P (inputsF P R) p kind pat dagger cut1 cut2 ζ t s n n' Pm hpat M]
  unfold flowerTail flowerErr
  rw [← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

end Main

end WaveTurbulence.X2E
