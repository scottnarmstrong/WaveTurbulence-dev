/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapCond
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite
/-! FLOWER-P7: `coupleSum … true` as `c² ∑_n outerWeight(n) · S(n)`, `S(n)` a finite sum of six-tree garden kernels. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset

variable {d : ℕ}

/-- The cap summand family over the six-tree labellings is summable (plain cap, summable inputs). -/
theorem summable_capSummand (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (hplain : LG.garden.IsPlain)
    (hF : ∀ q : ℕ, Summable fun n : Fin d → ℤ => |F q (k + latticePoint L n)|) :
    Summable (capSummand L γ δ F LG hsig p hp t k) := by
  have hpl : (capGarden LG.garden hsig).IsPlain := (isPlain_cap_iff _ hsig).2 hplain
  have hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf (capLayered LG hsig p hp).garden.tree =>
      ℓ.1.1 = j ∧ (capLayered LG hsig p hp).garden.IsLone ℓ).card ≤ 1 := fun j => by
    rw [Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun ℓ _ h => by
      have h2 := h.2
      unfold Garden.IsLone at h2
      rw [hpl ℓ] at h2
      exact absurd h2 (by simp))]
    exact Nat.zero_le _
  have hsum := summable_kgTerm L γ δ F (capLayered LG hsig p hp) (fun _ => t)
    (pinRoots (T := LG.garden.tree) t) k (fun _ => 0) 0 hlone (fun ℓ _ => hF _)
  rw [← (capDecEquiv LG.garden hsig d).summable_iff]
  exact hsum.congr fun κ => (capSummand_equiv L γ δ F LG hsig p hp t k κ).symm

/-- For each plain source the outer-label series converges. -/
theorem summable_outer_kernel (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (hplain : LG.garden.IsPlain)
    (hF : ∀ q : ℕ, Summable fun n : Fin d → ℤ => |F q (k + latticePoint L n)|) :
    Summable fun n : OuterLabels d => outerWeight L γ δ k t n.1 *
      kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 := by
  have hsum1 := summable_capSummand L γ δ F LG hsig p hp t k hplain hF
  have hsum2 : Summable fun x : (Σ n : OuterLabels d, GenDecoration LG.garden d n.1 0) =>
      capSummand L γ δ F LG hsig p hp t k (decSigma LG.garden d x) :=
    (Equiv.summable_iff (decSigma LG.garden d) (f := capSummand L γ δ F LG hsig p hp t k)).2 hsum1
  have hs3 := hsum2.sigma
  have h3 : ∀ n : OuterLabels d,
      ∑' κ : GenDecoration LG.garden d n.1 0,
        capSummand L γ δ F LG hsig p hp t k (decSigma LG.garden d ⟨n, κ⟩) =
      outerWeight L γ δ k t n.1 * ∑' κ : GenDecoration LG.garden d n.1 0,
        kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k κ.1 := by
    intro n
    rw [← tsum_mul_left]
    exact tsum_congr fun κ => capSummand_sigma L γ δ F LG hsig p hp t k ⟨n, κ⟩
  simp only [h3] at hs3
  have := hs3.mul_left ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta)
  refine this.congr fun n => ?_
  rw [kernelKgen_eq_tsum]
  ring

theorem finite_Y6 (P : WTParams) (p N : ℕ) (kind : TreeKind) :
    {y : CapSrc p | Y6Cond P p N kind y.1}.Finite := by
  have hfin := Canon.finite_layeredGardens (2 * 3) N p
  refine Set.Finite.subset (hfin.preimage (Subtype.val_injective.injOn)) ?_
  intro y hy
  refine ⟨?_, y.2.2⟩
  have := hy.2.2.2.1
  omega

/-- **The sum-level decapitation identity, reorganised by the outer labels**: `coupleSum … true` is
`c² ∑_n outerWeight(n) S(n)`, where `S(n)` is the (finite) sum of the six-tree garden kernels of the
decapitated carrier at the root labels `n`. -/
theorem coupleSum_true_swap (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind) (t : ℝ)
    (k : Mom P.d)
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |F q (k + latticePoint P.L n)|) :
    coupleSum P F p N kind true t k =
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d, outerWeight P.L P.γ P.δ k t n.1 *
        ∑ᶠ (y : CapSrc p) (_ : Y6Cond P p N kind y.1),
          kernelKgen P.L P.γ P.δ F y.1 (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 := by
  classical
  rw [coupleSum_true_cap P F p N kind t k hF]
  have hcond : ∀ y : CapSrc p, CoupleCond P p N kind y.cap ↔ Y6Cond P p N kind y.1 :=
    fun y => coupleCond_cap_iff P p N kind y
  have e1 : ∀ y : CapSrc p, ∑ᶠ (_ : CoupleCond P p N kind y.cap),
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d, outerWeight P.L P.γ P.δ k t n.1 *
        kernelKgen P.L P.γ P.δ F y.1 (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 =
      ∑ᶠ (_ : Y6Cond P p N kind y.1),
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d, outerWeight P.L P.γ P.δ k t n.1 *
        kernelKgen P.L P.γ P.δ F y.1 (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 := fun y => by
    rw [propext (hcond y)]
  rw [finsum_congr fun y => e1 y]
  have hfin := finite_Y6 P p N kind
  rw [show (∑ᶠ (y : CapSrc p) (_ : Y6Cond P p N kind y.1), _) = ∑ᶠ y ∈ {y : CapSrc p | Y6Cond P p N kind y.1}, _ from rfl,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hs : ∀ y ∈ hfin.toFinset, Summable fun n : OuterLabels P.d => outerWeight P.L P.γ P.δ k t n.1 *
      kernelKgen P.L P.γ P.δ F y.1 (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 := by
    intro y hy
    have hy' : Y6Cond P p N kind y.1 := hfin.mem_toFinset.1 hy
    exact summable_outer_kernel P.L P.γ P.δ F y.1 y.2.1 p y.2.2 t k hy'.1 hF
  have hS : ∀ n : OuterLabels P.d, ∑ᶠ (y : CapSrc p) (_ : Y6Cond P p N kind y.1),
      kernelKgen P.L P.γ P.δ F y.1 (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 =
      ∑ y ∈ hfin.toFinset, kernelKgen P.L P.γ P.δ F y.1 (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k n.1 0 :=
    fun n => finsum_mem_eq_finite_toFinset_sum _ hfin
  simp only [hS]
  rw [← Finset.mul_sum]
  congr 1
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum hs]

end WaveTurbulence.FlowerP7
