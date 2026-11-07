/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeSum
/-! FLOWER-P7: `coupleSum … L0 false` as the outer-label sum of the root-time integrals of the decapitated sums. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

/-- The integrand of `freeTerm` in the root times. -/
noncomputable def freeIntegrand (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3)) (p : ℕ) (t : ℝ)
    (k : Mom d) (n : OuterLabels d) (s : Fin 2 → ℝ) : ℂ :=
  (rootDom p t).indicator (fun s =>
    ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ) *
      rootPhaseS L γ δ k s n.1 *
      kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k n.1 0) s

theorem freeTerm_def (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3)) (p : ℕ) (t : ℝ)
    (k : Mom d) (n : OuterLabels d) :
    freeTerm L γ δ F LG p t k n = ∫ s, freeIntegrand L γ δ F LG p t k n s := rfl

theorem tsum_gfun_eq (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3)) (p : ℕ) (t : ℝ)
    (k : Mom d) (n : OuterLabels d) (s : Fin 2 → ℝ) :
    ∑' κ : GenDecoration LG.garden d n.1 0, gfun L γ δ F LG p t k κ.1 s =
      (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s n.1 *
        ∑' κ : GenDecoration LG.garden d n.1 0,
          kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k κ.1) s := by
  have hr : ∀ κ : GenDecoration LG.garden d n.1 0,
      (fun c => κ.1 (GNode.root LG.garden.tree c)) = n.1 := fun κ => funext fun c => κ.2.2.1 c
  by_cases hs : s ∈ rootDom p t
  · simp only [gfun, Set.indicator_of_mem hs, hr, tsum_mul_left]
  · simp only [gfun, Set.indicator_of_notMem hs, tsum_zero]

theorem freeIntegrand_eq (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3)) (p : ℕ) (t : ℝ)
    (k : Mom d) (n : OuterLabels d) (s : Fin 2 → ℝ) :
    freeIntegrand L γ δ F LG p t k n s =
      ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ)) *
        ∑' κ : GenDecoration LG.garden d n.1 0, gfun L γ δ F LG p t k κ.1 s := by
  rw [tsum_gfun_eq]
  unfold freeIntegrand
  by_cases hs : s ∈ rootDom p t
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, kernelKgen_eq_tsum]
    ring
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero]

theorem integrable_freeIntegrand (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (hplain : LG.garden.IsPlain)
    (hF : ∀ q : ℕ, Summable fun n : Fin d → ℤ => |F q (k + latticePoint L n)|) (n : OuterLabels d) :
    Integrable (freeIntegrand L γ δ F LG p t k n) := by
  have h := (integrable_tsum_gfun L γ δ F LG hsig p hp t k n.1 hplain hF).const_mul
    ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ))
  refine h.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only
  rw [freeIntegrand_eq]

/-- **`coupleSum … L0 false` over the caps of the carrier `CapSrc`.** -/
theorem coupleSum_false_cap (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) (k : Mom P.d)
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |F q (k + latticePoint P.L n)|) :
    coupleSum P F p N .L0 false t k =
      ∑ᶠ (y : CapSrc p) (_ : CoupleCond P p N .L0 y.cap),
        (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d, freeTerm P.L P.γ P.δ F y.1 p t k n := by
  classical
  unfold coupleSum
  have hfix : ∀ Q : LayeredGarden 2, (fun b : GBranch Q.garden.tree => if (false = true) ∧ b.1.2 = [] then some t else none) =
      fun _ => none := fun Q => by
    funext b; simp
  have hset : ∀ Q : LayeredGarden 2,
      (IsCanonC (p + 1) Q ∧ (∀ u ∈ Q.attachNodes p, Q.attachedOrder p u ≤ P.N p) ∧ Q.garden.order = N ∧
        Q.TreeKindOK p (P.N (p + 1)) .L0 ∧
        (false = true → ∀ j : Fin 2, ∃ b : GBranch Q.garden.tree, b.1 = (j, []) ∧ Q.layer b.toNode = p)) =
      CoupleCond P p N .L0 Q := fun Q => by
    apply propext
    constructor
    · rintro ⟨h1, h2, h3, h4, -⟩
      exact ⟨h1, h2, h3, h4, roots_layer_of_L0 Q p _ h1.2.1 h4⟩
    · rintro ⟨h1, h2, h3, h4, -⟩
      exact ⟨h1, h2, h3, h4, fun h => absurd h (by simp)⟩
  have e0 : ∀ Q : LayeredGarden 2, (∑ᶠ (_ : IsCanonC (p + 1) Q ∧ (∀ u ∈ Q.attachNodes p, Q.attachedOrder p u ≤ P.N p) ∧
        Q.garden.order = N ∧ Q.TreeKindOK p (P.N (p + 1)) .L0 ∧
        (false = true → ∀ j : Fin 2, ∃ b : GBranch Q.garden.tree, b.1 = (j, []) ∧ Q.layer b.toNode = p)),
      kernelKgen P.L P.γ P.δ F Q (fun b => if (false = true) ∧ b.1.2 = [] then some t else none) ∅
        (fun _ => 1) (fun _ => t) k (fun _ => 0) 0) =
      ∑ᶠ (_ : CoupleCond P p N .L0 Q),
        kernelKgen P.L P.γ P.δ F Q (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k (fun _ => 0) 0 := fun Q =>
    finsum_congr_Prop (hset Q) (fun h => by rw [hfix Q])
  rw [finsum_congr e0]
  refine (finsum_cap_eq (p := p) {Q | CoupleCond P p N .L0 Q}
    (fun Q hQ => coupleCond_facts P p N .L0 Q hQ)
    (fun Q => kernelKgen P.L P.γ P.δ F Q (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k (fun _ => 0) 0)).trans ?_
  refine finsum_congr fun y => finsum_congr_Prop rfl fun hy => ?_
  have hplain : y.1.garden.IsPlain := by
    have hp2 := (coupleCond_facts P p N .L0 _ hy).2.1
    exact (isPlain_cap_iff _ y.2.1).1 hp2
  exact kernelKgen_cap_free P.L P.γ P.δ F y.1 y.2.1 p y.2.2 t k hplain hF

/-- **The sum-level decapitation identity for `coupleSum … L0 false`**: the outer-label sum of the root-time
integrals of the decapitated six-tree sums (finite sum over the decapitated carrier). -/
theorem coupleSum_false_swap (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) (k : Mom P.d)
    (hF : ∀ q : ℕ, Summable fun n : Fin P.d → ℤ => |F q (k + latticePoint P.L n)|) :
    coupleSum P F p N .L0 false t k =
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d, ∫ s : Fin 2 → ℝ,
        ∑ y ∈ (finite_Y6 P p N .L0).toFinset, freeIntegrand P.L P.γ P.δ F y.1 p t k n s := by
  classical
  rw [coupleSum_false_cap P F p N t k hF]
  have hcond : ∀ y : CapSrc p, CoupleCond P p N .L0 y.cap ↔ Y6Cond P p N .L0 y.1 :=
    fun y => coupleCond_cap_iff P p N .L0 y
  have e1 : ∀ y : CapSrc p, ∑ᶠ (_ : CoupleCond P p N .L0 y.cap),
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d, freeTerm P.L P.γ P.δ F y.1 p t k n =
      ∑ᶠ (_ : Y6Cond P p N .L0 y.1),
      (coupling P.d P.L P.γ P.δ : ℂ) ^ 2 * ∑' n : OuterLabels P.d, freeTerm P.L P.γ P.δ F y.1 p t k n :=
    fun y => by rw [propext (hcond y)]
  rw [finsum_congr fun y => e1 y]
  have hfin := finite_Y6 P p N .L0
  rw [show (∑ᶠ (y : CapSrc p) (_ : Y6Cond P p N .L0 y.1), _) = ∑ᶠ y ∈ {y : CapSrc p | Y6Cond P p N .L0 y.1}, _ from rfl,
    finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hs : ∀ y ∈ hfin.toFinset, Summable fun n : OuterLabels P.d => freeTerm P.L P.γ P.δ F y.1 p t k n := by
    intro y hy
    have hy' : Y6Cond P p N .L0 y.1 := hfin.mem_toFinset.1 hy
    exact summable_freeTerm P.L P.γ P.δ F y.1 y.2.1 p y.2.2 t k hy'.1 hF
  rw [← Finset.mul_sum]
  congr 1
  rw [← Summable.tsum_finsetSum hs]
  refine tsum_congr fun n => ?_
  simp only [freeTerm_def]
  rw [integral_finset_sum]
  intro y hy
  have hy' : Y6Cond P p N .L0 y.1 := hfin.mem_toFinset.1 hy
  exact integrable_freeIntegrand P.L P.γ P.δ F y.1 y.2.1 p y.2.2 t k hy'.1 hF n

end WaveTurbulence.FlowerP7
