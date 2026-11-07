/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeSwap
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.GluePiece
/-! FLOWER-P7: **the decapitation identity of the free cap** (kind `L0`, `dt = false`):
`K_Q(t,k) = c² ∑_n ε(n) ∫_{s∈rootDom} e^{rootphase(n,s)} K_{G}(caps s; n) ds`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

instance countable_genDecoration {w : ℕ} (G : Garden w) (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) :
    Countable (GenDecoration G d nroot nfl) := by
  unfold GenDecoration
  infer_instance

theorem volume_rootDom_lt_top (p : ℕ) (t : ℝ) : (volume : Measure (Fin 2 → ℝ)) (rootDom p t) < ⊤ := by
  have hsub : rootDom p t ⊆ Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (p : ℝ) (p + 1) := fun s hs j _ =>
    ⟨(hs j).1, (hs j).2.1⟩
  refine lt_of_le_of_lt (measure_mono hsub) ?_
  rw [volume_pi_pi]
  simp

/-- The decoration sum commutes with the root-time integral. -/
theorem tsum_integral_gfun (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (nroot : Fin (2 * 3) → (Fin d → ℤ)) (hplain : LG.garden.IsPlain)
    (hF : ∀ q : ℕ, Summable fun n : Fin d → ℤ => |F q (k + latticePoint L n)|) :
    ∑' κ : GenDecoration LG.garden d nroot 0, ∫ s, gfun L γ δ F LG p t k κ.1 s =
      ∫ s, ∑' κ : GenDecoration LG.garden d nroot 0, gfun L γ δ F LG p t k κ.1 s := by
  set C := (volume : Measure ({b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ)).real
    (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) with hC
  have hC0 : 0 ≤ C := measureReal_nonneg
  have hsB := summable_kgBound L F LG k nroot 0 (plain_hlone _ hplain) (fun ℓ _ => hF _)
  refine integral_tsum_of_summable_integral_norm (fun κ => integrable_gfun L γ δ F LG hsig p hp t k κ.1) ?_
  refine Summable.of_nonneg_of_le (fun κ => integral_nonneg fun s => norm_nonneg _) (fun κ => ?_)
    (hsB.mul_left C)
  have hkg : 0 ≤ kgBound L F LG k κ.1 := Finset.prod_nonneg fun _ _ => abs_nonneg _
  have hmeas := measurableSet_rootDom p t
  have hI : Integrable ((rootDom p t).indicator fun _ => C * kgBound L F LG k κ.1) :=
    (integrable_indicator_iff hmeas).2 (integrableOn_const (volume_rootDom_lt_top p t).ne)
  calc ∫ s, ‖gfun L γ δ F LG p t k κ.1 s‖
      ≤ ∫ s, (rootDom p t).indicator (fun _ => C * kgBound L F LG k κ.1) s :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _) hI
          (Filter.Eventually.of_forall fun s => norm_gfun_le L γ δ F LG p t k κ.1 s)
    _ = (volume : Measure (Fin 2 → ℝ)).real (rootDom p t) * (C * kgBound L F LG k κ.1) := by
        rw [integral_indicator_const _ hmeas, smul_eq_mul]
    _ ≤ 1 * (C * kgBound L F LG k κ.1) :=
        mul_le_mul_of_nonneg_right (volume_rootDom_le p t) (mul_nonneg hC0 hkg)
    _ = C * kgBound L F LG k κ.1 := one_mul _

/-- The cap summand with free roots, as a function of the six-tree decoration. -/
noncomputable def capSummandFree (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (κ' : Dec6 LG.garden d) : ℂ :=
  kgTerm L γ δ F (capLayered LG hsig p hp) (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k
    (upperDec (T := LG.garden.tree) κ'.1)

/-- The `n`-th outer term of the free decapitation identity. -/
noncomputable def freeTerm (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3)) (p : ℕ) (t : ℝ)
    (k : Mom d) (n : OuterLabels d) : ℂ :=
  ∫ s : Fin 2 → ℝ, (rootDom p t).indicator (fun s =>
    ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ) *
      rootPhaseS L γ δ k s n.1 *
      kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k n.1 0) s

theorem sum_cs_eq (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (hplain : LG.garden.IsPlain)
    (hF : ∀ q : ℕ, Summable fun n : Fin d → ℤ => |F q (k + latticePoint L n)|) (n : OuterLabels d) :
    ∑' κ : GenDecoration LG.garden d n.1 0, capSummandFree L γ δ F LG hsig p hp t k (decSigma LG.garden d ⟨n, κ⟩) =
      ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ) *
        ∫ s : Fin 2 → ℝ, (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s n.1 *
          ∑' κ : GenDecoration LG.garden d n.1 0,
            kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k κ.1) s := by
  have hr : ∀ κ : GenDecoration LG.garden d n.1 0,
      (fun c => κ.1 (GNode.root LG.garden.tree c)) = n.1 := fun κ => funext fun c => κ.2.2.1 c
  have hterm : ∀ κ : GenDecoration LG.garden d n.1 0,
      capSummandFree L γ δ F LG hsig p hp t k (decSigma LG.garden d ⟨n, κ⟩) =
        ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ) *
          ∫ s, gfun L γ δ F LG p t k κ.1 s := by
    intro κ
    have e : (decSigma LG.garden d ⟨n, κ⟩).1 = κ.1 := rfl
    simp only [capSummandFree, e]
    rw [kgTerm_cap_free]
    have h' : ∀ j i, κ.1 (GNode.root LG.garden.tree (idx j i)) = n.1 (idx j i) := fun j i => κ.2.2.1 (idx j i)
    simp only [h']
    rfl
  simp only [hterm]
  rw [tsum_mul_left, tsum_integral_gfun L γ δ F LG hsig p hp t k n.1 hplain hF]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ rootDom p t
  · simp only [gfun, Set.indicator_of_mem hs, hr, tsum_mul_left]
  · simp only [gfun, Set.indicator_of_notMem hs, tsum_zero]

theorem freeTerm_eq (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3)) (p : ℕ) (t : ℝ)
    (k : Mom d) (n : OuterLabels d) :
    freeTerm L γ δ F LG p t k n =
      ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ)) *
        ∫ s : Fin 2 → ℝ, (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s n.1 *
          ∑' κ : GenDecoration LG.garden d n.1 0,
            kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k κ.1) s := by
  unfold freeTerm
  have hk : ∀ s : Fin 2 → ℝ, (rootDom p t).indicator (fun s =>
      ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ) *
        rootPhaseS L γ δ k s n.1 *
        kernelKgen L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k n.1 0) s =
      ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
        ((∏ j : Fin 2, epsCoef (n.1 (idx j 0)) (n.1 (idx j 1)) (n.1 (idx j 2)) : ℝ) : ℂ)) *
        (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s n.1 *
          ∑' κ : GenDecoration LG.garden d n.1 0,
            kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k κ.1) s := by
    intro s
    by_cases hs : s ∈ rootDom p t
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, kernelKgen_eq_tsum]
      ring
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero]
  simp only [hk]
  rw [integral_const_mul]

/-- **The decapitation identity of the free cap.** -/
theorem kernelKgen_cap_free (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (hplain : LG.garden.IsPlain)
    (hF : ∀ q : ℕ, Summable fun n : Fin d → ℤ => |F q (k + latticePoint L n)|) :
    kernelKgen L γ δ F (capLayered LG hsig p hp) (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * ∑' n : OuterLabels d, freeTerm L γ δ F LG p t k n := by
  have hplainQ : (capLayered LG hsig p hp).garden.IsPlain := (isPlain_cap_iff _ hsig).2 hplain
  have hsum := summable_kgTerm L γ δ F (capLayered LG hsig p hp) (fun _ => t) (fun _ => none) k (fun _ => 0) 0
    (plain_hlone _ hplainQ) (fun ℓ _ => hF _)
  rw [kernelKgen_eq_tsum]
  set cs : Dec6 LG.garden d → ℂ := capSummandFree L γ δ F LG hsig p hp t k with hcs
  have hceq : ∀ κ : GenDecoration (capGarden LG.garden hsig) d (fun _ => 0) 0,
      cs (capDecEquiv LG.garden hsig d κ) =
        kgTerm L γ δ F (capLayered LG hsig p hp) (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k κ.1 := by
    intro κ
    simp only [hcs, capSummandFree]
    rw [← capDec_val]
  have hsum1 : Summable cs := by
    rw [← (capDecEquiv LG.garden hsig d).summable_iff]
    exact hsum.congr fun κ => (hceq κ).symm
  have h1 : ∑' κ : GenDecoration (capGarden LG.garden hsig) d (fun _ => 0) 0,
      kgTerm L γ δ F (capLayered LG hsig p hp) (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k κ.1 =
        ∑' κ' : Dec6 LG.garden d, cs κ' := by
    rw [← (capDecEquiv LG.garden hsig d).tsum_eq cs]
    exact tsum_congr fun κ => (hceq κ).symm
  have hsum2 : Summable fun x : (Σ n : OuterLabels d, GenDecoration LG.garden d n.1 0) =>
      cs (decSigma LG.garden d x) := (Equiv.summable_iff (decSigma LG.garden d) (f := cs)).2 hsum1
  have h2 : ∑' κ' : Dec6 LG.garden d, cs κ' =
      ∑' x : (Σ n : OuterLabels d, GenDecoration LG.garden d n.1 0), cs (decSigma LG.garden d x) :=
    ((decSigma LG.garden d).tsum_eq cs).symm
  rw [h1, h2, Summable.tsum_sigma hsum2]
  simp only [hcs, sum_cs_eq L γ δ F LG hsig p hp t k hplain hF]
  rw [order_cap, zeta_cap, pow_add, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [freeTerm_eq]
  ring

/-- The outer-label series of the free cap converges. -/
theorem summable_freeTerm (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (hplain : LG.garden.IsPlain)
    (hF : ∀ q : ℕ, Summable fun n : Fin d → ℤ => |F q (k + latticePoint L n)|) :
    Summable fun n : OuterLabels d => freeTerm L γ δ F LG p t k n := by
  have hplainQ : (capLayered LG hsig p hp).garden.IsPlain := (isPlain_cap_iff _ hsig).2 hplain
  have hsum := summable_kgTerm L γ δ F (capLayered LG hsig p hp) (fun _ => t) (fun _ => none) k (fun _ => 0) 0
    (plain_hlone _ hplainQ) (fun ℓ _ => hF _)
  set cs : Dec6 LG.garden d → ℂ := capSummandFree L γ δ F LG hsig p hp t k with hcs
  have hceq : ∀ κ : GenDecoration (capGarden LG.garden hsig) d (fun _ => 0) 0,
      cs (capDecEquiv LG.garden hsig d κ) =
        kgTerm L γ δ F (capLayered LG hsig p hp) (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k κ.1 := by
    intro κ
    simp only [hcs, capSummandFree]
    rw [← capDec_val]
  have hsum1 : Summable cs := by
    rw [← (capDecEquiv LG.garden hsig d).summable_iff]
    exact hsum.congr fun κ => (hceq κ).symm
  have hsum2 : Summable fun x : (Σ n : OuterLabels d, GenDecoration LG.garden d n.1 0) =>
      cs (decSigma LG.garden d x) := (Equiv.summable_iff (decSigma LG.garden d) (f := cs)).2 hsum1
  have hs3 := hsum2.sigma
  simp only [hcs, sum_cs_eq L γ δ F LG hsig p hp t k hplain hF] at hs3
  have := hs3.mul_left ((coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta)
  refine this.congr fun n => ?_
  rw [freeTerm_eq]
  ring

end WaveTurbulence.FlowerP7
