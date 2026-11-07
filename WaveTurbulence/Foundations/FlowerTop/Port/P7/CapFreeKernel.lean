/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapFreeIntegral
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapSum
/-! FLOWER-P7: the decapitation identity for the couple with FREE root times (kind `L0`, no `∂_t`):
`K_Q(t,k) = c² ∑_n ε(n) ∫_{s ∈ rootDom} e^{rootphase(n,s)} K_{G}(caps s; n) ds`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

/-- The summable majorant of the decoration terms. -/
noncomputable def kgBound {w : ℕ} (L : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (k₀ : Mom d)
    (κ : GNode LG.garden.tree → (Fin d → ℤ)) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden, |F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ ℓ.toNode)|

theorem summable_kgBound {w : ℕ} (L : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ)
    (hlone : ∀ j, (Finset.univ.filter fun ℓ : GLeaf LG.garden.tree =>
      ℓ.1.1 = j ∧ LG.garden.IsLone ℓ).card ≤ 1)
    (hF : ∀ ℓ ∈ inputLeaves LG.garden,
      Summable fun n : Fin d → ℤ => |F (LG.layer ℓ.toNode) (k₀ + latticePoint L n)|) :
    Summable fun κ : GenDecoration LG.garden d nroot nfl => kgBound L F LG k₀ κ.1 := by
  classical
  have hΦ := decoration_injective_of_inputs LG nroot nfl hlone
  let ι := {ℓ : GLeaf LG.garden.tree // ℓ ∈ inputLeaves LG.garden}
  let f : ι → (Fin d → ℤ) → ℝ := fun ℓ n => |F (LG.layer ℓ.1.toNode) (k₀ + latticePoint L n)|
  have hf : Summable fun z : ι → (Fin d → ℤ) => ∏ ℓ, f ℓ (z ℓ) :=
    summable_pi_prod f (fun _ _ => abs_nonneg _) fun ℓ => hF ℓ.1 ℓ.2
  refine (hf.comp_injective hΦ).congr fun κ => ?_
  simp only [Function.comp_apply, kgBound]
  symm
  rw [← Finset.prod_coe_sort]
  rfl

theorem norm_kgTerm_le {w : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (κ : GNode LG.garden.tree → (Fin d → ℤ)) :
    ‖kgTerm L γ δ F LG fix ∅ (fun _ => 1) up k₀ κ‖ ≤
      (volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)).real
        (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) *
        kgBound L F LG k₀ κ := by
  unfold kgTerm kgBound
  rw [norm_mul, norm_mul, norm_mul, norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, norm_one]
  have hC : 0 ≤ (volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)).real
        (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) := measureReal_nonneg
  have hP : 0 ≤ ∏ ℓ ∈ inputLeaves LG.garden,
      |F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ ℓ.toNode)| :=
    Finset.prod_nonneg fun _ _ => abs_nonneg _
  calc _ ≤ 1 * 1 * (volume : Measure ({b : GBranch LG.garden.tree // fix b = none} → ℝ)).real
        (Set.pi Set.univ fun b => Set.Icc (LG.layer b.1.toNode : ℝ) (LG.layer b.1.toNode + 1)) *
        ∏ ℓ ∈ inputLeaves LG.garden, |F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ ℓ.toNode)| := by
        gcongr
        · exact abs_epsDec_le_one LG.garden κ
        · exact norm_pinnedIntegral_le L γ δ LG up fix _
    _ = _ := by ring

/-- **Term-level identity of the free cap.** -/
theorem kgTerm_cap_free (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden (2 * 3))
    (hsig : ∀ c, LG.garden.sig c = childSig c) (p : ℕ) (hp : ∀ a, LG.layer a ≤ p) (t : ℝ) (k : Mom d)
    (κ' : GNode LG.garden.tree → (Fin d → ℤ)) :
    kgTerm L γ δ F (capLayered LG hsig p hp) (fun _ => none) ∅ (fun _ => 1) (fun _ => t) k
        (upperDec (T := LG.garden.tree) κ') =
      ((∏ j : Fin 2, epsCoef (κ' (GNode.root LG.garden.tree (idx j 0))) (κ' (GNode.root LG.garden.tree (idx j 1)))
        (κ' (GNode.root LG.garden.tree (idx j 2))) : ℝ) : ℂ) *
        ∫ s : Fin 2 → ℝ, (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s
          (fun c => κ' (GNode.root LG.garden.tree c)) *
            kgTerm L γ δ F LG (fun _ => none) ∅ (fun _ => 1) (fun b => s (jOf b.1.1)) k κ') s := by
  unfold kgTerm
  rw [integral_cap_free L γ δ LG hsig p hp t k κ', inputProd_cap L F LG hsig p hp k κ', epsDec_cap LG.garden hsig κ']
  set A : ℂ := (epsDec LG.garden κ' : ℂ) with hA
  set B : ℂ := ∏ ℓ ∈ inputLeaves LG.garden, (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k κ' ℓ.toNode) : ℂ) with hB
  set E : ℂ := ((∏ j : Fin 2, epsCoef (κ' (GNode.root LG.garden.tree (idx j 0)))
    (κ' (GNode.root LG.garden.tree (idx j 1))) (κ' (GNode.root LG.garden.tree (idx j 2))) : ℝ) : ℂ) with hE
  have hpt : ∀ s : Fin 2 → ℝ, (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s
      (fun c => κ' (GNode.root LG.garden.tree c)) *
        (A * (((fun _ : GNode LG.garden.tree → Mom d => (1 : ℝ)) (cosetDecoration LG.garden L k κ') : ℝ) : ℂ) *
          (∫ σ : {b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ,
            (kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none)).indicator
              (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ'))
              (LG.garden.extendFix (fun _ => none) σ)) * B)) s =
      (A * B) * (rootDom p t).indicator (fun s => rootPhaseS L γ δ k s
        (fun c => κ' (GNode.root LG.garden.tree c)) *
          ∫ σ : {b : GBranch LG.garden.tree // (fun _ : GBranch LG.garden.tree => (none : Option ℝ)) b = none} → ℝ,
            (kDomainFix LG (fun b => s (jOf b.1.1)) (fun _ => none)).indicator
              (phaseProdOff L γ δ LG.garden ∅ (cosetDecoration LG.garden L k κ'))
              (LG.garden.extendFix (fun _ => none) σ)) s := by
    intro s
    by_cases hs : s ∈ rootDom p t
    · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      simp only [Complex.ofReal_one, mul_one]
      ring
    · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero]
  simp only [hpt]
  rw [integral_const_mul, Complex.ofReal_mul]
  simp only [Complex.ofReal_one, mul_one]
  ring

end WaveTurbulence.FlowerP7
