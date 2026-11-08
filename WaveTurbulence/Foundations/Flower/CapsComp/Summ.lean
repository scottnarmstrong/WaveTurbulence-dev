/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Bij
public import WaveTurbulence.Foundations.Flower.CapsFub.Summ
public import WaveTurbulence.Foundations.Flower.MkDefs.Bounds
/-! # A3b CAPS-COMP: summability of the component kernel summands (the side condition `hs` of A3a's
`compValue_glueN`)

The weight `capWt = selOK · markedWeight` of a capped component is bounded by a constant times the product, over
the input leaves not paired with a cap, of `b ⟨k⟩^{-(d+1)}` (from the `S^{40d,40d}` bound of the pair profiles,
`CapsFub.abs_le_of_SNormR`). On decorations the cap pairs carry the fixed cap momentum, so multiplying the weight by
the indicator that the cap-pair input leaves carry that momentum changes no summand; the modified weight is
dominated as in `CapsFub.summable_kernelGenFactor_dom'`. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs GraftGen

variable {W : ℕ}

theorem abs_selOK_le (LG : LayeredGarden W) (J : Finset (Fin W)) (kSel : Fin W → Option ℕ) :
    |selOK LG J kSel| ≤ 1 := by
  unfold selOK; split_ifs <;> simp

theorem abs_dagW_le {d : ℕ} (LG : LayeredGarden W) (J : Finset (Fin W)) (dag : Option (Fin W → Fin 3 → Mom d))
    (k : GNode LG.garden.tree → Mom d) : |dag.elim 1 (fun c => sibWeightCap LG J c k)| ≤ 1 := by
  cases dag with
  | none => simp
  | some c => exact abs_sibWeightCap_le_one LG J c k

/-- The selection constant. -/
def selConst (LG : LayeredGarden W) (J : Finset (Fin W)) (kSel : Fin W → Option ℕ) (Rs : Fin W → ℝ) : ℝ :=
  ∏ j : Fin W, (if (selCap LG J kSel j).isSome then chiDConst * |Rs j|⁻¹ else 1)

theorem selConst_nonneg (LG : LayeredGarden W) (J : Finset (Fin W)) (kSel : Fin W → Option ℕ) (Rs : Fin W → ℝ) :
    0 ≤ selConst LG J kSel Rs :=
  Finset.prod_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg chiDConst_nonneg (inv_nonneg.2 (abs_nonneg _))
    · exact zero_le_one

/-- The weight bound: `|capWt k| ≤ selConst · |leafProdCap k|`. -/
theorem abs_capWt_le {d : ℕ} (LG : LayeredGarden W) (J : Finset (Fin W)) (p : ℕ) (L : ℝ)
    (kSel : Fin W → Option ℕ) (Rf : Fin W → Option ℝ) (sg : Fin W → Option ℕ) (Rs : Fin W → ℝ)
    (h : ℕ → Fin W → Fin W → Mom d → ℝ) (dag : Option (Fin W → Fin 3 → Mom d)) (k : GNode LG.garden.tree → Mom d) :
    |capWt LG J p L kSel Rf sg Rs h dag k| ≤ selConst LG J kSel Rs * |leafProdCap LG J h k| := by
  unfold capWt markedWeight
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
  have h1 := abs_selOK_le LG J kSel
  have h2 := Fam.abs_frontierW_le LG p Rf k
  have h3 := abs_stemFilterCap_le_one LG J L sg k
  have h4 := abs_selWeightCap_le LG J (selCap LG J kSel) Rs k
  have h6 := abs_dagW_le LG J dag k
  have hS := selConst_nonneg LG J kSel Rs
  calc _ ≤ 1 * (1 * 1 * selConst LG J kSel Rs * |leafProdCap LG J h k| * 1) := by
        refine mul_le_mul h1 ?_ (by positivity) zero_le_one
        refine mul_le_mul ?_ h6 (abs_nonneg _) (by positivity)
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        refine mul_le_mul (mul_le_mul h2 h3 (abs_nonneg _) zero_le_one) h4 (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- **Summability of the component summands.** -/
theorem summable_kgTerm_capWt (P : WTParams) (hL : 0 < P.L) {p : ℕ} (G : LayeredGarden W)
    (hpl : G.garden.IsPlain) (hlay : ∀ a, G.layer a ≤ p) (J : Finset (Fin W))
    (hJ : ∀ i ∈ J, G.garden.tree i = TTree.leaf) (roots : Fin W → (Fin P.d → ℤ)) (n' : Fin P.d → ℤ)
    (hroots : ∀ i ∈ J, roots i = n') (fix : GBranch G.garden.tree → Option ℝ) (off : Finset (GBranch G.garden.tree))
    (up : GBranch G.garden.tree → ℝ) (kSel : Fin W → Option ℕ) (Rf : Fin W → Option ℝ) (sg : Fin W → Option ℕ)
    (Rs : Fin W → ℝ) (h : ℕ → Fin W → Fin W → Mom P.d → ℝ) (dag : Option (Fin W → Fin 3 → Mom P.d)) (b : ℝ)
    (hb : 1 ≤ b) (hh : ∀ q ≤ p, ∀ i i', SNormR (40 * P.d) (40 * P.d) (h q i i') ≤ ENNReal.ofReal b) :
    Summable fun κ : GenDecoration G.garden P.d roots 0 =>
      FlowerP7.kgTerm P.L P.γ P.δ (fun _ _ => 1) G fix off (capWt G J p P.L kSel Rf sg Rs h dag) up 0 κ.1 := by
  set x0 : Mom P.d := (0 : Mom P.d) + latticePoint P.L n' with hx0
  set capInp : GLeaf G.garden.tree → Prop := fun ℓ => ℓ.1.1 ∈ J ∨ (G.garden.pair ℓ).1.1 ∈ J
  set ind : (GNode G.garden.tree → Mom P.d) → ℝ := fun k =>
    ∏ ℓ ∈ (inputLeaves G.garden).filter capInp, (if k ℓ.toNode = x0 then (1 : ℝ) else 0) with hind
  set M : ℝ := max 1 (selConst G J kSel Rs) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  set wt2 : (GNode G.garden.tree → Mom P.d) → ℝ := fun k => M⁻¹ * (capWt G J p P.L kSel Rf sg Rs h dag k * ind k)
    with hwt2
  set C : ℝ := b * jbr x0 ^ ((P.d + 1 : ℕ) : ℝ) with hC
  have hjx0 : 1 ≤ jbr x0 := Induct.one_le_jbr _
  have hbC : b ≤ C := le_mul_of_one_le_right (by linarith) (Real.one_le_rpow hjx0 (by positivity))
  have hC0 : 0 ≤ C := by linarith
  have hn : ∀ ℓ, G.garden.mark ℓ ≠ some MarkTag.lower := fun ℓ => by rw [hpl ℓ]; simp
  -- the domination
  have hdom : ∀ k, |wt2 k| ≤ ∏ ℓ ∈ inputLeaves G.garden, (C * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ))) := by
    intro k
    have hR0 : 0 ≤ ∏ ℓ ∈ inputLeaves G.garden, (C * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ))) :=
      Finset.prod_nonneg fun ℓ _ => mul_nonneg hC0 (Real.rpow_nonneg (Polar.jbr_pos_p _).le _)
    by_cases hall : ∀ ℓ ∈ (inputLeaves G.garden).filter capInp, k ℓ.toNode = x0
    · have hind1 : ind k = 1 := by
        rw [hind]; exact Finset.prod_eq_one fun ℓ hℓ => by rw [ite_eq_left (hall ℓ hℓ)]
      rw [hwt2]
      simp only [hind1, mul_one]
      rw [abs_mul, abs_of_pos (inv_pos.2 hM0)]
      have hw := abs_capWt_le G J p P.L kSel Rf sg Rs h dag k
      have hl : |leafProdCap G J h k| ≤ ∏ ℓ ∈ inputLeaves G.garden,
          (C * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ))) := by
        unfold leafProdCap
        rw [Finset.abs_prod]
        refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ℓ hℓ => ?_
        split_ifs with hc
        · rw [abs_one, hall ℓ (mem_filter.2 ⟨hℓ, hc⟩), hC, mul_assoc, ← Real.rpow_add (Polar.jbr_pos_p _)]
          simp only [add_neg_cancel, Real.rpow_zero, mul_one]
          exact hb
        · rw [typeProfiles_leaf]
          refine (CapsFub.abs_le_of_SNormR _ b hb (hh _ (hlay _) _ _) _).trans ?_
          exact mul_le_mul_of_nonneg_right hbC (Real.rpow_nonneg (Polar.jbr_pos_p _).le _)
      calc M⁻¹ * |capWt G J p P.L kSel Rf sg Rs h dag k|
          ≤ M⁻¹ * (selConst G J kSel Rs * |leafProdCap G J h k|) :=
            mul_le_mul_of_nonneg_left hw (inv_nonneg.2 hM0.le)
        _ ≤ M⁻¹ * (M * |leafProdCap G J h k|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
              (inv_nonneg.2 hM0.le)
        _ = |leafProdCap G J h k| := by field_simp
        _ ≤ _ := hl
    · push_neg at hall
      obtain ⟨ℓ, hℓ, hne⟩ := hall
      have hind0 : ind k = 0 := by rw [hind]; exact Finset.prod_eq_zero hℓ (if_neg hne)
      rw [hwt2]
      simp only [hind0, mul_zero, abs_zero]
      exact hR0
  have hs := CapsFub.summable_kernelGenFactor_dom' P.L P.γ P.δ hL G fix off up roots 0 hn wt2 C hC0 hdom
  -- the indicator is `1` on decorations
  have hindκ : ∀ κ : GenDecoration G.garden P.d roots 0, ind (cosetDecoration G.garden P.L 0 κ.1) = 1 := by
    intro κ
    rw [hind]
    refine Finset.prod_eq_one fun ℓ hℓ => if_pos ?_
    obtain ⟨-, hc⟩ := mem_filter.1 hℓ
    show (0 : Mom P.d) + latticePoint P.L (κ.1 ℓ.toNode) = x0
    rw [hx0]
    congr 2
    have hroot : ∀ i ∈ J, ∀ ℓ' : GLeaf G.garden.tree, ℓ'.1.1 = i → κ.1 ℓ'.toNode = n' := by
      intro i hi ℓ' hℓ'
      have hq : ℓ'.1.2 = [] := by
        have := ℓ'.2
        rw [hℓ', hJ i hi] at this
        simpa [TTree.leaves] using this
      have : ℓ'.toNode = GNode.root G.garden.tree i := Subtype.ext (Prod.ext hℓ' hq)
      rw [this, κ.2.2.1 i, hroots i hi]
    rcases hc with hc | hc
    · exact hroot _ hc ℓ rfl
    · rw [κ.2.1.2 ℓ]
      exact hroot _ hc _ rfl
  refine (hs.mul_left (M : ℂ)).congr fun κ => ?_
  have e1 := Polar.kernelGenFactor_eq_mul P.L P.γ P.δ (fun _ _ => 1) G fix off wt2 up 0 κ
  have e2 := Polar.kernelGenFactor_eq_mul P.L P.γ P.δ (fun _ _ => 1) G fix off
    (capWt G J p P.L kSel Rf sg Rs h dag) up 0 κ
  have e3 : FlowerP7.kgTerm P.L P.γ P.δ (fun _ _ => 1) G fix off (capWt G J p P.L kSel Rf sg Rs h dag) up 0 κ.1 =
      kernelGenFactor P.L P.γ P.δ (fun _ _ => 1) G fix off (capWt G J p P.L kSel Rf sg Rs h dag) up 0 κ := rfl
  rw [e3, e2, e1, hwt2]
  simp only [hindκ κ, mul_one]
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
  push_cast
  field_simp

end WaveTurbulence.Flower.CapsComp
