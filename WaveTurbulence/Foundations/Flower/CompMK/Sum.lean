/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CompMK.Defs
public import WaveTurbulence.Foundations.Flower.CapsComp.Summ

/-! # C5b COMP-MK: the component sum is the sum of the Stage-1′ piece values

* `summable_kgTerm_capWt_gen`: A3b's `CapsComp.summable_kgTerm_capWt` (copied by source, see `COPIED-SHA256SUMS`)
  with arbitrary cap roots (the original fixes one cap momentum `n'` for all caps): the cap pairs carry the momentum
  of their own cap tree.
* `kernelKgen_eq_sum_sel`: main's `kernelLeavesTerm_sum_sel` for `kernelKgen`/`kernelKgenSel` (the σ-indicator
  partition of the decoration sum).
* `sum_compValue_eq_sum_pieces`: main's `sum_eq_sum_pieces` for capped components. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsComp GraftGen

namespace WaveTurbulence.Flower.CompMK

variable {W : ℕ}

/-- The cap tree a cap-pair input leaf is attached to. -/
def capTreeOf (G : LayeredGarden W) (J : Finset (Fin W)) (ℓ : GLeaf G.garden.tree) : Fin W :=
  if ℓ.1.1 ∈ J then ℓ.1.1 else (G.garden.pair ℓ).1.1

-- [copied, generalized] CapsComp/Summ.lean (sha256 8b8d94f6…) L65-160: `n'`/`hroots` replaced by the per-leaf cap
-- momentum `capTreeOf`, and `C := b ∏_j ⟨x_j⟩^{d+1}`.
/-- **Summability of the component summands**, arbitrary cap roots. -/
theorem summable_kgTerm_capWt_gen (P : WTParams) (hL : 0 < P.L) {p : ℕ} (G : LayeredGarden W)
    (hpl : G.garden.IsPlain) (hlay : ∀ a, G.layer a ≤ p) (J : Finset (Fin W))
    (hJ : ∀ i ∈ J, G.garden.tree i = TTree.leaf) (roots : Fin W → (Fin P.d → ℤ))
    (fix : GBranch G.garden.tree → Option ℝ) (off : Finset (GBranch G.garden.tree))
    (up : GBranch G.garden.tree → ℝ) (kSel : Fin W → Option ℕ) (Rf : Fin W → Option ℝ) (sg : Fin W → Option ℕ)
    (Rs : Fin W → ℝ) (h : ℕ → Fin W → Fin W → Mom P.d → ℝ) (dag : Option (Fin W → Fin 3 → Mom P.d)) (b : ℝ)
    (hb : 1 ≤ b) (hh : ∀ q ≤ p, ∀ i i', SNormR (40 * P.d) (40 * P.d) (h q i i') ≤ ENNReal.ofReal b) :
    Summable fun κ : GenDecoration G.garden P.d roots 0 =>
      FlowerP7.kgTerm P.L P.γ P.δ (fun _ _ => 1) G fix off (capWt G J p P.L kSel Rf sg Rs h dag) up 0 κ.1 := by
  set xr : Fin W → Mom P.d := fun j => (0 : Mom P.d) + latticePoint P.L (roots j) with hxr
  set capInp : GLeaf G.garden.tree → Prop := fun ℓ => ℓ.1.1 ∈ J ∨ (G.garden.pair ℓ).1.1 ∈ J
  set ind : (GNode G.garden.tree → Mom P.d) → ℝ := fun k =>
    ∏ ℓ ∈ (inputLeaves G.garden).filter capInp,
      (if k ℓ.toNode = xr (capTreeOf G J ℓ) then (1 : ℝ) else 0) with hind
  set M : ℝ := max 1 (selConst G J kSel Rs) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  set wt2 : (GNode G.garden.tree → Mom P.d) → ℝ := fun k => M⁻¹ * (capWt G J p P.L kSel Rf sg Rs h dag k * ind k)
    with hwt2
  set Qr0 : ℝ := ∏ j : Fin W, jbr (xr j) ^ ((P.d + 1 : ℕ) : ℝ) with hQr0
  have hjx : ∀ j, 1 ≤ jbr (xr j) ^ ((P.d + 1 : ℕ) : ℝ) := fun j =>
    Real.one_le_rpow (Induct.one_le_jbr _) (by positivity)
  have hQr1 : 1 ≤ Qr0 := Finset.one_le_prod₀ fun j _ => hjx j
  have hQrj : ∀ j, jbr (xr j) ^ ((P.d + 1 : ℕ) : ℝ) ≤ Qr0 := fun j => by
    rw [hQr0, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    exact le_mul_of_one_le_right (by linarith [hjx j]) (Finset.one_le_prod₀ fun i _ => hjx i)
  set C : ℝ := b * Qr0 with hC
  have hbC : b ≤ C := le_mul_of_one_le_right (by linarith) hQr1
  have hC0 : 0 ≤ C := by linarith
  have hn : ∀ ℓ, G.garden.mark ℓ ≠ some MarkTag.lower := fun ℓ => by rw [hpl ℓ]; simp
  -- the domination
  have hdom : ∀ k, |wt2 k| ≤ ∏ ℓ ∈ inputLeaves G.garden, (C * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ))) := by
    intro k
    have hR0 : 0 ≤ ∏ ℓ ∈ inputLeaves G.garden, (C * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ))) :=
      Finset.prod_nonneg fun ℓ _ => mul_nonneg hC0 (Real.rpow_nonneg (Polar.jbr_pos_p _).le _)
    by_cases hall : ∀ ℓ ∈ (inputLeaves G.garden).filter capInp, k ℓ.toNode = xr (capTreeOf G J ℓ)
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
        · rw [abs_one, hall ℓ (mem_filter.2 ⟨hℓ, hc⟩)]
          have hpos : 0 < jbr (xr (capTreeOf G J ℓ)) ^ ((P.d + 1 : ℕ) : ℝ) :=
            Real.rpow_pos_of_pos (Polar.jbr_pos_p _) _
          have hinv : jbr (xr (capTreeOf G J ℓ)) ^ (-((P.d + 1 : ℕ) : ℝ)) =
              (jbr (xr (capTreeOf G J ℓ)) ^ ((P.d + 1 : ℕ) : ℝ))⁻¹ :=
            Real.rpow_neg (Polar.jbr_pos_p _).le _
          rw [hinv, ← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
          calc jbr (xr (capTreeOf G J ℓ)) ^ ((P.d + 1 : ℕ) : ℝ) ≤ Qr0 := hQrj _
            _ ≤ C := le_mul_of_one_le_left (by linarith) hb
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
    show (0 : Mom P.d) + latticePoint P.L (κ.1 ℓ.toNode) = xr (capTreeOf G J ℓ)
    rw [hxr]
    congr 2
    have hroot : ∀ i ∈ J, ∀ ℓ' : GLeaf G.garden.tree, ℓ'.1.1 = i → κ.1 ℓ'.toNode = roots i := by
      intro i hi ℓ' hℓ'
      have hq : ℓ'.1.2 = [] := by
        have := ℓ'.2
        rw [hℓ', hJ i hi] at this
        simpa [TTree.leaves] using this
      have : ℓ'.toNode = GNode.root G.garden.tree i := Subtype.ext (Prod.ext hℓ' hq)
      rw [this, κ.2.2.1 i]
    unfold capTreeOf
    by_cases h1 : ℓ.1.1 ∈ J
    · rw [if_pos h1]; exact hroot _ h1 ℓ rfl
    · rw [if_neg h1]
      have hc' : (G.garden.pair ℓ).1.1 ∈ J := hc.resolve_left h1
      rw [κ.2.1.2 ℓ]
      exact hroot _ hc' _ rfl
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
-- [end copied]

/-- The σ-indicator partition for `kernelKgen` (input `F ≡ 1`): main's `kernelLeavesTerm_sum_sel`. -/
theorem kernelKgen_eq_sum_sel {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden W) (fix : GBranch LG.garden.tree → Option ℝ)
    (off : Finset (GBranch LG.garden.tree)) (wt : (GNode LG.garden.tree → Mom d) → ℝ)
    (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d) (roots : Fin W → (Fin d → ℤ)) {ι : Type*} (t : Finset ι)
    (sel : ι → GenDecoration LG.garden d roots 0 → Prop) (hpart : ∀ κ, ∃! i, i ∈ t ∧ sel i κ)
    (hsum : Summable fun κ : GenDecoration LG.garden d roots 0 =>
      FlowerP7.kgTerm L γ δ (fun _ _ => 1) LG fix off wt up k₀ κ.1) :
    kernelKgen L γ δ (fun _ _ => 1) LG fix off wt up k₀ roots 0 =
      ∑ i ∈ t, kernelKgenSel L γ δ LG fix off wt up k₀ roots (sel i) := by
  have hterm : ∀ κ : GenDecoration LG.garden d roots 0,
      FlowerP7.kgTerm L γ δ (fun _ _ => 1) LG fix off wt up k₀ κ.1 =
        (epsDec LG.garden κ.1 : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
          (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
            (kDomainFix LG up fix).indicator
              (phaseProdOff L γ δ LG.garden off (cosetDecoration LG.garden L k₀ κ.1))
              (LG.garden.extendFix fix τ)) := by
    intro κ
    simp [FlowerP7.kgTerm]
  have hsel : ∀ i, Summable fun κ : GenDecoration LG.garden d roots 0 =>
      if sel i κ then (epsDec LG.garden κ.1 : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
          (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
            (kDomainFix LG up fix).indicator
              (phaseProdOff L γ δ LG.garden off (cosetDecoration LG.garden L k₀ κ.1))
              (LG.garden.extendFix fix τ)) else 0 := by
    intro i
    have := hsum.indicator {κ | sel i κ}
    refine this.congr fun κ => ?_
    by_cases h : sel i κ <;> simp [Set.indicator, h, hterm]
  unfold kernelKgen kernelKgenSel
  rw [← Finset.mul_sum, ← Summable.tsum_finsetSum (fun i _ => hsel i)]
  congr 1
  refine tsum_congr fun κ => ?_
  obtain ⟨i0, ⟨hi0, hs0⟩, huniq⟩ := hpart κ
  rw [Finset.sum_eq_single i0]
  · simp [hs0]
  · intro j hj hne
    have : ¬ sel j κ := fun h => hne (huniq j ⟨hj, h⟩)
    simp [this]
  · intro h; exact absurd hi0 h

/-- **The component sum is the sum of the piece values** (main's `sum_eq_sum_pieces`), for any
`Stage1Partition` whose pieces are the σ-restricted kernels and whose gardens have summable decoration sums. -/
theorem sum_compValue_eq_sum_pieces (P : WTParams) {R : ℕ} {Pc Cl : Type} [Fintype Pc] [Fintype Cl]
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (A : Finset (LayeredGarden (2 * R)))
    (members : Cl → Finset (LayeredGarden (2 * R))) (cls : Pc → Cl)
    (sel : Pc → ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → Prop)
    (hpart : Stage1Partition roots A members cls sel) (t : ℝ)
    (fix : ∀ LG : LayeredGarden (2 * R), GBranch LG.garden.tree → Option ℝ)
    (off : ∀ LG : LayeredGarden (2 * R), Finset (GBranch LG.garden.tree))
    (wt : ∀ LG : LayeredGarden (2 * R), (GNode LG.garden.tree → Mom P.d) → ℝ) (val : Pc → ℂ)
    (hval : ∀ π, val π = ∑ LG ∈ members (cls π),
      kernelKgenSel P.L P.γ P.δ LG (fix LG) (off LG) (wt LG) (fun _ => t) 0 roots (sel π LG))
    (hsum : ∀ LG ∈ A, Summable fun κ : GenDecoration LG.garden P.d roots 0 =>
      FlowerP7.kgTerm P.L P.γ P.δ (fun _ _ => 1) LG (fix LG) (off LG) (wt LG) (fun _ => t) 0 κ.1) :
    ∑ LG ∈ A, compValue P LG (fix LG) (off LG) (wt LG) t roots = ∑ π, val π := by
  have hA : A = Finset.univ.biUnion members := by
    ext LG; simp [hpart.1 LG]
  have e1 : ∑ LG ∈ A, compValue P LG (fix LG) (off LG) (wt LG) t roots =
      ∑ c, ∑ LG ∈ members c, compValue P LG (fix LG) (off LG) (wt LG) t roots := by
    rw [hA, Finset.sum_biUnion]
    intro c _ c' _ hne
    exact hpart.2.1 c c' hne
  rw [e1, ← Finset.sum_fiberwise (s := Finset.univ) (g := cls)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hmem : ∀ LG ∈ members c, LG ∈ A := fun LG hLG => (hpart.1 LG).2 ⟨c, hLG⟩
  calc ∑ LG ∈ members c, compValue P LG (fix LG) (off LG) (wt LG) t roots
      = ∑ LG ∈ members c, ∑ π ∈ Finset.univ.filter (fun π => cls π = c),
          kernelKgenSel P.L P.γ P.δ LG (fix LG) (off LG) (wt LG) (fun _ => t) 0 roots (sel π LG) := by
        refine Finset.sum_congr rfl fun LG hLG => ?_
        refine kernelKgen_eq_sum_sel P.L P.γ P.δ LG (fix LG) (off LG) (wt LG) (fun _ => t) 0 roots
          (Finset.univ.filter (fun π => cls π = c)) (fun π => sel π LG) (fun κ => ?_) (hsum LG (hmem LG hLG))
        obtain ⟨π, ⟨hπ1, hπ2⟩, hu⟩ := hpart.2.2 c LG hLG κ
        exact ⟨π, ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hπ1⟩, hπ2⟩,
          fun π' ⟨hπ', hs'⟩ => hu π' ⟨(Finset.mem_filter.mp hπ').2, hs'⟩⟩
    _ = ∑ π ∈ Finset.univ.filter (fun π => cls π = c), ∑ LG ∈ members (cls π),
          kernelKgenSel P.L P.γ P.δ LG (fix LG) (off LG) (wt LG) (fun _ => t) 0 roots (sel π LG) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun π hπ => ?_
        rw [(Finset.mem_filter.mp hπ).2]
    _ = ∑ π ∈ Finset.univ.filter (fun π => cls π = c), val π :=
        Finset.sum_congr rfl fun π _ => (hval π).symm

end WaveTurbulence.Flower.CompMK
