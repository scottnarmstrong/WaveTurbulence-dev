/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsFub.Exchange
public import WaveTurbulence.Foundations.Flower.CapsFub.Shell
public import WaveTurbulence.Foundations.Flower.CapsFub.Summ
/-! # CAPS-FUBINI: exchange of the shell `R`-integral with the flower sum at the Core-G integrand. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsFub
open Finset MeasureTheory Set GraftGen LGSpine Flower.Typed

theorem measurableSet_shellBox (w : ℕ) (L : ℝ) (j₂ : ℕ) : MeasurableSet (MkAsm.shellBox w L j₂) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem volume_shellBox_lt_top (w : ℕ) (L : ℝ) (j₂ : ℕ) : volume (MkAsm.shellBox w L j₂) < ⊤ :=
  (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top

/-- The per-garden exchange. -/
theorem garden_shell_exchange (P : WTParams) (hL : 0 < P.L) (p : ℕ) {w : ℕ}
    (dagger : Option (Fin w → Fin 3 → Mom P.d)) (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (b : ℝ) (hb : 1 ≤ b)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin w → ℝ) (j₂ : ℕ) (hj : 0 < j₂) (LG : LayeredGarden w) (hH : IsCanonH (p + 1) LG)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (up : GBranch LG.garden.tree → ℝ) (n : Fin w → (Fin P.d → ℤ)) (nfl : Fin P.d → ℤ) :
    IntegrableOn (fun R => kernelKgen P.L P.γ P.δ (fun _ _ => 1) LG fix off
      (fun k => (frontierW LG p (fun j => some (Rf j)) k * shellIntegrand LG P.L k R *
        leafProd LG h k) * (dagger.elim 1 fun c => LG.sibWeight c k)) up 0 n nfl)
      (MkAsm.shellBox w P.L j₂) ∧
    kernelKgen P.L P.γ P.δ (fun _ _ => 1) LG fix off
      (fun k => (frontierW LG p (fun j => some (Rf j)) k * LG.cutWeight2P P.L j₂ k *
        leafProd LG h k) * (dagger.elim 1 fun c => LG.sibWeight c k)) up 0 n nfl =
    ∫ R in MkAsm.shellBox w P.L j₂, kernelKgen P.L P.γ P.δ (fun _ _ => 1) LG fix off
      (fun k => (frontierW LG p (fun j => some (Rf j)) k * shellIntegrand LG P.L k R *
        leafProd LG h k) * (dagger.elim 1 fun c => LG.sibWeight c k)) up 0 n nfl := by
  obtain ⟨Cd, hCd0, hCd⟩ := exists_abs_chiD_le
  set S := MkAsm.shellBox w P.L j₂ with hSdef
  set Bsh : ℝ := ((Fintype.piFinset (Cases.stemSet LG)).card : ℝ) *
    ((2 ^ (j₂ - 1) * P.L)⁻¹ * Cd) ^ w with hBsh
  have hapos : 0 < 2 ^ (j₂ - 1) * P.L := by positivity
  have hBsh0 : 0 ≤ Bsh := by positivity
  have hlayer : ∀ a, LG.layer a ≤ p := Canon.layer_le_of_isCanonH hH
  have hn := Polar.mark_ne_lower_of_flowerGarden LG.garden hH.1
  let sibf : (GNode LG.garden.tree → Mom P.d) → ℝ := fun k => dagger.elim 1 fun c => LG.sibWeight c k
  let wt0 : (GNode LG.garden.tree → Mom P.d) → ℝ :=
    fun k => ∏ ℓ ∈ inputLeaves LG.garden, (b * jbr (k ℓ.toNode) ^ (-((P.d + 1 : ℕ) : ℝ)))
  have hwt0 : ∀ k, 0 ≤ wt0 k := fun k => Finset.prod_nonneg fun ℓ _ =>
    mul_nonneg (by linarith) (Real.rpow_nonneg (Polar.jbr_pos_p _).le _)
  have hsib : ∀ k, |sibf k| ≤ 1 := by
    intro k
    cases dagger with
    | none => simp [sibf]
    | some c => exact Polar.sibWeight_abs_le_one LG c k
  have hleaf : ∀ k, |leafProd LG h k| ≤ wt0 k := by
    intro k
    unfold leafProd
    rw [Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun ℓ _ => abs_nonneg _) fun ℓ _ => ?_
    rw [typeProfiles_leaf]
    exact abs_le_of_SNormR _ b hb (hh _ (hlayer _) _ _) _
  let g : (GNode LG.garden.tree → Mom P.d) → (Fin w → ℝ) → ℝ := fun k R =>
    (frontierW LG p (fun j => some (Rf j)) k * shellIntegrand LG P.L k R * leafProd LG h k) * sibf k
  let G : (GNode LG.garden.tree → Mom P.d) → ℝ := fun k => Bsh * wt0 k
  have hgm : ∀ k, Measurable (g k) := fun k =>
    ((measurable_const.mul (measurable_shellIntegrand LG P.L k)).mul_const _).mul_const _
  have hbd : ∀ k, ∀ R ∈ S, |g k R| ≤ |G k| := by
    intro k R hR
    have h1 := Fam.abs_frontierW_le LG p (fun j => some (Rf j)) k
    have h2 := abs_shellIntegrand_le LG P.L hL j₂ k Cd hCd R hR
    have h3 := hleaf k
    have h4 := hsib k
    rw [abs_of_nonneg (mul_nonneg hBsh0 (hwt0 k))]
    dsimp only [g]
    rw [abs_mul, abs_mul, abs_mul]
    calc _ ≤ (1 * Bsh) * wt0 k * 1 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one) h3
            (abs_nonneg _) (by rw [one_mul]; exact hBsh0)) h4 (abs_nonneg _)
            (mul_nonneg (by rw [one_mul]; exact hBsh0) (hwt0 k))
      _ = _ := by ring
  have hG : Summable (kernelGenFactor P.L P.γ P.δ (fun _ _ => 1) LG fix off G up 0
      (n := n) (nfl := nfl)) := by
    have hs := summable_kernelGenFactor_dom' P.L P.γ P.δ hL LG fix off up n nfl hn wt0 b
      (by linarith) fun k => (abs_of_nonneg (hwt0 k)).le
    refine (hs.mul_left (Bsh : ℂ)).congr fun κ => ?_
    have e1 := Flower.Polar.kernelGenFactor_eq_mul P.L P.γ P.δ (fun _ _ => 1) LG fix off G up 0 κ
    have e2 := Flower.Polar.kernelGenFactor_eq_mul P.L P.γ P.δ (fun _ _ => 1) LG fix off wt0 up 0 κ
    rw [e1, e2]
    simp only [G]
    push_cast; ring
  obtain ⟨hI, hE⟩ := kernelKgen_integral_swap P.L P.γ P.δ (fun _ _ => 1) LG fix off up 0 n nfl S
    (measurableSet_shellBox _ _ _) (volume_shellBox_lt_top _ _ _) g G hgm hbd hG
  refine ⟨hI, ?_⟩
  rw [← hE]
  congr 1
  funext k
  simp only [g]
  rw [integral_mul_const, integral_mul_const, integral_const_mul, hSdef,
    cutWeight2P_eq_shellIntegrand LG P.L hL j₂ hj k]

end WaveTurbulence.Flower.CapsFub
