/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.FlSepApp
public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Prefix
public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.Orders
public import WaveTurbulence.Foundations.FlowerTop.LogAbsorption

/-! # B4 STAGE1MK-GATE: zero classes vanish, and the gate

* `zeroVanishAt`: `ZeroVanish P` at parameters with `L ≥ 4`, `η ≤ γ`, `8 N_{p+1}^4 + 8 ≤ L` (all `p < 𝔇`): every point
  of a fine′ class containing a stem-unclean point is stem-unclean (`notClean_iff_of_related`, B2e's `X` transport),
  so the weight vanishes on each selected decoration (`markedWt_zero_of_unclean`, B2e's per-tree FL-SEP) and every
  `kernelKgenSel` term of the class value is `0`.
* `zeroVanish_prefix : WTPrefix ZeroVanish` (`n ≤ N_{p+1}^4` is polylogarithmic: `Regref.le_logPow_ordExp`).
* `b2eIX : B2eIX` (B2e's `fineTransportedAt_markIX`).
* **`stage1ReductionAtMKFull_of_B3s`** and **`stage1ReductionAtMK_of_B3s`**: the marked Stage-1′ gate (Full form, and
  the frozen form at `cP + 343`) from the single remaining input `WTPrefix (MarkedClassRepresentsMK cP cθ)` (B3s). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA
open WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents Set Finset

namespace WaveTurbulence.Flower.Stage1MKGate

/-- **Zero classes vanish** at parameters with `L ≥ 4`, `η ≤ γ` and `8 N_{p+1}^4 + 8 ≤ L`. -/
theorem zeroVanishAt (P : WTParams) (hL4 : 4 ≤ P.L) (hηγ : P.η ≤ P.γ)
    (hbig : ∀ p, p < P.D → 8 * ((P.N (p + 1) ^ 4 : ℕ) : ℝ) + 8 ≤ P.L) : ZeroVanish P := by
  intro p hp R hR hRmax N hN1 hNb J pat kSel t ht s hs A hA roots h b Rf σ Rs dag hRf hhigh π hS ⟨a, hra, hna⟩
  unfold classValue
  refine Finset.sum_eq_zero fun LG hLG => ?_
  have hLGA : LG ∈ A := (Finset.mem_filter.1 hLG).1
  have hterm : ∀ κ : GenDecoration LG.garden P.d roots 0,
      selPMk p (objKind (2 * R)) A P 0 roots (fineMk J pat t s kSel σ) π LG κ →
      markedWt P J p kSel h Rf σ Rs dag LG (cosetDecoration LG.garden P.L 0 κ.1) = 0 := by
    rintro κ ⟨b', hb', hrb', hsel⟩
    subst hb'
    have hrel : Related (p := p) (kind := objKind (2 * R)) a b' (fineMk J pat t s kSel σ) :=
      Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ hra) hrb'
    have hun' : ¬ CleanPt J b' := (notClean_iff_of_related J pat t s kSel σ hS hrel).mp hna
    exact markedWt_zero_of_unclean P b' (hA _ hLGA) roots h Rf σ Rs dag hRf hhigh hS hun' hL4 hηγ (hbig p hp) κ hsel
  have hz : (∑' κ : GenDecoration LG.garden P.d roots 0,
      if selPMk p (objKind (2 * R)) A P 0 roots (fineMk J pat t s kSel σ) π LG κ then
        (epsDec LG.garden κ.1 : ℂ) *
          (markedWt P J p kSel h Rf σ Rs dag LG (cosetDecoration LG.garden P.L 0 κ.1) : ℂ) *
          (∫ τ : {b : GBranch LG.garden.tree // fixCap LG J pat t s b = none} → ℝ,
            (kDomainFix LG (fun _ => t) (fixCap LG J pat t s)).indicator
              (phaseProdOff P.L P.γ P.δ LG.garden (offCap LG J dag.isSome)
                (cosetDecoration LG.garden P.L 0 κ.1))
              (LG.garden.extendFix (fixCap LG J pat t s) τ)) else 0) = 0 := by
    refine (tsum_congr fun κ => ?_).trans tsum_zero
    split_ifs with hk
    · rw [hterm κ hk, Complex.ofReal_zero, mul_zero, zero_mul]
    · rfl
  unfold kernelKgenSel
  rw [hz, mul_zero]

/-- **`WTPrefix ZeroVanish`.** -/
theorem zeroVanish_prefix : WTPrefix ZeroVanish := by
  intro d hd γ hγ
  refine ⟨γ, hγ.1, fun η hη φin hφin τ hτ φ hφ => ⟨1, le_rfl, 1, one_pos, fun ν hν => ⟨1, one_pos,
    fun δ hδ D hD hτD => ?_⟩⟩⟩
  obtain ⟨L₁, hL₁⟩ := Filter.eventually_atTop.mp
    (FlowerTop.eventually_constant_log_pow_le 16 (Regref.ordExp d D) one_pos)
  refine ⟨1, le_rfl, max (max 4 L₁) (Real.exp 1),
    le_trans (by norm_num) (le_max_of_le_left (le_max_left _ _)), fun L hL => ?_⟩
  have hL4 : 4 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hL)
  have hLL₁ : L₁ ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL)
  have hLe : Real.exp 1 ≤ L := (le_max_right _ _).trans hL
  have hlog : 1 ≤ Real.log L := (Real.le_log_iff_exp_le (by linarith)).mpr hLe
  refine zeroVanishAt _ hL4 hη.2 fun p _ => ?_
  have hn := Regref.le_logPow_ordExp (⟨d, γ, η, φin, τ, φ, 1, ν, δ, D, 1, L⟩ : WTParams) (by show 1 ≤ d; omega)
    hlog p _ le_rfl
  rw [Real.rpow_natCast] at hn
  obtain ⟨-, hC⟩ := hL₁ L hLL₁
  rw [Real.rpow_one] at hC
  have h1 : 1 ≤ Real.log L ^ (Regref.ordExp d D) := one_le_pow₀ hlog
  have hn' : (((⟨d, γ, η, φin, τ, φ, 1, ν, δ, D, 1, L⟩ : WTParams).N (p + 1) ^ 4 : ℕ) : ℝ) ≤
      Real.log L ^ (Regref.ordExp d D) := hn
  show 8 * (((⟨d, γ, η, φin, τ, φ, 1, ν, δ, D, 1, L⟩ : WTParams).N (p + 1) ^ 4 : ℕ) : ℝ) + 8 ≤ L
  linarith

/-- B2e's fine transport of `markIX` (`MkMarkX.fineTransportedAt_markIX`). -/
theorem b2eIX : B2eIX := fun J pat t s kSel a => MkMarkX.fineTransportedAt_markIX J pat t s kSel a

/-- **The marked Stage-1′ gate, Full form (rulings R177–R180)**, from B3s's hypothesis alone. -/
theorem stage1ReductionAtMKFull_of_B3s (cP cθ : ℝ) (hB : WTPrefix (MarkedClassRepresentsMK cP cθ)) :
    ∃ C₀ : ℕ, 2 ≤ C₀ ∧ WTPrefix (Stage1ReductionAtMKFull C₀ cP cθ) :=
  stage1ReductionAtMKFull_of cP cθ hB b2eIX zeroVanish_prefix

/-- **The frozen form** `MkDefs.Stage1ReductionAtMK` (R177/R180 text) at `cP + 343`, from B3s's hypothesis alone. -/
theorem stage1ReductionAtMK_of_B3s (cP cθ : ℝ) (hB : WTPrefix (MarkedClassRepresentsMK cP cθ)) :
    ∃ C₀ : ℕ, 2 ≤ C₀ ∧ WTPrefix (Stage1ReductionAtMK C₀ (cP + 343)) :=
  stage1ReductionAtMK_of cP cθ hB b2eIX zeroVanish_prefix

end WaveTurbulence.Flower.Stage1MKGate
