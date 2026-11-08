/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkAsm.Budget

/-! # A5 MK-ASM (revised A2-R): one capped component with all premises of `MarkedComponentBoundAtI`, and its bound.

`CompData` packages the data and the premises of `MarkedComponentBoundAtI` for one irreducible capped component
(width `2R`, `|J| = R` caps): intrinsic pins (`pat`), depth selections (`kSel`), dagger (`dag`), carrier `MkCarries`
(ruling R156), twist closure at the concrete `protSkOf` (B0). It is the interface between the capped-encoding
helpers (CAPS-ID / CAPS-COMP, conditional here) and the analytic per-component bound. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.Flower.MkDefs

namespace WaveTurbulence.Flower.MkAsm

/-- One capped component: width `2R`, order `n`, cap trees `J` (`|J| = R`), the class `A` of gardens, the pattern
`pat`, the depth selections `kSel`, the dagger `dag`, and weight data, together with every premise of
`MarkedComponentBoundAtI`. -/
structure CompData (P : WTParams) (p : ℕ) (t s b : ℝ) where
  R : ℕ
  hR : 1 ≤ R
  n : ℕ
  hn : 1 ≤ n
  J : Finset (Fin (2 * R))
  hJ : J.card = R
  roots : Fin (2 * R) → (Fin P.d → ℤ)
  pat : Fin (2 * R) → FixPat
  kSel : Fin (2 * R) → Option ℕ
  A : Finset (LayeredGarden (2 * R))
  h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ
  Rf : Fin (2 * R) → Option ℝ
  σ : Fin (2 * R) → Option ℕ
  Rs : Fin (2 * R) → ℝ
  dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)
  hA : ∀ LG ∈ A, MkCarries P p n LG ∧ LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧
      CapGeo LG J p ∧ CapPatValid LG J pat p
  hplain : ∀ j, (kSel j).isSome → pat j = FixPat.plain
  hclosed : MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel))
  hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b
  hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r
  hRs : ∀ j, P.L ≤ Rs j
  hdecay : ((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖

namespace CompData

variable {P : WTParams} {p : ℕ} {t s b : ℝ}

/-- The value of the component class. -/
noncomputable def val (D : CompData P p t s b) : ℂ :=
  ∑ LG ∈ D.A, compValue P LG (fixCap LG D.J D.pat t s) (offCap LG D.J D.dag.isSome)
    (fun k => selOK LG D.J D.kSel * markedWeight LG D.J p P.L D.Rf D.σ (selCap LG D.J D.kSel) D.Rs D.h D.dag k)
    t D.roots

/-- The selected-vertex gain factor. -/
noncomputable def gain (D : CompData P p t s b) : ℝ :=
  ∏ j : Fin (2 * D.R), (if (D.kSel j).isSome then (D.Rs j)⁻¹ * (D.Rs j) ^ (-(1 / 18 : ℝ)) else 1)

/-- The per-component bound, from `MarkedComponentBoundAtI`. -/
theorem norm_val_le {B : ℝ} {Pm : ℕ} (hM : MarkedComponentBoundAtI B Pm P)
    (hγ : 1 / 2 < P.γ) {p : ℕ} (hp : p < P.D) {t s b : ℝ} (ht : t ∈ Ioo (p : ℝ) (p + 1))
    (hs : s ∈ Ioo (p : ℝ) t) (hb : 1 ≤ b) (D : CompData P p t s b)
    (hR2 : D.R ≤ 2 * Pm) (hn : D.n ≤ P.N (p + 1) ^ 4) :
    ‖D.val‖ ≤ P.L ^ (B * P.d * (2 * D.R : ℕ)) * P.δ ^ (7 * P.ν * D.n) * b ^ D.n * D.gain :=
  hM hγ p hp D.R D.hR hR2 D.n D.hn hn t ht s hs D.J D.roots D.hJ D.pat D.kSel D.A D.hA D.hplain D.hclosed
    D.h b hb D.hh D.Rf D.σ D.Rs D.dag D.hRf D.hRs D.hdecay

end CompData

end WaveTurbulence.Flower.MkAsm
