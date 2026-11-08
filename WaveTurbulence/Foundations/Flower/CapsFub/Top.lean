/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsFub.Main
/-! # CAPS-FUBINI: the Core-G exchange theorem. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsFub
open Finset MeasureTheory Set Flower.Typed

theorem coreG_shell_exchange (P : WTParams) (hL : 0 < P.L) (p N : ℕ) {w : ℕ} (kind : FlowerKind)
    (dagger : Option (Fin w → Fin 3 → Mom P.d)) (h : ℕ → Fin w → Fin w → Mom P.d → ℝ) (b : ℝ) (hb : 1 ≤ b)
    (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin w → ℝ) (hRf : ∀ j, P.L / 2 ≤ Rf j) (j₂ : ℕ) (hj : 0 < j₂)
    (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) :
    FC23.flowerWeighted P (fun _ _ => 1) p N kind (fun _ => .plain) dagger
      (fun LG k => Typed.frontierW LG p (fun j => some (Rf j)) k * LG.cutWeight2P P.L j₂ k *
        Typed.leafProd LG h k) ζ t s n n' =
      ∫ R in MkAsm.shellBox w P.L j₂,
        FC23.flowerWeighted P (fun _ _ => 1) p N kind (fun _ => .plain) dagger
          (fun LG k => Typed.frontierW LG p (fun j => some (Rf j)) k * shellIntegrand LG P.L k R *
            Typed.leafProd LG h k) ζ t s n n' := by
  simp only [FC23.flowerWeighted_eq_sum]
  have hmem : ∀ LG ∈ (FC23.flowerCarrier_finite (w := w) P p N kind (fun _ => FixPat.plain) ζ).toFinset,
      IsCanonH (p + 1) LG := fun LG hLG =>
    ((FC23.flowerCarrier_finite (w := w) P p N kind (fun _ => FixPat.plain) ζ).mem_toFinset.mp hLG).1
  have hex := fun (LG : LayeredGarden w) (hLG : LG ∈ (FC23.flowerCarrier_finite (w := w) P p N kind (fun _ => FixPat.plain) ζ).toFinset) =>
    garden_shell_exchange P hL p dagger h b hb hh Rf j₂ hj LG (hmem LG hLG)
      (LG.fixPat (fun _ => FixPat.plain) t s)
      (if dagger.isSome then Finset.univ.filter LG.garden.IsFlowerParent else ∅) (fun _ => t)
      (fun _ => n) n'
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun LG hLG => (hex LG hLG).2
  · exact fun LG hLG => (hex LG hLG).1

end WaveTurbulence.Flower.CapsFub
