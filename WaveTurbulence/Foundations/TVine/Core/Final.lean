/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiIng
public import WaveTurbulence.Foundations.TVine.Core.TCap2
public import WaveTurbulence.Foundations.TVine.Core.Lemma19Ins2
public import WaveTurbulence.Foundations.TVine.Core.VineII3

/-!
# L1: the statements in their `Statement` form

* `deleteRung_holds : DeleteRungStatement` (N2 Lemma 1.9(1)), from `isTVineU_rungDel`;
* `phiType_of_II`: N2 Lemma 1.14(c′) from the (II) ladder step;
* `phiType_holds : PhiTypeStatement` (N2 Lemma 1.14(c′)), with the ladder step `vineII_rungDel` (`Core.VineII3`).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

/-- N2 Lemma 1.14(c′) from the (II) ladder step (all other ingredient steps plugged in). -/
theorem phiType_of_II
    (hII : ∀ {V : Type u} [DecidableEq V] (X : UMultigraph V) (p q a b xm xp ym yp : V) (Km Kp : Finset V)
      (μ : Bool), IsVineXU .II X p q → RungCore X a b xm xp ym yp Km Kp → a ≠ p → a ≠ q → b ≠ p → b ≠ q →
      IsVineXU .II (rungDel X a b xm xp ym yp μ) p q ∨
        (X.verts = {p, a, b, q} ∧ IsVineXU .I (rungDel X a b xm xp ym yp μ) p q ∧
          ((Km = {p} ∧ Kp = {q}) ∨ (Km = {q} ∧ Kp = {p})))) :
    PhiTypeStatement.{u} := by
  intro V _ G j₁ j₂ a b xm xp ym yp Km Kp U ks μ hB hl hD hVL h1a h1b h2a h2b haS
  exact phiType_of_ing (ingConcl_of (fun X p q a b xm xp ym yp Km Kp μ => hII X p q a b xm xp ym yp Km Kp μ)
    (fun _ _ _ _ _ _ _ _ _ _ _ μ hT hR hap haq hbp hbq hcap => isTVineU_rungDel_cap hT hR hap haq hbp hbq hcap μ))
    G j₁ j₂ a b xm xp ym yp Km Kp U ks μ hB hl hD hVL h1a h1b h2a h2b haS

/-- **N2 Lemma 1.14(c′)** (N3 §2.1, REF2 R1): `Φ(U)` is vine-like with the same kinds, or one (II) Q-block became
(I) and the gap of `Φ(U)` is cut. -/
theorem phiType_holds : PhiTypeStatement.{u} :=
  phiType_of_II fun X _ _ _ _ _ _ _ _ _ _ μ hX hR hap haq hbp hbq => vineII_rungDel (X := X) hX hR hap haq hbp hbq μ

/-- **N2 Lemma 1.9(1)** in its statement form. -/
theorem deleteRung_holds : DeleteRungStatement.{u} :=
  fun _ _ _ _ _ _ _ _ _ _ _ hT hD μ => isTVineU_rungDel hT hD μ

end WaveTurbulence.TVine.Core
