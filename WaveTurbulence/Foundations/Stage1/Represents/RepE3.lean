/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.CarriesW
public import WaveTurbulence.Foundations.Stage1.Represents.RepE2

/-!
# S2 REPRESENTS, VINE-E (3): the object kind of a Stage 1 carrier (VINEEST's `CanonicalObject p kind` premise, R57)

A Stage 1 carrier is canonical in `𝒢_{p+1} ∪ 𝒞_{p+1}` (`IsCanonGC (p+1)`).  Width `≥ 4`: it is a canonical garden
(`CanonicalObject p true`); width `2`: a canonical couple (`CanonicalObject p false`, signature `(+, -)`).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.LFTwist WaveTurbulence.LGSpine

/-- The object kind of a canonical layered garden of width `w`: gardens for `w ≥ 4`, couples for `w = 2`. -/
def objKind (w : ℕ) : Bool := decide (4 ≤ w)

theorem canonicalObject_of_isCanonGC {w p : ℕ} {LG : LayeredGarden w} (hc : IsCanonGC (p + 1) LG) :
    CanonicalObject p (objKind w) LG := by
  obtain ⟨hplain, hcase, hcrit⟩ := hc
  rcases hcase with ⟨h4, hirr⟩ | ⟨h2, hsig⟩
  · have hk : objKind w = true := decide_eq_true h4
    rw [hk]
    exact .garden ⟨h4, hplain, hirr, hcrit⟩
  · subst h2
    have hk : objKind 2 = false := by decide
    rw [hk]
    refine .couple ⟨⟨hplain, ?_⟩, hcrit⟩
    funext j
    fin_cases j
    · simpa using hsig 0
    · simpa using hsig 1

/-- B1b (R156): the canonical object from the truncation-free carrier. -/
theorem canonicalObject_of_carriesW {P : WTParams} {p N R : ℕ} {LG : LayeredGarden (2 * R)}
    (h : Stage1Mk.Stage1CarriesW P p N LG) : CanonicalObject p (objKind (2 * R)) LG :=
  canonicalObject_of_isCanonGC h.1

theorem canonicalObject_of_carries {P : WTParams} {p N R : ℕ} {LG : LayeredGarden (2 * R)}
    (h : Stage1Carries P p N LG) : CanonicalObject p (objKind (2 * R)) LG :=
  canonicalObject_of_isCanonGC h.1

end WaveTurbulence.Represents
