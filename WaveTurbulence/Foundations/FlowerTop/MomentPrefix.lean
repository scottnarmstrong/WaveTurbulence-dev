/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.P7Prefix

/-! Moment-order and joint-prefix bookkeeping with the frozen quantifier order. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop
open LGSpine Set Filter

theorem prefixP_lift {A : WTParams → Prop} (hA : WTPrefix A) : WTPrefixP (fun _ => A) := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hA⟩ := hA d hd γ hγ
  refine ⟨η₀, hη₀, ?_⟩
  intro η hη φin hφin τ hτ φ hsol
  obtain ⟨C₁, hC₁, ν₀, hν₀, hA⟩ := hA η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, ?_⟩
  intro ν hν
  exact ⟨0, fun Pm _ => hA ν hν⟩

/-- P7 supplies the entire couple half in the moment-order prefix of frozen v3. -/
theorem couple_clause_moment_prefix (S : FlowerSpineInputsV3) (hcount : FinalCountGateHalf) :
    WTPrefixP (fun _ P => 1 / 2 < P.γ → CoupleClauseAt P) :=
  prefixP_lift (couple_clause_prefix S hcount)

end WaveTurbulence.FlowerTop
