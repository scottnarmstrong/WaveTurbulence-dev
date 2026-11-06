/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfiles
import Mathlib.Tactic

/-! # Exhaustive orientation classification of base vine I

The natural counts satisfy only multiplicity bounds and the actual outgoing
vertex degrees (one at joints, two elsewhere). Each branch follows from
these source equations. No enumerator or external arithmetic oracle is used.
-/

public section
namespace WaveTurbulence.Vine.Param.Profiles.I

private theorem case0 (q0 : ℕ) (h0 : q0 ≤ 2) (hb0 : q0=1) (hb1 : (2-q0)=1) :
    ∃ p : Fin (baseProfileCount .I),baseProfileCounts .I p=[q0] := by
  have he : q0=1 := by omega
  subst q0
  exact ⟨⟨0,by decide⟩,rfl⟩

/-- Every source-balanced bundle orientation occurs in the finite profile list. -/
theorem exhaustive (q0 : ℕ) (h0 : q0 ≤ 2) (hb0 : q0=1) (hb1 : (2-q0)=1) :
    ∃ p : Fin (baseProfileCount .I),baseProfileCounts .I p=[q0] := by
  exact case0 q0 h0 hb0 hb1

end WaveTurbulence.Vine.Param.Profiles.I
