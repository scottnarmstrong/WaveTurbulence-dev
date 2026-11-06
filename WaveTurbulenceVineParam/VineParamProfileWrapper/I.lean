/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfileDegrees
import WaveTurbulenceVineParam.VineParamProfileProof.I
import Mathlib.Tactic

/-! # Source degree constraints exhaust the literal profiles of vine I -/

public section
namespace WaveTurbulence.Vine.Param.Profiles.I

private theorem outgoing_row_0 (k : Fin 1 → ℕ) : baseOutgoing .I k 0=k ⟨0,by decide⟩ := by
  change (∑ i : Fin 1, if ((baseBundles .I)[i.1]).1.1=0 then k i else
    if ((baseBundles .I)[i.1]).1.2=0 then ((baseBundles .I)[i.1]).2-k i else 0)=_
  simp [baseBundles]

private theorem outgoing_row_1 (k : Fin 1 → ℕ) : baseOutgoing .I k 1=(2-k ⟨0,by decide⟩) := by
  change (∑ i : Fin 1, if ((baseBundles .I)[i.1]).1.1=1 then k i else
    if ((baseBundles .I)[i.1]).1.2=1 then ((baseBundles .I)[i.1]).2-k i else 0)=_
  simp [baseBundles]

/-- Every normalized source-balanced orientation has an actual profile index. -/
theorem exists_profile (k : Fin (baseBundles .I).length → ℕ)
    (hk : ∀ i,k i ≤ ((baseBundles .I)[i.1]'i.2).2)
    (hb : ∀ v : Fin VineType.I.template.n,
      baseOutgoing .I k v.1=if v.1<2 then 1 else 2) :
    ∃ p : Fin (baseProfileCount .I),baseProfileCounts .I p=List.ofFn k := by
  change Fin 1 → ℕ at k
  have h0 := hk ⟨0,by decide⟩
  change k ⟨0,by decide⟩ ≤ 2 at h0
  have hbal0 := hb ⟨0,by decide⟩
  change baseOutgoing .I k 0=1 at hbal0
  rw [outgoing_row_0] at hbal0
  have hbal1 := hb ⟨1,by decide⟩
  change baseOutgoing .I k 1=1 at hbal1
  rw [outgoing_row_1] at hbal1
  obtain ⟨p,hp⟩ := exhaustive (k ⟨0,by decide⟩) h0 hbal0 hbal1
  refine ⟨p,?_⟩
  change baseProfileCounts .I p=List.ofFn (fun i : Fin 1 => k i)
  rw [hp]
  apply List.ext_getElem
  · simp only [List.length_cons,List.length_nil,List.length_ofFn]
  · intro i hi _hi2
    have hib : i<1 := by simpa only [List.length_cons,List.length_nil] using hi
    simp only [List.getElem_ofFn]
    interval_cases i; rfl

end WaveTurbulence.Vine.Param.Profiles.I
