/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfileDegrees
import WaveTurbulenceVineParam.VineParamProfileProof.II
import Mathlib.Tactic

/-! # Source degree constraints exhaust the literal profiles of vine II -/

public section
namespace WaveTurbulence.Vine.Param.Profiles.II

private theorem outgoing_row_0 (k : Fin 5 → ℕ) : baseOutgoing .II k 0=k ⟨0,by decide⟩+k ⟨1,by decide⟩ := by
  change (∑ i : Fin 5, if ((baseBundles .II)[i.1]).1.1=0 then k i else
    if ((baseBundles .II)[i.1]).1.2=0 then ((baseBundles .II)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ]

private theorem outgoing_row_1 (k : Fin 5 → ℕ) : baseOutgoing .II k 1=k ⟨3,by decide⟩+k ⟨4,by decide⟩ := by
  change (∑ i : Fin 5, if ((baseBundles .II)[i.1]).1.1=1 then k i else
    if ((baseBundles .II)[i.1]).1.2=1 then ((baseBundles .II)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ]

private theorem outgoing_row_2 (k : Fin 5 → ℕ) : baseOutgoing .II k 2=(1-k ⟨0,by decide⟩)+k ⟨2,by decide⟩+(1-k ⟨3,by decide⟩) := by
  change (∑ i : Fin 5, if ((baseBundles .II)[i.1]).1.1=2 then k i else
    if ((baseBundles .II)[i.1]).1.2=2 then ((baseBundles .II)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_3 (k : Fin 5 → ℕ) : baseOutgoing .II k 3=(1-k ⟨1,by decide⟩)+(2-k ⟨2,by decide⟩)+(1-k ⟨4,by decide⟩) := by
  change (∑ i : Fin 5, if ((baseBundles .II)[i.1]).1.1=3 then k i else
    if ((baseBundles .II)[i.1]).1.2=3 then ((baseBundles .II)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

/-- Every normalized source-balanced orientation has an actual profile index. -/
theorem exists_profile (k : Fin (baseBundles .II).length → ℕ)
    (hk : ∀ i,k i ≤ ((baseBundles .II)[i.1]'i.2).2)
    (hb : ∀ v : Fin VineType.II.template.n,
      baseOutgoing .II k v.1=if v.1<2 then 1 else 2) :
    ∃ p : Fin (baseProfileCount .II),baseProfileCounts .II p=List.ofFn k := by
  change Fin 5 → ℕ at k
  have h0 := hk ⟨0,by decide⟩
  change k ⟨0,by decide⟩ ≤ 1 at h0
  have h1 := hk ⟨1,by decide⟩
  change k ⟨1,by decide⟩ ≤ 1 at h1
  have h2 := hk ⟨2,by decide⟩
  change k ⟨2,by decide⟩ ≤ 2 at h2
  have h3 := hk ⟨3,by decide⟩
  change k ⟨3,by decide⟩ ≤ 1 at h3
  have h4 := hk ⟨4,by decide⟩
  change k ⟨4,by decide⟩ ≤ 1 at h4
  have hbal0 := hb ⟨0,by decide⟩
  change baseOutgoing .II k 0=1 at hbal0
  rw [outgoing_row_0] at hbal0
  have hbal1 := hb ⟨1,by decide⟩
  change baseOutgoing .II k 1=1 at hbal1
  rw [outgoing_row_1] at hbal1
  have hbal2 := hb ⟨2,by decide⟩
  change baseOutgoing .II k 2=2 at hbal2
  rw [outgoing_row_2] at hbal2
  have hbal3 := hb ⟨3,by decide⟩
  change baseOutgoing .II k 3=2 at hbal3
  rw [outgoing_row_3] at hbal3
  obtain ⟨p,hp⟩ := exhaustive (k ⟨0,by decide⟩) (k ⟨1,by decide⟩) (k ⟨2,by decide⟩) (k ⟨3,by decide⟩) (k ⟨4,by decide⟩) h0 h1 h2 h3 h4 hbal0 hbal1 hbal2 hbal3
  refine ⟨p,?_⟩
  change baseProfileCounts .II p=List.ofFn (fun i : Fin 5 => k i)
  rw [hp]
  apply List.ext_getElem
  · simp only [List.length_cons,List.length_nil,List.length_ofFn]
  · intro i hi _hi2
    have hib : i<5 := by simpa only [List.length_cons,List.length_nil] using hi
    simp only [List.getElem_ofFn]
    interval_cases i <;> rfl

end WaveTurbulence.Vine.Param.Profiles.II
