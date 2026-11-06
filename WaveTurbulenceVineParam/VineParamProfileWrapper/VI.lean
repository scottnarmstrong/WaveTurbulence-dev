/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfileDegrees
import WaveTurbulenceVineParam.VineParamProfileProof.VI
import Mathlib.Tactic

/-! # Source degree constraints exhaust the literal profiles of vine VI -/

public section
namespace WaveTurbulence.Vine.Param.Profiles.VI

private theorem outgoing_row_0 (k : Fin 21 → ℕ) : baseOutgoing .VI k 0=k ⟨0,by decide⟩+k ⟨1,by decide⟩ := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=0 then k i else
    if ((baseBundles .VI)[i.1]).1.2=0 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ]

private theorem outgoing_row_1 (k : Fin 21 → ℕ) : baseOutgoing .VI k 1=k ⟨13,by decide⟩+k ⟨14,by decide⟩ := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=1 then k i else
    if ((baseBundles .VI)[i.1]).1.2=1 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ]

private theorem outgoing_row_2 (k : Fin 21 → ℕ) : baseOutgoing .VI k 2=(1-k ⟨0,by decide⟩)+k ⟨2,by decide⟩+k ⟨15,by decide⟩ := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=2 then k i else
    if ((baseBundles .VI)[i.1]).1.2=2 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_3 (k : Fin 21 → ℕ) : baseOutgoing .VI k 3=(1-k ⟨1,by decide⟩)+(2-k ⟨2,by decide⟩)+k ⟨16,by decide⟩ := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=3 then k i else
    if ((baseBundles .VI)[i.1]).1.2=3 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_4 (k : Fin 21 → ℕ) : baseOutgoing .VI k 4=k ⟨3,by decide⟩+k ⟨4,by decide⟩+(1-k ⟨15,by decide⟩) := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=4 then k i else
    if ((baseBundles .VI)[i.1]).1.2=4 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_5 (k : Fin 21 → ℕ) : baseOutgoing .VI k 5=(2-k ⟨3,by decide⟩)+k ⟨5,by decide⟩+(1-k ⟨16,by decide⟩) := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=5 then k i else
    if ((baseBundles .VI)[i.1]).1.2=5 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_6 (k : Fin 21 → ℕ) : baseOutgoing .VI k 6=(1-k ⟨4,by decide⟩)+k ⟨6,by decide⟩+k ⟨19,by decide⟩ := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=6 then k i else
    if ((baseBundles .VI)[i.1]).1.2=6 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_7 (k : Fin 21 → ℕ) : baseOutgoing .VI k 7=(2-k ⟨6,by decide⟩)+k ⟨7,by decide⟩+k ⟨20,by decide⟩ := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=7 then k i else
    if ((baseBundles .VI)[i.1]).1.2=7 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_8 (k : Fin 21 → ℕ) : baseOutgoing .VI k 8=(1-k ⟨5,by decide⟩)+k ⟨8,by decide⟩+k ⟨17,by decide⟩ := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=8 then k i else
    if ((baseBundles .VI)[i.1]).1.2=8 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_9 (k : Fin 21 → ℕ) : baseOutgoing .VI k 9=(1-k ⟨7,by decide⟩)+(2-k ⟨8,by decide⟩)+k ⟨18,by decide⟩ := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=9 then k i else
    if ((baseBundles .VI)[i.1]).1.2=9 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_10 (k : Fin 21 → ℕ) : baseOutgoing .VI k 10=k ⟨9,by decide⟩+k ⟨10,by decide⟩+(1-k ⟨17,by decide⟩) := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=10 then k i else
    if ((baseBundles .VI)[i.1]).1.2=10 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_11 (k : Fin 21 → ℕ) : baseOutgoing .VI k 11=(1-k ⟨9,by decide⟩)+k ⟨11,by decide⟩+(1-k ⟨18,by decide⟩) := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=11 then k i else
    if ((baseBundles .VI)[i.1]).1.2=11 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_12 (k : Fin 21 → ℕ) : baseOutgoing .VI k 12=(2-k ⟨10,by decide⟩)+(2-k ⟨11,by decide⟩) := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=12 then k i else
    if ((baseBundles .VI)[i.1]).1.2=12 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ]

private theorem outgoing_row_13 (k : Fin 21 → ℕ) : baseOutgoing .VI k 13=k ⟨12,by decide⟩+(1-k ⟨13,by decide⟩)+(1-k ⟨19,by decide⟩) := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=13 then k i else
    if ((baseBundles .VI)[i.1]).1.2=13 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

private theorem outgoing_row_14 (k : Fin 21 → ℕ) : baseOutgoing .VI k 14=(2-k ⟨12,by decide⟩)+(1-k ⟨14,by decide⟩)+(1-k ⟨20,by decide⟩) := by
  change (∑ i : Fin 21, if ((baseBundles .VI)[i.1]).1.1=14 then k i else
    if ((baseBundles .VI)[i.1]).1.2=14 then ((baseBundles .VI)[i.1]).2-k i else 0)=_
  simp [baseBundles,Fin.sum_univ_succ,Nat.add_assoc]

/-- Every normalized source-balanced orientation has an actual profile index. -/
theorem exists_profile (k : Fin (baseBundles .VI).length → ℕ)
    (hk : ∀ i,k i ≤ ((baseBundles .VI)[i.1]'i.2).2)
    (hb : ∀ v : Fin VineType.VI.template.n,
      baseOutgoing .VI k v.1=if v.1<2 then 1 else 2) :
    ∃ p : Fin (baseProfileCount .VI),baseProfileCounts .VI p=List.ofFn k := by
  change Fin 21 → ℕ at k
  have h0 := hk ⟨0,by decide⟩
  change k ⟨0,by decide⟩ ≤ 1 at h0
  have h1 := hk ⟨1,by decide⟩
  change k ⟨1,by decide⟩ ≤ 1 at h1
  have h2 := hk ⟨2,by decide⟩
  change k ⟨2,by decide⟩ ≤ 2 at h2
  have h3 := hk ⟨3,by decide⟩
  change k ⟨3,by decide⟩ ≤ 2 at h3
  have h4 := hk ⟨4,by decide⟩
  change k ⟨4,by decide⟩ ≤ 1 at h4
  have h5 := hk ⟨5,by decide⟩
  change k ⟨5,by decide⟩ ≤ 1 at h5
  have h6 := hk ⟨6,by decide⟩
  change k ⟨6,by decide⟩ ≤ 2 at h6
  have h7 := hk ⟨7,by decide⟩
  change k ⟨7,by decide⟩ ≤ 1 at h7
  have h8 := hk ⟨8,by decide⟩
  change k ⟨8,by decide⟩ ≤ 2 at h8
  have h9 := hk ⟨9,by decide⟩
  change k ⟨9,by decide⟩ ≤ 1 at h9
  have h10 := hk ⟨10,by decide⟩
  change k ⟨10,by decide⟩ ≤ 2 at h10
  have h11 := hk ⟨11,by decide⟩
  change k ⟨11,by decide⟩ ≤ 2 at h11
  have h12 := hk ⟨12,by decide⟩
  change k ⟨12,by decide⟩ ≤ 2 at h12
  have h13 := hk ⟨13,by decide⟩
  change k ⟨13,by decide⟩ ≤ 1 at h13
  have h14 := hk ⟨14,by decide⟩
  change k ⟨14,by decide⟩ ≤ 1 at h14
  have h15 := hk ⟨15,by decide⟩
  change k ⟨15,by decide⟩ ≤ 1 at h15
  have h16 := hk ⟨16,by decide⟩
  change k ⟨16,by decide⟩ ≤ 1 at h16
  have h17 := hk ⟨17,by decide⟩
  change k ⟨17,by decide⟩ ≤ 1 at h17
  have h18 := hk ⟨18,by decide⟩
  change k ⟨18,by decide⟩ ≤ 1 at h18
  have h19 := hk ⟨19,by decide⟩
  change k ⟨19,by decide⟩ ≤ 1 at h19
  have h20 := hk ⟨20,by decide⟩
  change k ⟨20,by decide⟩ ≤ 1 at h20
  have hbal0 := hb ⟨0,by decide⟩
  change baseOutgoing .VI k 0=1 at hbal0
  rw [outgoing_row_0] at hbal0
  have hbal1 := hb ⟨1,by decide⟩
  change baseOutgoing .VI k 1=1 at hbal1
  rw [outgoing_row_1] at hbal1
  have hbal2 := hb ⟨2,by decide⟩
  change baseOutgoing .VI k 2=2 at hbal2
  rw [outgoing_row_2] at hbal2
  have hbal3 := hb ⟨3,by decide⟩
  change baseOutgoing .VI k 3=2 at hbal3
  rw [outgoing_row_3] at hbal3
  have hbal4 := hb ⟨4,by decide⟩
  change baseOutgoing .VI k 4=2 at hbal4
  rw [outgoing_row_4] at hbal4
  have hbal5 := hb ⟨5,by decide⟩
  change baseOutgoing .VI k 5=2 at hbal5
  rw [outgoing_row_5] at hbal5
  have hbal6 := hb ⟨6,by decide⟩
  change baseOutgoing .VI k 6=2 at hbal6
  rw [outgoing_row_6] at hbal6
  have hbal7 := hb ⟨7,by decide⟩
  change baseOutgoing .VI k 7=2 at hbal7
  rw [outgoing_row_7] at hbal7
  have hbal8 := hb ⟨8,by decide⟩
  change baseOutgoing .VI k 8=2 at hbal8
  rw [outgoing_row_8] at hbal8
  have hbal9 := hb ⟨9,by decide⟩
  change baseOutgoing .VI k 9=2 at hbal9
  rw [outgoing_row_9] at hbal9
  have hbal10 := hb ⟨10,by decide⟩
  change baseOutgoing .VI k 10=2 at hbal10
  rw [outgoing_row_10] at hbal10
  have hbal11 := hb ⟨11,by decide⟩
  change baseOutgoing .VI k 11=2 at hbal11
  rw [outgoing_row_11] at hbal11
  have hbal12 := hb ⟨12,by decide⟩
  change baseOutgoing .VI k 12=2 at hbal12
  rw [outgoing_row_12] at hbal12
  have hbal13 := hb ⟨13,by decide⟩
  change baseOutgoing .VI k 13=2 at hbal13
  rw [outgoing_row_13] at hbal13
  have hbal14 := hb ⟨14,by decide⟩
  change baseOutgoing .VI k 14=2 at hbal14
  rw [outgoing_row_14] at hbal14
  obtain ⟨p,hp⟩ := exhaustive (k ⟨0,by decide⟩) (k ⟨1,by decide⟩) (k ⟨2,by decide⟩) (k ⟨3,by decide⟩) (k ⟨4,by decide⟩) (k ⟨5,by decide⟩) (k ⟨6,by decide⟩) (k ⟨7,by decide⟩) (k ⟨8,by decide⟩) (k ⟨9,by decide⟩) (k ⟨10,by decide⟩) (k ⟨11,by decide⟩) (k ⟨12,by decide⟩) (k ⟨13,by decide⟩) (k ⟨14,by decide⟩) (k ⟨15,by decide⟩) (k ⟨16,by decide⟩) (k ⟨17,by decide⟩) (k ⟨18,by decide⟩) (k ⟨19,by decide⟩) (k ⟨20,by decide⟩) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 hbal0 hbal1 hbal2 hbal3 hbal4 hbal5 hbal6 hbal7 hbal8 hbal9 hbal10 hbal11 hbal12 hbal13 hbal14
  refine ⟨p,?_⟩
  change baseProfileCounts .VI p=List.ofFn (fun i : Fin 21 => k i)
  rw [hp]
  apply List.ext_getElem
  · simp only [List.length_cons,List.length_nil,List.length_ofFn]
  · intro i hi _hi2
    have hib : i<21 := by simpa only [List.length_cons,List.length_nil] using hi
    simp only [List.getElem_ofFn]
    interval_cases i <;> rfl

end WaveTurbulence.Vine.Param.Profiles.VI
