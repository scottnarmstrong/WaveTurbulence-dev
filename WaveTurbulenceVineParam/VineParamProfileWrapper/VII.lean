/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamProfileDegrees
import WaveTurbulenceVineParam.VineParamProfileProof.VII
import Mathlib.Tactic

/-! # Source degree constraints exhaust the literal profiles of vine VII -/

public section
namespace WaveTurbulence.Vine.Param.Profiles.VII

private theorem outgoing_row_0 (k : Fin 16 → ℕ) : baseOutgoing .VII k 0=k ⟨0,by decide⟩+k ⟨1,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=0 then k i else
    if ((baseBundles .VII)[i.1]).1.2=0 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, ↓reduceIte, Fin.val_succ, List.getElem_cons_succ, Fin.succ_zero_eq_one,
    OfNat.ofNat_ne_zero, one_ne_zero, Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add,
    Finset.sum_const_zero, add_zero, Fin.zero_eta, Fin.mk_one]

private theorem outgoing_row_1 (k : Fin 16 → ℕ) : baseOutgoing .VII k 1=k ⟨8,by decide⟩+k ⟨9,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=1 then k i else
    if ((baseBundles .VII)[i.1]).1.2=1 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, zero_ne_one, ↓reduceIte, OfNat.ofNat_ne_one, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Finset.univ_unique, Fin.default_eq_zero,
    Fin.val_eq_zero, zero_add, Finset.sum_const_zero, add_zero, Fin.reduceFinMk]

private theorem outgoing_row_2 (k : Fin 16 → ℕ) : baseOutgoing .VII k 2=(1-k ⟨0,by decide⟩)+k ⟨2,by decide⟩+k ⟨10,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=2 then k i else
    if ((baseBundles .VII)[i.1]).1.2=2 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Fin.val_succ, List.getElem_cons_succ, Nat.succ_ne_self,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.reduceEqDiff, OfNat.one_ne_ofNat, Fin.reduceSucc,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_const_zero, add_zero,
    Fin.zero_eta, Fin.reduceFinMk, Nat.add_assoc]

private theorem outgoing_row_3 (k : Fin 16 → ℕ) : baseOutgoing .VII k 3=(1-k ⟨1,by decide⟩)+(2-k ⟨2,by decide⟩)+k ⟨11,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=3 then k i else
    if ((baseBundles .VII)[i.1]).1.2=3 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.reduceEqDiff, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Nat.succ_ne_self, OfNat.one_ne_ofNat, Fin.reduceSucc,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_const_zero, add_zero, Fin.mk_one,
    Fin.reduceFinMk, Nat.add_assoc]

private theorem outgoing_row_4 (k : Fin 16 → ℕ) : baseOutgoing .VII k 4=k ⟨3,by decide⟩+k ⟨4,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=4 then k i else
    if ((baseBundles .VII)[i.1]).1.2=4 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.reduceEqDiff, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Nat.succ_ne_self, OfNat.one_ne_ofNat,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_const_zero, add_zero,
    Fin.reduceFinMk]

private theorem outgoing_row_5 (k : Fin 16 → ℕ) : baseOutgoing .VII k 5=(2-k ⟨3,by decide⟩)+k ⟨5,by decide⟩+k ⟨12,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=5 then k i else
    if ((baseBundles .VII)[i.1]).1.2=5 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.reduceEqDiff, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Nat.succ_ne_self, OfNat.one_ne_ofNat,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_const_zero, add_zero,
    Fin.reduceFinMk, Nat.add_assoc]

private theorem outgoing_row_6 (k : Fin 16 → ℕ) : baseOutgoing .VII k 6=(2-k ⟨4,by decide⟩)+(1-k ⟨5,by decide⟩)+k ⟨13,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=6 then k i else
    if ((baseBundles .VII)[i.1]).1.2=6 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.reduceEqDiff, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Nat.succ_ne_self, OfNat.one_ne_ofNat,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_const_zero, add_zero,
    Fin.reduceFinMk, Nat.add_assoc]

private theorem outgoing_row_7 (k : Fin 16 → ℕ) : baseOutgoing .VII k 7=k ⟨6,by decide⟩+(1-k ⟨10,by decide⟩)+(1-k ⟨12,by decide⟩)+k ⟨14,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=7 then k i else
    if ((baseBundles .VII)[i.1]).1.2=7 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.reduceEqDiff, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, OfNat.one_ne_ofNat, Nat.succ_ne_self,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_const_zero, add_zero,
    Fin.reduceFinMk, Nat.add_assoc]

private theorem outgoing_row_8 (k : Fin 16 → ℕ) : baseOutgoing .VII k 8=(1-k ⟨6,by decide⟩)+(1-k ⟨11,by decide⟩)+(1-k ⟨13,by decide⟩)+k ⟨15,by decide⟩ := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=8 then k i else
    if ((baseBundles .VII)[i.1]).1.2=8 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.reduceEqDiff, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, Nat.succ_ne_self, OfNat.one_ne_ofNat,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_singleton, Fin.reduceFinMk,
    Nat.add_assoc]

private theorem outgoing_row_9 (k : Fin 16 → ℕ) : baseOutgoing .VII k 9=k ⟨7,by decide⟩+(1-k ⟨8,by decide⟩)+(1-k ⟨14,by decide⟩) := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=9 then k i else
    if ((baseBundles .VII)[i.1]).1.2=9 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.reduceEqDiff, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, OfNat.one_ne_ofNat, Nat.succ_ne_self,
    Finset.univ_unique, Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_const_zero, add_zero,
    Fin.reduceFinMk, Nat.add_assoc]

private theorem outgoing_row_10 (k : Fin 16 → ℕ) : baseOutgoing .VII k 10=(2-k ⟨7,by decide⟩)+(1-k ⟨9,by decide⟩)+(1-k ⟨15,by decide⟩) := by
  change (∑ i : Fin 16, if ((baseBundles .VII)[i.1]).1.1=10 then k i else
    if ((baseBundles .VII)[i.1]).1.2=10 then ((baseBundles .VII)[i.1]).2-k i else 0)=_
  simp only [baseBundles, Fin.sum_univ_succ, Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
    List.getElem_cons_zero, OfNat.zero_ne_ofNat, ↓reduceIte, Nat.reduceEqDiff, Fin.val_succ, List.getElem_cons_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc, OfNat.one_ne_ofNat, Finset.univ_unique,
    Fin.default_eq_zero, Fin.val_eq_zero, zero_add, Finset.sum_singleton, Fin.reduceFinMk, Nat.add_assoc]

/-- Every normalized source-balanced orientation has an actual profile index. -/
theorem exists_profile (k : Fin (baseBundles .VII).length → ℕ)
    (hk : ∀ i,k i ≤ ((baseBundles .VII)[i.1]'i.2).2)
    (hb : ∀ v : Fin VineType.VII.template.n,
      baseOutgoing .VII k v.1=if v.1<2 then 1 else 2) :
    ∃ p : Fin (baseProfileCount .VII),baseProfileCounts .VII p=List.ofFn k := by
  change Fin 16 → ℕ at k
  have h0 := hk ⟨0,by decide⟩
  change k ⟨0,by decide⟩ ≤ 1 at h0
  have h1 := hk ⟨1,by decide⟩
  change k ⟨1,by decide⟩ ≤ 1 at h1
  have h2 := hk ⟨2,by decide⟩
  change k ⟨2,by decide⟩ ≤ 2 at h2
  have h3 := hk ⟨3,by decide⟩
  change k ⟨3,by decide⟩ ≤ 2 at h3
  have h4 := hk ⟨4,by decide⟩
  change k ⟨4,by decide⟩ ≤ 2 at h4
  have h5 := hk ⟨5,by decide⟩
  change k ⟨5,by decide⟩ ≤ 1 at h5
  have h6 := hk ⟨6,by decide⟩
  change k ⟨6,by decide⟩ ≤ 1 at h6
  have h7 := hk ⟨7,by decide⟩
  change k ⟨7,by decide⟩ ≤ 2 at h7
  have h8 := hk ⟨8,by decide⟩
  change k ⟨8,by decide⟩ ≤ 1 at h8
  have h9 := hk ⟨9,by decide⟩
  change k ⟨9,by decide⟩ ≤ 1 at h9
  have h10 := hk ⟨10,by decide⟩
  change k ⟨10,by decide⟩ ≤ 1 at h10
  have h11 := hk ⟨11,by decide⟩
  change k ⟨11,by decide⟩ ≤ 1 at h11
  have h12 := hk ⟨12,by decide⟩
  change k ⟨12,by decide⟩ ≤ 1 at h12
  have h13 := hk ⟨13,by decide⟩
  change k ⟨13,by decide⟩ ≤ 1 at h13
  have h14 := hk ⟨14,by decide⟩
  change k ⟨14,by decide⟩ ≤ 1 at h14
  have h15 := hk ⟨15,by decide⟩
  change k ⟨15,by decide⟩ ≤ 1 at h15
  have hbal0 := hb ⟨0,by decide⟩
  change baseOutgoing .VII k 0=1 at hbal0
  rw [outgoing_row_0] at hbal0
  have hbal1 := hb ⟨1,by decide⟩
  change baseOutgoing .VII k 1=1 at hbal1
  rw [outgoing_row_1] at hbal1
  have hbal2 := hb ⟨2,by decide⟩
  change baseOutgoing .VII k 2=2 at hbal2
  rw [outgoing_row_2] at hbal2
  have hbal3 := hb ⟨3,by decide⟩
  change baseOutgoing .VII k 3=2 at hbal3
  rw [outgoing_row_3] at hbal3
  have hbal4 := hb ⟨4,by decide⟩
  change baseOutgoing .VII k 4=2 at hbal4
  rw [outgoing_row_4] at hbal4
  have hbal5 := hb ⟨5,by decide⟩
  change baseOutgoing .VII k 5=2 at hbal5
  rw [outgoing_row_5] at hbal5
  have hbal6 := hb ⟨6,by decide⟩
  change baseOutgoing .VII k 6=2 at hbal6
  rw [outgoing_row_6] at hbal6
  have hbal7 := hb ⟨7,by decide⟩
  change baseOutgoing .VII k 7=2 at hbal7
  rw [outgoing_row_7] at hbal7
  have hbal8 := hb ⟨8,by decide⟩
  change baseOutgoing .VII k 8=2 at hbal8
  rw [outgoing_row_8] at hbal8
  have hbal9 := hb ⟨9,by decide⟩
  change baseOutgoing .VII k 9=2 at hbal9
  rw [outgoing_row_9] at hbal9
  have hbal10 := hb ⟨10,by decide⟩
  change baseOutgoing .VII k 10=2 at hbal10
  rw [outgoing_row_10] at hbal10
  obtain ⟨p,hp⟩ := exhaustive (k ⟨0,by decide⟩) (k ⟨1,by decide⟩) (k ⟨2,by decide⟩) (k ⟨3,by decide⟩) (k ⟨4,by decide⟩) (k ⟨5,by decide⟩) (k ⟨6,by decide⟩) (k ⟨7,by decide⟩) (k ⟨8,by decide⟩) (k ⟨9,by decide⟩) (k ⟨10,by decide⟩) (k ⟨11,by decide⟩) (k ⟨12,by decide⟩) (k ⟨13,by decide⟩) (k ⟨14,by decide⟩) (k ⟨15,by decide⟩) h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 hbal0 hbal1 hbal2 hbal3 hbal4 hbal5 hbal6 hbal7 hbal8 hbal9 hbal10
  refine ⟨p,?_⟩
  change baseProfileCounts .VII p=List.ofFn (fun i : Fin 16 => k i)
  rw [hp]
  apply List.ext_getElem
  · simp only [List.length_cons,List.length_nil,List.length_ofFn]
  · intro i hi _hi2
    have hib : i<16 := by simpa only [List.length_cons,List.length_nil] using hi
    simp only [List.getElem_ofFn]
    interval_cases i <;> rfl

end WaveTurbulence.Vine.Param.Profiles.VII
