/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DecodedPairProperties

/-! # Removing a decoded pair removes exactly its two endpoints -/

public section
namespace WaveTurbulence.Reg
open TTree Finset

/-- Two oriented decoded pairs sharing their first endpoint are the same pair. -/
theorem decodedPair_shared_fst (Q : RegCpl) {p q : (Fin 2 × Path) × (Fin 2 × Path)}
    (hp : p ∈ Q.raw.2) (hq : q ∈ Q.raw.2) (h : p.1 = q.1) : p = q := by
  apply Prod.ext h
  apply decodedPair_functional Q
  · exact (mem_symmPairs_iff _ _).mpr (Or.inl hp)
  · rw [h]
    exact (mem_symmPairs_iff _ _).mpr (Or.inl hq)

/-- The same uniqueness holds for the negative endpoints. -/
theorem decodedPair_shared_snd (Q : RegCpl) {p q : (Fin 2 × Path) × (Fin 2 × Path)}
    (hp : p ∈ Q.raw.2) (hq : q ∈ Q.raw.2) (h : p.2 = q.2) : p = q := by
  have hp' : (p.2,p.1) ∈ symmPairs Q.raw.2 :=
    (mem_symmPairs_iff _ _).mpr (Or.inr (by simpa only [Prod.swap,Prod.eta] using hp))
  have hq' : (p.2,q.1) ∈ symmPairs Q.raw.2 := by
    have hh : (q.2,q.1) ∈ symmPairs Q.raw.2 :=
      (mem_symmPairs_iff _ _).mpr (Or.inr (by simpa only [Prod.swap,Prod.eta] using hq))
    simpa only [← h] using hh
  exact Prod.ext (decodedPair_functional Q hp' hq') h

/-- Positive and negative endpoints cannot coincide. -/
theorem decodedPair_fst_ne_snd (Q : RegCpl) {p q : (Fin 2 × Path) × (Fin 2 × Path)}
    (hp : p ∈ Q.raw.2) (hq : q ∈ Q.raw.2) : p.1 ≠ q.2 := by
  intro he
  have hpos := (decodedCouple_pair_signs Q p hp).1
  have hneg := (decodedCouple_pair_signs Q q hq).2
  rw [he,hneg] at hpos
  exact (by decide : (-1 : ℤˣ) ≠ 1) hpos

/-- Distinct entries have disjoint endpoint sets. -/
theorem decodedPair_disjoint_endpoints (Q : RegCpl) {p q : (Fin 2 × Path) × (Fin 2 × Path)}
    (hp : p ∈ Q.raw.2) (hq : q ∈ Q.raw.2) (hne : p ≠ q) :
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2 :=
  ⟨fun h => hne (decodedPair_shared_fst Q hp hq h), decodedPair_fst_ne_snd Q hp hq,
    (decodedPair_fst_ne_snd Q hq hp).symm, fun h => hne (decodedPair_shared_snd Q hp hq h)⟩

/-- Erasing one actual decoded pair removes precisely its two actual leaves. -/
theorem pairEndpoints_erase (Q : RegCpl) (x y : Fin 2 × Path) (ht : (x,y) ∈ Q.raw.2) :
    pairEndpoints (Q.raw.2.erase (x,y)) = pairEndpoints Q.raw.2 \ {x,y} := by
  ext z
  constructor
  · intro hz
    obtain ⟨p,hp,hz⟩ := (mem_pairEndpoints_iff _ _).mp hz
    obtain ⟨hne,hp⟩ := (decodedPair_nodup Q).mem_erase_iff.mp hp
    have hd := decodedPair_disjoint_endpoints Q hp ht hne
    apply Finset.mem_sdiff.mpr
    refine ⟨(mem_pairEndpoints_iff _ _).mpr ⟨p,hp,hz⟩,?_⟩
    simp only [Finset.mem_insert,Finset.mem_singleton]
    rcases hz with hz | hz
    · exact fun h => h.elim (fun he => hd.1 (hz.symm.trans he))
        (fun he => hd.2.1 (hz.symm.trans he))
    · exact fun h => h.elim (fun he => hd.2.2.1 (hz.symm.trans he))
        (fun he => hd.2.2.2 (hz.symm.trans he))
  · intro hz
    obtain ⟨hz,hne⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨p,hp,hz⟩ := (mem_pairEndpoints_iff _ _).mp hz
    have hpt : p ≠ (x,y) := by
      intro he
      subst p
      apply hne
      simp only [Finset.mem_insert,Finset.mem_singleton]
      exact hz
    exact (mem_pairEndpoints_iff _ _).mpr
      ⟨p,(decodedPair_nodup Q).mem_erase_iff.mpr ⟨hpt,hp⟩,hz⟩

end WaveTurbulence.Reg
