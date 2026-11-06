/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamCurrentBlocks

public import WaveTurbulenceVineParam.VineParamSlotCapSupport
public import WaveTurbulence.Foundations.Molecule.VineRailReversal
import Mathlib.Tactic

/-! # Insertions in other slots create no new crossings of a fixed cap -/

public section
namespace WaveTurbulence.Vine.Param

/-- A rail outside a cap has both endpoints of every bond outside it. -/
theorem railBonds_outside_cap (C : Finset ℕ) (a b : ℕ) (ws : List ℕ)
    (ha : a ∉ C) (hb : b ∉ C) (hws : ∀ v ∈ ws,v ∉ C) :
    ∀ e ∈ railBonds a ws b,e.1 ∉ C ∧ e.2 ∉ C := by
  intro e he
  have hh := List.of_mem_zip he
  constructor
  · rcases List.mem_cons.mp hh.1 with h | h
    · exact h ▸ ha
    · exact hws _ h
  · rcases List.mem_append.mp hh.2 with h | h
    · exact hws _ h
    · exact List.mem_singleton.mp h ▸ hb

/-- If a slot and every fresh name are outside a fixed old cap, insertion
adds only outside bonds. Any cap-crossing occurrence is an old bond. -/
theorem insertRungs_old_or_outside_cap (T : VineTemplate)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (C : Finset ℕ)
    (hC : ∀ v ∈ C,v<T.n)
    (hs : s.1.1 ∉ C ∧ s.1.2 ∉ C ∧ s.2.1 ∉ C ∧ s.2.2 ∉ C) :
    ∀ e ∈ (insertRungs T s k).bonds,e ∈ T.bonds ∨ (e.1 ∉ C ∧ e.2 ∉ C) := by
  by_cases hk : k=0
  · subst k
    intro e he
    exact Or.inl he
  · have hu : ∀ v ∈ (List.range k).map (T.n+·),v ∉ C := by
      intro v hv hmem
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hv
      have := hC _ hmem
      omega
    have hv : ∀ v ∈ (List.range k).map (T.n+k+·),v ∉ C := by
      intro v hv hmem
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hv
      have := hC _ hmem
      omega
    intro e he
    simp only [insertRungs,hk,ite_false,List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · exact Or.inl (List.mem_of_mem_erase (List.mem_of_mem_erase he))
    · exact Or.inr (railBonds_outside_cap C _ _ _ hs.1 hs.2.1 hu e he)
    · exact Or.inr (railBonds_outside_cap C _ _ _ hs.2.2.1 hs.2.2.2 hv e he)
    · obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp he
      have hep : e=p := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_self] using he
      subst e
      have hm := List.of_mem_zip hp
      exact Or.inr ⟨hu _ hm.1,hv _ hm.2⟩

/-- No new crossing of an old cap is introduced by an outside insertion. -/
theorem insertRungs_cap_crossing_old (T : VineTemplate)
    (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ) (C : Finset ℕ)
    (hC : ∀ v ∈ C,v<T.n)
    (hs : s.1.1 ∉ C ∧ s.1.2 ∉ C ∧ s.2.1 ∉ C ∧ s.2.2 ∉ C)
    {e : ℕ×ℕ} (he : e ∈ (insertRungs T s k).bonds)
    (hc : ¬(e.1 ∈ C ↔ e.2 ∈ C)) : e ∈ T.bonds := by
  rcases insertRungs_old_or_outside_cap T s k C hC hs e he with h | h
  · exact h
  · exact False.elim (hc (iff_of_false h.1 h.2))

end WaveTurbulence.Vine.Param
