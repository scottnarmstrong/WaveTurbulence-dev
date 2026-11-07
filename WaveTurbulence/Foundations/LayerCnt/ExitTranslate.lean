/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.ChainLower
import Mathlib.Tactic

/-! # Dart-level uniqueness of single bonds of a vine (TARGET layervine, L1531)

If the template bond class `s(f u, f v)` occurs at most once among the bonds of the expanded template, then at most
one dart of the molecule leads from `u` to `v`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence WaveTurbulence.Vine Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
  {S : Finset V} {a b : V}

/-- The template bond class `e` occurs at most once among the bonds of `T`. -/
@[expose] def SymSingle (T : VineTemplate) (e : ℕ × ℕ) : Prop :=
  (T.bonds.map (fun p => s(p.1, p.2))).count s(e.1, e.2) ≤ 1

theorem mem_groupBonds_iff_out (S : Finset V) (β : Sym2 V) :
    β ∈ M.groupBonds S ↔ ∃ o : D, M.out o = true ∧ M.InGroup S o ∧ M.ends o = β := by
  unfold Molecule.groupBonds
  rw [Multiset.mem_map]
  constructor
  · rintro ⟨o, ho, rfl⟩
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at ho
    exact ⟨o, ho.1, ho.2, rfl⟩
  · rintro ⟨o, h1, h2, rfl⟩
    exact ⟨o, by simp [h1, h2], rfl⟩

/-- At most one dart leads from `u` to `v` when the template class is single. -/
theorem dart_unique (R : VineRealization M X S a b) {u v : V} (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (hc : SymSingle (X.expand R.k) (R.f u, R.f v)) {d d' : D}
    (hd1 : M.atom d = u) (hd2 : M.atom (M.mate d) = v)
    (hd1' : M.atom d' = u) (hd2' : M.atom (M.mate d') = v) : d = d' := by
  by_contra hne
  -- the out-darts of the two bonds
  have hin : ∀ e : D, M.atom e = u → M.atom (M.mate e) = v → M.InGroup S e := fun e h1 h2 => by
    unfold Molecule.InGroup; rw [h1, h2]; exact ⟨hu, hv⟩
  have hout : ∀ e : D, M.atom e = u → M.atom (M.mate e) = v →
      ∃ o, M.out o = true ∧ M.InGroup S o ∧ M.ends o = s(u, v) ∧ (o = e ∨ o = M.mate e) := by
    intro e h1 h2
    by_cases ho : M.out e = true
    · exact ⟨e, ho, hin e h1 h2, by unfold Molecule.ends; rw [h1, h2], Or.inl rfl⟩
    · have ho' : M.out (M.mate e) = true := by rw [M.out_mate]; simpa using ho
      refine ⟨M.mate e, ho', ?_, ?_, Or.inr rfl⟩
      · unfold Molecule.InGroup; rw [M.mate_mate, h1, h2]; exact ⟨hv, hu⟩
      · unfold Molecule.ends; rw [M.mate_mate, h1, h2, Sym2.eq_swap]
  obtain ⟨o, ho1, ho2, ho3, ho4⟩ := hout d hd1 hd2
  obtain ⟨o', ho1', ho2', ho3', ho4'⟩ := hout d' hd1' hd2'
  have hoo : o ≠ o' := by
    intro h
    rcases ho4 with h1 | h1 <;> rcases ho4' with h2 | h2
    · exact hne (h1.symm.trans (h.trans h2))
    · apply huv
      calc u = M.atom d := hd1.symm
        _ = M.atom o := by rw [h1]
        _ = M.atom o' := by rw [h]
        _ = M.atom (M.mate d') := by rw [h2]
        _ = v := hd2'
    · apply huv
      calc u = M.atom d' := hd1'.symm
        _ = M.atom o' := by rw [h2]
        _ = M.atom o := by rw [h]
        _ = M.atom (M.mate d) := by rw [h1]
        _ = v := hd2
    · exact hne (by
        have := congrArg M.mate (h1.symm.trans (h.trans h2))
        simpa [M.mate_mate] using this)
  -- two distinct bonds of the group with the same ends
  set F := (Finset.univ.filter fun x : D => M.out x = true ∧ M.InGroup S x) with hF
  have hmo : o ∈ F := by simp [hF, ho1, ho2]
  have hmo' : o' ∈ F := by simp [hF, ho1', ho2']
  have hcount : 2 ≤ (Multiset.filter (fun β => s(u, v) = β) (M.groupBonds S)).card := by
    unfold Molecule.groupBonds
    rw [Multiset.filter_map, Multiset.card_map]
    have : ({o, o'} : Finset D) ⊆ (Multiset.filter ((fun β => s(u, v) = β) ∘ M.ends) F.val).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Multiset.mem_toFinset, Multiset.mem_filter]
      rcases hx with rfl | rfl
      · exact ⟨hmo, ho3.symm⟩
      · exact ⟨hmo', ho3'.symm⟩
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hoo] at h2
    exact h2.trans (Multiset.toFinset_card_le _)
  -- map to the template
  have hmap : (Multiset.filter (fun β => s(u, v) = β) (M.groupBonds S)).card ≤
      ((M.groupBonds S).map (Sym2.map R.f)).count s(R.f u, R.f v) := by
    rw [Multiset.count_map]
    apply Multiset.card_le_card
    apply Multiset.monotone_filter_right
    intro β hβ
    rw [← hβ]; rfl
  rw [R.bonds_eq] at hmap
  have := hc
  unfold SymSingle at this
  have h2 : (((X.expand R.k).bonds.map fun p => s(p.1, p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)).count
      s(R.f u, R.f v) ≤ 1 := by rw [Multiset.coe_count]; exact this
  omega

end WaveTurbulence.LayerCnt
