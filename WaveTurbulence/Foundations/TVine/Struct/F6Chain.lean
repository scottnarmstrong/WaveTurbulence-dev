/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Discharge
public import WaveTurbulence.Foundations.TVine.Struct.RemoveAll
public import WaveTurbulence.Foundations.TVine.Struct.IIData
public import WaveTurbulence.Foundations.TVine.Core.Chain
public import WaveTurbulence.Foundations.TVine.Core.NoCutVertex
import Mathlib.Tactic

/-!
# Chains: reversal and concatenation; concatenated members (packet L3; for N2 Thm 1.15 (F6))

* `isTVineU_swap'`, `isVineKindU_swap`: the kinds are symmetric in the joints (private copy: L1's `IsTVineU.swap` is in
  the unpublished `Core.TCap`);
* `ChainU.concat'`, `ChainU.reverse'`, `IsVineLikeU.swap'`;
* **`concat_allowed`**: two block members `U, W` of a T-vine meeting exactly in the joint `U.k₂ = W.k₁` form a
  vine-like sub-object `U ∪ W` with kinds `ks_U ++ ks_W`; so these kinds are allowed (N2 Thm 1.15 (F3));
* `allowed_append`: then `ks_U = ks_W = [I]`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u

variable {V : Type u} [DecidableEq V]

theorem isClosureU_swap' {G C : UMultigraph V} {j₁ j₂ : V} (h : IsClosureU G j₁ j₂ C) : IsClosureU G j₂ j₁ C := by
  obtain ⟨hσ, hV, hl, added, hdata, hm⟩ := h
  have hs : G.mult s(j₂, j₁) = G.mult s(j₁, j₂) := by rw [Sym2.eq_swap]
  refine ⟨by rw [hs]; exact hσ, by rw [hV]; exact Finset.erase_right_comm, hl, added, ?_, fun e => ?_⟩
  · rcases hdata with ⟨h0, a, b, c, d, h1, h2, rfl⟩ | ⟨h1', x, y, h1, h2, rfl⟩
    · exact Or.inl ⟨by rw [hs]; exact h0, c, d, a, b, h2, h1, Multiset.pair_comm _ _⟩
    · exact Or.inr ⟨by rw [hs]; exact h1', y, x, h2, h1, by rw [Sym2.eq_swap]⟩
  · rw [hm e]; congr 1; exact if_congr or_comm rfl rfl

theorem isTVineU_swap' {G : UMultigraph V} {j₁ j₂ : V} (h : IsTVineU G j₁ j₂) : IsTVineU G j₂ j₁ := by
  obtain ⟨hB, hm, C, hC, hRT⟩ := h
  exact ⟨hB.swap, hm, C, isClosureU_swap' hC, hRT⟩

theorem isVineXU_swap {X : VineType} {G : UMultigraph V} {j₁ j₂ : V} (h : IsVineXU X G j₁ j₂) :
    IsVineXU X G j₂ j₁ := by
  obtain ⟨hB, k, hk, f, hinj, himg, hj, hb⟩ := h
  exact ⟨hB.swap, k, hk, f, hinj, himg, by rw [Finset.pair_comm]; exact hj, hb⟩

theorem isVineKindU_swap {k : EnlKind} {G : UMultigraph V} {a b : V} (h : IsVineKindU k G a b) :
    IsVineKindU k G b a := by
  cases k with
  | I => exact isVineXU_swap h
  | II => exact isVineXU_swap h
  | T => exact isTVineU_swap' h

theorem chain_ne_nil {H : UMultigraph V} {S : Finset V} {a b : V} {ks : List EnlKind} (h : ChainU H S a b ks) :
    ks ≠ [] := by
  cases h with
  | single _ => simp
  | append _ _ _ _ => simp

/-- **Concatenation of chains.** -/
theorem ChainU.concat' {H : UMultigraph V} {S T : Finset V} {a b c : V} {ks₁ ks₂ : List EnlKind}
    (h₁ : ChainU H S a b ks₁) (h₂ : ChainU H T b c ks₂) (hST : S ∩ T = {b}) (hac : a ≠ c) :
    ChainU H (S ∪ T) a c (ks₁ ++ ks₂) := by
  induction h₂ with
  | single hv => exact .append h₁ hv hST hac
  | @append T₁ T₂ b' c' d ks' k hch hv hT₁₂ hbd ih =>
    have hbT₁ := (ChainU.ends_mem hch).1
    have hc'T₁ := (ChainU.ends_mem hch).2
    have hbc' := ChainU.ne hch
    have haS := (ChainU.ends_mem h₁).1
    have hab := ChainU.ne h₁
    have hc'T₂ : c' ∈ T₂ := by
      have : c' ∈ T₁ ∩ T₂ := by rw [hT₁₂]; simp
      exact (Finset.mem_inter.mp this).2
    have hST₁ : S ∩ T₁ = {b'} := by
      apply Finset.Subset.antisymm
      · intro x hx
        rw [← hST]
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1,
          Finset.mem_union_left _ (Finset.mem_inter.mp hx).2⟩
      · intro x hx
        rw [Finset.mem_singleton.mp hx]
        exact Finset.mem_inter.mpr ⟨(ChainU.ends_mem h₁).2, hbT₁⟩
    have hac' : a ≠ c' := by
      intro h
      have : a ∈ S ∩ T₁ := Finset.mem_inter.mpr ⟨haS, h ▸ hc'T₁⟩
      rw [hST₁] at this
      exact hab (Finset.mem_singleton.mp this)
    have h' := ih h₁ hST₁ hac'
    have hST₂ : (S ∪ T₁) ∩ T₂ = {c'} := by
      apply Finset.Subset.antisymm
      · intro x hx
        obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
        rcases Finset.mem_union.mp hx1 with hxS | hxT₁
        · exfalso
          have : x ∈ S ∩ (T₁ ∪ T₂) := Finset.mem_inter.mpr ⟨hxS, Finset.mem_union_right _ hx2⟩
          rw [hST] at this
          have hxb := Finset.mem_singleton.mp this
          subst hxb
          have : x ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨hbT₁, hx2⟩
          rw [hT₁₂] at this
          exact hbc' (Finset.mem_singleton.mp this)
        · have : x ∈ T₁ ∩ T₂ := Finset.mem_inter.mpr ⟨hxT₁, hx2⟩
          rwa [hT₁₂] at this
      · intro x hx
        rw [Finset.mem_singleton.mp hx]
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ hc'T₁, hc'T₂⟩
    have := ChainU.append h' hv hST₂ hac
    rw [Finset.union_assoc, List.append_assoc] at this
    exact this

/-- **Reversal of a chain.** -/
theorem ChainU.reverse' {H : UMultigraph V} {S : Finset V} {a b : V} {ks : List EnlKind}
    (h : ChainU H S a b ks) : ChainU H S b a ks.reverse := by
  induction h with
  | single hv => exact .single (isVineKindU_swap hv)
  | @append S T a b c ks k hch hv hST hac ih =>
    have := ChainU.concat' (ChainU.single (isVineKindU_swap hv)) ih
      (by rw [Finset.inter_comm]; exact hST) (Ne.symm hac)
    rw [Finset.union_comm] at this
    simpa using this

theorem IsVineLikeU.swap' {G : UMultigraph V} {U : SubObj V} {ks : List EnlKind} (h : IsVineLikeU G U ks) :
    IsVineLikeU G U.swap ks.reverse :=
  ⟨h.1.swap, by rw [SubObj.core_swap]; exact ChainU.reverse' h.2⟩

theorem allowed_append {l₁ l₂ : List EnlKind} (h : AllowedKinds (l₁ ++ l₂)) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    l₁ = [.I] ∧ l₂ = [.I] := by
  obtain ⟨x, l₁', rfl⟩ := List.exists_cons_of_ne_nil h₁
  obtain ⟨y, l₂', rfl⟩ := List.exists_cons_of_ne_nil h₂
  rcases h with h | h | h
  · simp at h
  · cases l₁' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, rfl⟩
    | cons z l => simp at h
  · simp at h

/-- The degree of the induced graph, as a sum. -/
theorem deg_induce_eq (G : UMultigraph V) (hl : G.Loopless) {X : Finset V} {v : V} (hv : v ∈ X) :
    deg (induce G X) v = ∑ w ∈ X, G.mult s(v, w) := by
  unfold deg
  rw [show (induce G X).verts = X from rfl, Core.induce_mult_of_mem G hv hv, hl v, add_zero]
  exact Finset.sum_congr rfl fun w hw => Core.induce_mult_of_mem G hv hw

end WaveTurbulence.TVine.Struct
