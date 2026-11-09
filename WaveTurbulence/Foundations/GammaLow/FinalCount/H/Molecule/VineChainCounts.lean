/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineChainCounts`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Ingredient and atom counts of vine chains (TARGET defvine, subsetvc) -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- A chain of n nonempty vine ingredients has at least n+1 atoms. -/
theorem chain_card_ge {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ}
    (h : Src.Chain Src.γL M S a b n) : n+1 ≤ S.card := by
  induction h with
  | single h => have hX := h; exact (Src.IsSomeVine.card_ge_two hX)
  | @append S T a b c n hS hT hi _hne ih =>
    have hX := hT
    have htwo := (Src.IsSomeVine.card_ge_two hX)
    have hc := card_union_add_card_inter S T
    rw [hi,card_singleton] at hc
    omega

omit [Fintype D] [DecidableEq D] in
/-- (Y2) steps only delete vertices. -/
theorem y2_verts_subset {G G' : TVine.UMultigraph V} (hr : Relation.ReflTransGen TVine.Y2Step G G') :
    G'.verts ⊆ G.verts := by
  induction hr with
  | refl => exact le_rfl
  | tail _ hst ih =>
    obtain ⟨x, y, c, e, -, -, -, -, -, -, -, -, -, -, -, hv, -⟩ := hst
    intro z hz
    rw [hv] at hz
    exact ih (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))

/-- A T-vine has at least five atoms: its closure lives on `S ∖ {j₁, j₂}`, and (Y2) steps only delete vertices, so the
closure contains the three vertices of the doubled triangle. -/
theorem isTVine_card_ge_five {M : Molecule V D} {S : Finset V} {a b : V} (h : M.IsTVine S a b) : 5 ≤ S.card := by
  obtain ⟨hB, -, G, G', hC, hr, hT⟩ := h
  have hsub := y2_verts_subset hr
  obtain ⟨p, q, r, hpq, hpr, hqr, hverts, -⟩ := hT
  have h3 : 3 ≤ G.verts.card := by
    have := Finset.card_le_card hsub
    rw [hverts] at this
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]), Finset.card_pair hqr] at this
    exact this
  rw [hC.2.1] at h3
  have hbS : b ∈ S.erase a := Finset.mem_erase.2 ⟨hB.2.2.2.1.symm, hB.2.2.1⟩
  rw [Finset.card_erase_of_mem hbS, Finset.card_erase_of_mem hB.2.1] at h3
  omega

/-- A family member with fewer than four atoms is a vine of type (I) (main's `isVine_typeI_of_card_lt_four` for
(I), (II); a T-vine has at least five atoms). -/
theorem isSomeVine_typeI_of_card_lt_four {M : Molecule V D} {S : Finset V} {a b : V}
    (h : Src.IsSomeVine Src.γL M S a b) (hc : S.card < 4) : M.IsVine .I S a b := by
  rcases h.cases with h | h | h
  · exact h
  · exact absurd (isVine_typeI_of_card_lt_four h hc) (by decide)
  · exact absurd (isTVine_card_ge_five h) (by omega)

/-- Every small chain consists only of double-bond ingredients. -/
theorem chain_doubleChain_of_card_lt_four {M : Molecule V D} {S : Finset V}
    {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) (hc : S.card<4) : DoubleChain M S a b n := by
  induction h with
  | single h => exact DoubleChain.single (isSomeVine_typeI_of_card_lt_four h hc)
  | @append S T a b c n hS hT hi hne ih =>
    have hcS : S.card<4 := (card_le_card (subset_union_left : S ⊆ S ∪ T)).trans_lt hc
    have hcT : T.card<4 := (card_le_card (subset_union_right : T ⊆ S ∪ T)).trans_lt hc
    exact DoubleChain.append (ih hcS) (isSomeVine_typeI_of_card_lt_four hT hcT) hi hne

end WaveTurbulence.GammaLow.FinalCount.H
