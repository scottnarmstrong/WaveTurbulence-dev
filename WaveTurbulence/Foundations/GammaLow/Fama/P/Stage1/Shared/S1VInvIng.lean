/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
-- L5a port of main `WaveTurbulence.Foundations.Stage1.Shared.S1VInvIng` (sha256 in COPIED-SHA256SUMS) over L6's 𝒱_γ carrier `Src`.
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.IsoStmt
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Stage1.Shared.S1VInvChain
public import WaveTurbulence.Foundations.FinalCount.S1Erase
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
import Mathlib.Tactic
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIng
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Basic
public import WaveTurbulence.Foundations.GammaLow.Fama.Coll.Collection
public import WaveTurbulence.Foundations.GammaLow.Fama.Inputs
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Chain
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainEraseEndpoints
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Facts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Fama.P.Spine.VineDelObjects


/-!
# Ingredients of a maximal group: separation, for both the VC and the HVC alternatives

`ing_pair`: two distinct ingredients (`IsIngredientG γ`) of the same group meet in at most one atom, and
the common atom has internal degree `2` in both.  The two certificates may use different deleted
bonds; the entries of an HVC chain never contain both joints, so they are vines of `M` itself.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.Stage1 WaveTurbulence.GammaLow.FinalCount
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {γ : ℝ} [Fact TVineF1Input] [Fact VinechainlemPrimeInput] [Fact (γ ≤ 1 / 2)] [Fact TVineIsoInvariant]

namespace ChainL
variable {N : Molecule V D} {U : Finset V} {a b : V} {L : List (Finset V × V × V)}

theorem joints (h : ChainL γ N U a b L) : a ≠ b ∧ a ∈ U ∧ b ∈ U := by
  induction h with
  | single hv => have hX := hv; exact ⟨(Src.isBlock_of_isSomeVine hX).2.2.2.1, (Src.isBlock_of_isSomeVine hX).2.1, (Src.isBlock_of_isSomeVine hX).2.2.1⟩
  | append _ hT _ hne ih =>
    have hX := hT
    exact ⟨hne, mem_union_left _ ih.2.1, mem_union_right _ (Src.isBlock_of_isSomeVine hX).2.2.1⟩

/-- In a chain with at least two ingredients no ingredient contains both end joints. -/
theorem entry_not_both (h : ChainL γ N U a b L) (hl : 2 ≤ L.length) :
    ∀ t ∈ L, ¬ (a ∈ t.1 ∧ b ∈ t.1) := by
  induction h with
  | single _ => simp at hl
  | @append S T a b c L hL hT hi hne _ =>
    have hX := hT
    intro t ht ⟨ha, hc⟩
    rcases List.mem_append.mp ht with ht | ht
    · have hcS : c ∈ S := hL.entry_subset t ht hc
      have : c ∈ S ∩ T := mem_inter.mpr ⟨hcS, (Src.isBlock_of_isSomeVine hX).2.2.1⟩
      rw [hi] at this
      have hcb : c = b := by simpa using this
      exact (Src.isBlock_of_isSomeVine hX).2.2.2.1 hcb.symm
    · simp only [List.mem_singleton] at ht
      subst ht
      have hat : a ∈ S ∩ T := mem_inter.mpr ⟨hL.joints.2.1, ha⟩
      rw [hi] at hat
      have hab : a = b := by simpa using hat
      exact hL.joints.1 hab

/-- Transport of a decomposition to another molecule in which every entry is still a vine. -/
theorem map {D' : Type} [Fintype D'] [DecidableEq D'] {N' : Molecule V D'} (h : ChainL γ N U a b L)
    (hv : ∀ t ∈ L, Src.IsSomeVine γ N t.1 t.2.1 t.2.2 → Src.IsSomeVine γ N' t.1 t.2.1 t.2.2) :
    ChainL γ N' U a b L := by
  induction h with
  | single h0 => exact ChainL.single (hv (_, _, _) (by simp) h0)
  | append hL hT hi hne ih =>
    refine ChainL.append (ih fun t ht => hv t (List.mem_append_left _ ht)) ?_ hi hne
    exact hv (_, _, _) (by simp) hT

end ChainL

section Erase
variable {M : Molecule V D}




end Erase



/-- The data extracted from an HVC-type ingredient certificate. -/
theorem hvc_data {M : Molecule V D} {S T : Finset V} {a b : V} {e : D} {n : ℕ} {x y : V}
    (he : M.ends e = s(a, b)) (hn : 2 ≤ n) (_hB : (Molecule.eraseBond M e).IsBlock S a b)
    (hc : ChainIngredientG γ (Molecule.eraseBond M e) S a b n T x y) :
    ∃ L, ChainL γ (Molecule.eraseBond M e) S a b L ∧ (T, x, y) ∈ L ∧
      (∀ t ∈ L, ¬ M.InGroup t.1 e) := by
  obtain ⟨L, hL, hm, hl⟩ := exists_chainL_of_ingredient hc
  refine ⟨L, hL, hm, fun t ht hg => ?_⟩
  obtain ⟨h1, h2⟩ := (inGroup_iff_ends he t.1).mp hg
  exact hL.entry_not_both (by omega) t ht ⟨h1, h2⟩

/-- Two distinct ingredients of one group meet in at most one atom, which has internal degree `2` in
both (both certificates may be of VC type or of HVC type, with possibly different deleted bonds). -/
theorem ing_pair {M : Molecule V D} (hM : M.IsMolecule) {S T T' : Finset V}
    (h : IsIngredientG γ M S T) (h' : IsIngredientG γ M S T') (hne : T ≠ T') :
    (∀ z ∈ T ∩ T', ∀ z' ∈ T ∩ T', z = z') ∧
      (∀ z ∈ T ∩ T', M.degIn T z = 2 ∧ M.degIn T' z = 2) := by
  rcases h with ⟨a1, b1, n1, x1, y1, hB1, hc1⟩ | ⟨a1, b1, e1, n1, x1, y1, he1, hn1, hB1, hc1⟩ <;>
  rcases h' with ⟨a2, b2, n2, x2, y2, hB2, hc2⟩ | ⟨a2, b2, e2, n2, x2, y2, he2, hn2, hB2, hc2⟩
  · exact ingredientIn_sep hM ⟨a1, b1, n1, x1, y1, hB1, hc1⟩ ⟨a2, b2, n2, x2, y2, hB2, hc2⟩ hne
  · exact (not_block_and_hyper hB1 he2 hB2).elim
  · exact (not_block_and_hyper hB2 he1 hB1).elim
  · -- both HVC
    obtain ⟨L1, hL1, hm1, hf1⟩ := hvc_data he1 hn1 hB1 hc1
    obtain ⟨L2, hL2, hm2, hf2⟩ := hvc_data he2 hn2 hB2 hc2
    have hd1 := Mole.hyperBlock_degrees M (j1 := a1) (j2 := b1) ⟨e1, he1, hB1⟩
    have hd2 := Mole.hyperBlock_degrees M (j1 := a2) (j2 := b2) ⟨e2, he2, hB2⟩
    have ha2 : a2 = a1 ∨ a2 = b1 := by
      by_contra hc
      have := hd1.2.2 a2 (hB2.2.1) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      omega
    have hb2 : b2 = a1 ∨ b2 = b1 := by
      by_contra hc
      have := hd1.2.2 b2 (hB2.2.2.1) (fun h => hc (Or.inl h)) (fun h => hc (Or.inr h))
      omega
    have hab2 := hB2.2.2.2.1
    -- the joints of the two certificates coincide as ordered or swapped pairs
    have hends : M.ends e2 = s(a1, b1) := by
      rw [he2]
      rcases ha2 with rfl | rfl <;> rcases hb2 with rfl | rfl
      · exact absurd rfl hab2
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hab2
    have hB2' : (Molecule.eraseBond M e2).IsBlock S a1 b1 := by
      rcases ha2 with rfl | rfl <;> rcases hb2 with rfl | rfl
      · exact absurd rfl hab2
      · exact hB2
      · exact isBlock_symm hB2
      · exact absurd rfl hab2
    have hmol1 : Molecule.eraseBond M e1 |>.IsMolecule := by
      have : M.atom e1 ≠ M.atom (M.mate e1) := by
        have hend := Sym2.eq_iff.mp he1
        change (M.atom e1 = a1 ∧ M.atom (M.mate e1) = b1) ∨ (M.atom e1 = b1 ∧ M.atom (M.mate e1) = a1) at hend
        rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> [exact hB1.2.2.2.1; exact hB1.2.2.2.1.symm]
      exact Vine.eraseBond_isMolecule M hM e1 this
    -- lift the first decomposition to the second erased molecule
    have hL1' : ChainL γ (Molecule.eraseBond M e2) S a1 b1 L1 := by
      refine hL1.map fun t ht hv => ?_
      have hX := hv
      have hfree1 := hf1 t ht
      have hfree2 : ¬ M.InGroup t.1 e2 := by
        rw [inGroup_iff_ends hends]
        rw [inGroup_iff_ends he1] at hfree1
        exact hfree1
      exact isSomeVine_eraseBond e2 (isSomeVine_of_eraseBond e1 hX hfree1) hfree2
    have hmol2 : (Molecule.eraseBond M e2).IsMolecule := by
      have : M.atom e2 ≠ M.atom (M.mate e2) := by
        have hend := Sym2.eq_iff.mp hends
        change (M.atom e2 = a1 ∧ M.atom (M.mate e2) = b1) ∨ (M.atom e2 = b1 ∧ M.atom (M.mate e2) = a1) at hend
        rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact hB2'.2.2.2.1
        · exact hB2'.2.2.2.1.symm
      exact Vine.eraseBond_isMolecule M hM e2 this
    have hBS : (Molecule.eraseBond M e2).IsBlock S a1 b1 := hB2'
    obtain ⟨hs1, hs2⟩ := chainL_sep hmol2 hL1' hBS hL2 hB2 hm1 hm2 hne
    have hfT : ¬ M.InGroup T e2 := by
      rw [inGroup_iff_ends hends]
      have := hf1 _ hm1
      rw [inGroup_iff_ends he1] at this
      exact this
    have hfT' : ¬ M.InGroup T' e2 := hf2 _ hm2
    refine ⟨hs1, fun z hz => ?_⟩
    have := hs2 z hz
    rw [degIn_eraseBond_of_not_inGroup e2 hfT, degIn_eraseBond_of_not_inGroup e2 hfT'] at this
    exact this
  
end WaveTurbulence.GammaLow.Fama
