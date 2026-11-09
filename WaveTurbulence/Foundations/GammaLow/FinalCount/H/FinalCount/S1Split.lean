/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.S1Split
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.S1Erase
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainInteriorConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.RS.Facts
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.S1Split`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# Stage 1 combinatorics: cutting a vine chain at an interior atom

Vines have no cut vertex, so a cut atom of a vine chain is a joint between two ingredients.  If a
chain `S` from `a` to `b` is the union of two sets `L ∋ a` and `R ∋ b` meeting only in `p`, with no
bond leaving `L \ {p}` inside `S`, then `L` is a chain from `a` to `p` and `R` a chain from `p` to
`b`.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Stage1
open Finset WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem chain_split_S1Split {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) :
    ∀ {L R : Finset V} {p : V}, S = L ∪ R → L ∩ R = {p} → a ∈ L → b ∈ R → a ≠ p → b ≠ p →
    (∀ x : D, M.atom x ∈ L → M.atom x ≠ p → M.InGroup S x → M.InGroup L x) →
    ∃ n0 n1, Src.Chain Src.γL M L a p n0 ∧ Src.Chain Src.γL M R p b n1 := by
  induction h with
  | @single T a b hv =>
    intro L R p hS hI haL hbR hap hbp HL
    have hX := hv
    have hpT : p ∈ T := by
      rw [hS]; exact mem_union_left _ (by
        have : p ∈ L ∩ R := by rw [hI]; exact mem_singleton_self _
        exact (mem_inter.mp this).1)
    have hbL : b ∉ L := by
      intro hb
      have : b ∈ L ∩ R := mem_inter.mpr ⟨hb, hbR⟩
      rw [hI] at this
      exact hbp (mem_singleton.mp this)
    have hcon := RS.isSomeVine_erase_connected hX p
    have haT : a ∈ T.erase p := mem_erase.mpr ⟨hap, hX.block.2.1⟩
    have hbT : b ∈ T.erase p := mem_erase.mpr ⟨hbp, hX.block.2.2.1⟩
    have := side_iff (S := T) (L := L) (X := T.erase p) (erase_subset _ _) (by simp) HL
      (hcon a haT b hbT)
    exact absurd (this.mp haL) hbL
  | @append S' T a q b n hS hT hi hne ih =>
    intro L R p hSLR hI haL hbR hap hbp HL
    have hX := hT
    have hS'S : S' ⊆ S' ∪ T := subset_union_left
    have hTS : T ⊆ S' ∪ T := subset_union_right
    have hq : q ∈ T := hX.block.2.1
    have hbT : b ∈ T := hX.block.2.2.1
    have hqb : q ≠ b := hX.block.2.2.2.1
    have haS' : a ∈ S' := (chain_ends hS).1
    have hqS' : q ∈ S' := (chain_ends hS).2.1
    have hbL : b ∉ L := by
      intro hb
      have : b ∈ L ∩ R := mem_inter.mpr ⟨hb, hbR⟩
      rw [hI] at this
      exact hbp (mem_singleton.mp this)
    have hpLR : p ∈ L ∧ p ∈ R := by
      have : p ∈ L ∩ R := by rw [hI]; exact mem_singleton_self _
      exact mem_inter.mp this
    have hpS : p ∈ S' ∪ T := by rw [hSLR]; exact mem_union_left _ hpLR.1
    have hconS' : ∀ u ∈ S', ∀ v ∈ S', (Mole.induced M S').SameComponent u v :=
      chain_connected hS.toVine
    by_cases hpT : p ∈ T
    · by_cases hpq : p = q
      · -- the cut atom is the joint between the last ingredient and the prefix
        subst hpq
        have hc1 : ∀ u ∈ S'.erase p, ∀ v ∈ S'.erase p,
            (Mole.induced M (S'.erase p)).SameComponent u v := by
          have := chain_erase_first_connected (chain_swap hS).toVine
          exact this
        have hc2 := RS.isSomeVine_erase_connected hX p
        have haE : a ∈ S'.erase p := mem_erase.mpr ⟨hap, haS'⟩
        have hbE : b ∈ T.erase p := mem_erase.mpr ⟨hbp, hbT⟩
        have hS'L : ∀ u ∈ S'.erase p, u ∈ L := fun u hu =>
          (side_iff (S := S' ∪ T) (L := L) (X := S'.erase p) ((erase_subset _ _).trans hS'S)
            (by simp) HL (hc1 a haE u hu)).mp haL
        have hTnL : ∀ u ∈ T.erase p, u ∉ L := fun u hu hL =>
          hbL ((side_iff (S := S' ∪ T) (L := L) (X := T.erase p)
            ((erase_subset _ _).trans hTS) (by simp) HL (hc2 u hu b hbE)).mp hL)
        have hLeq : L = S' := by
          ext x
          constructor
          · intro hx
            have hxS : x ∈ S' ∪ T := by rw [hSLR]; exact mem_union_left _ hx
            rcases mem_union.mp hxS with h1 | h1
            · exact h1
            · by_cases hxp : x = p
              · exact hxp ▸ hqS'
              · exact absurd hx (hTnL x (mem_erase.mpr ⟨hxp, h1⟩))
          · intro hx
            by_cases hxp : x = p
            · exact hxp ▸ hpLR.1
            · exact hS'L x (mem_erase.mpr ⟨hxp, hx⟩)
        have hReq : R = T := by
          ext x
          constructor
          · intro hx
            have hxS : x ∈ S' ∪ T := by rw [hSLR]; exact mem_union_right _ hx
            rcases mem_union.mp hxS with h1 | h1
            · by_cases hxp : x = p
              · exact hxp ▸ hpT
              · have hxL := hS'L x (mem_erase.mpr ⟨hxp, h1⟩)
                have : x ∈ L ∩ R := mem_inter.mpr ⟨hxL, hx⟩
                rw [hI] at this
                exact absurd (mem_singleton.mp this) hxp
            · exact h1
          · intro hx
            by_cases hxp : x = p
            · exact hxp ▸ hpLR.2
            · have hxS : x ∈ S' ∪ T := hTS hx
              rw [hSLR] at hxS
              rcases mem_union.mp hxS with h1 | h1
              · exact absurd h1 (hTnL x (mem_erase.mpr ⟨hxp, hx⟩))
              · exact h1
        subst hLeq
        subst hReq
        exact ⟨n, 1, hS, Src.Chain.single hX⟩
      · -- the cut atom is interior to the last vine: impossible
        have hpS' : p ∉ S' := by
          intro hp'
          have : p ∈ S' ∩ T := mem_inter.mpr ⟨hp', hpT⟩
          rw [hi] at this
          exact hpq (mem_singleton.mp this)
        have hqL : q ∈ L := (side_iff (S := S' ∪ T) (L := L) (X := S') hS'S hpS' HL
          (hconS' a haS' q hqS')).mp haL
        have hc2 := RS.isSomeVine_erase_connected hX p
        have hqE : q ∈ T.erase p := mem_erase.mpr ⟨Ne.symm hpq, hq⟩
        have hbE : b ∈ T.erase p := mem_erase.mpr ⟨hbp, hbT⟩
        exact absurd ((side_iff (S := S' ∪ T) (L := L) (X := T.erase p)
          ((erase_subset _ _).trans hTS) (by simp) HL (hc2 q hqE b hbE)).mp hqL) hbL
    · -- the cut atom lies in the prefix
      have hpS' : p ∈ S' := by
        rcases mem_union.mp hpS with h | h
        · exact h
        · exact absurd h hpT
      have hpq : p ≠ q := fun h => hpT (h ▸ hq)
      have hconT := Src.IsSomeVine.vconnected hX
      have hTnL : ∀ u ∈ T, u ∉ L := fun u hu hL =>
        hbL ((side_iff (S := S' ∪ T) (L := L) (X := T) hTS hpT HL (hconT u hu b hbT)).mp hL)
      have hqR : q ∈ R := by
        have hqS : q ∈ S' ∪ T := hTS hq
        rw [hSLR] at hqS
        rcases mem_union.mp hqS with h1 | h1
        · exact absurd h1 (hTnL q hq)
        · exact h1
      have hS'eq : S' = (L ∩ S') ∪ (R ∩ S') := by
        ext x
        constructor
        · intro hx
          have hxS : x ∈ L ∪ R := by rw [← hSLR]; exact hS'S hx
          rcases mem_union.mp hxS with h1 | h1
          · exact mem_union_left _ (mem_inter.mpr ⟨h1, hx⟩)
          · exact mem_union_right _ (mem_inter.mpr ⟨h1, hx⟩)
        · intro hx
          rcases mem_union.mp hx with h1 | h1
          · exact (mem_inter.mp h1).2
          · exact (mem_inter.mp h1).2
      have hI' : (L ∩ S') ∩ (R ∩ S') = {p} := by
        ext x
        constructor
        · intro hx
          have : x ∈ L ∩ R := mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hx).1).1,
            (mem_inter.mp (mem_inter.mp hx).2).1⟩
          rw [hI] at this
          exact this
        · intro hx
          have hxp := mem_singleton.mp hx
          subst hxp
          exact mem_inter.mpr ⟨mem_inter.mpr ⟨hpLR.1, hpS'⟩, mem_inter.mpr ⟨hpLR.2, hpS'⟩⟩
      have HL' : ∀ x : D, M.atom x ∈ L ∩ S' → M.atom x ≠ p → M.InGroup S' x →
          M.InGroup (L ∩ S') x := by
        intro x hx hxp hg
        have h1 := HL x (mem_inter.mp hx).1 hxp (inGroup_of_subset hS'S hg)
        exact ⟨mem_inter.mpr ⟨h1.1, hg.1⟩, mem_inter.mpr ⟨h1.2, hg.2⟩⟩
      obtain ⟨n0, n1, hL', hR'⟩ := ih hS'eq hI' (mem_inter.mpr ⟨haL, haS'⟩)
        (mem_inter.mpr ⟨hqR, hqS'⟩) hap (Ne.symm hpq) HL'
      have hLeq : L ∩ S' = L := by
        ext x
        constructor
        · exact fun hx => (mem_inter.mp hx).1
        · intro hx
          refine mem_inter.mpr ⟨hx, ?_⟩
          have hxS : x ∈ S' ∪ T := by rw [hSLR]; exact mem_union_left _ hx
          rcases mem_union.mp hxS with h1 | h1
          · exact h1
          · exact absurd hx (hTnL x h1)
      have hReq : (R ∩ S') ∪ T = R := by
        ext x
        constructor
        · intro hx
          rcases mem_union.mp hx with h1 | h1
          · exact (mem_inter.mp h1).1
          · have hxS : x ∈ S' ∪ T := hTS h1
            rw [hSLR] at hxS
            rcases mem_union.mp hxS with h2 | h2
            · exact absurd h2 (hTnL x h1)
            · exact h2
        · intro hx
          have hxS : x ∈ S' ∪ T := by rw [hSLR]; exact mem_union_right _ hx
          rcases mem_union.mp hxS with h1 | h1
          · exact mem_union_left _ (mem_inter.mpr ⟨hx, h1⟩)
          · exact mem_union_right _ h1
      rw [hLeq] at hL'
      have hRT : (R ∩ S') ∩ T = {q} := by
        ext x
        constructor
        · intro hx
          have : x ∈ S' ∩ T := mem_inter.mpr ⟨(mem_inter.mp (mem_inter.mp hx).1).2, (mem_inter.mp hx).2⟩
          rw [hi] at this
          exact this
        · intro hx
          have hxq := mem_singleton.mp hx
          subst hxq
          exact mem_inter.mpr ⟨mem_inter.mpr ⟨hqR, hqS'⟩, hq⟩
      have hfin := Src.Chain.append hR' hX hRT (fun h => hbp h.symm)
      rw [hReq] at hfin
      exact ⟨n0, n1 + 1, hL', hfin⟩

end WaveTurbulence.GammaLow.FinalCount.H
