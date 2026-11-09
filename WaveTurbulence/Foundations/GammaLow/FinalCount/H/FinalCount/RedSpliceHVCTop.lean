/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.RedSpliceHVCTop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceHVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.RedSpliceTop
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.RS.Facts
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.RedSpliceHVCTop`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.


# REDSPLICE-DEF (S2a): ingredients of an HVC group and its top ingredient

* `Spine.vine_in_member`: a vine contained in the union of a spine lies in one member.
* `Spine.members_not_nested`: distinct members of a spine are not nested.
* `isIngredient_hvc`: every ingredient (in the sense of `IsIngredient`, for any adjoint bond) of an HVC group is a
  member of its spine, in either orientation.  The adjoint bond is therefore irrelevant.
-/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.RedSplice
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.Mole TTree WaveTurbulence.Stage1

section generic
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- A vine contained in the union of a spine lies in one member. -/
theorem Spine.vine_in_member (hM : M.IsMolecule) {L : List (Finset V × V × V)} {U : Finset V} {a c : V}
    (hs : Spine M L U a c) (hB : M.IsBlock U a c) {A : Finset V} {x y : V}
    (hA : Src.IsSomeVine Src.γL M A x y) (hAU : A ⊆ U) : ∃ T p q, (T, p, q) ∈ L ∧ A ⊆ T := by
  induction hs with
  | @one T a' b hv => exact ⟨T, a', b, by simp, hAU⟩
  | @snoc L' U' T a' b c' hs' hT hi hne ih =>
    have hZ := hT
    have hBU' : M.IsBlock U' a' b := RS.chain_prefix_isBlock M hM hs'.chain hZ hi hB
    rcases RS.vine_in_terminal_split M hM hZ.block hB hs'.ends.2.1 hA hAU with h | h
    · obtain ⟨T', p, q, hm, hsub⟩ := ih hBU' h
      exact ⟨T', p, q, List.mem_append_left _ hm, hsub⟩
    · exact ⟨T, b, c', by simp, h⟩

/-- Distinct members of a spine are not nested. -/
theorem Spine.members_not_nested {L : List (Finset V × V × V)} {U : Finset V} {a c : V}
    (hs : Spine M L U a c) {T1 T2 : Finset V} {p1 q1 p2 q2 : V} (h1 : (T1, p1, q1) ∈ L)
    (h2 : (T2, p2, q2) ∈ L) (hsub : T1 ⊆ T2) : T1 = T2 := by
  induction hs with
  | @one T a' b hv =>
    simp only [List.mem_singleton, Prod.mk.injEq] at h1 h2
    rw [h1.1, h2.1]
  | @snoc L' U' T a' b c' hs' hT hi hne ih =>
    have hends := isSomeVine_ends_RedSpliceSplit hT
    have hne' : ∀ {Z : Finset V} {p q : V}, (Z, p, q) ∈ L' → Src.IsSomeVine Src.γL M Z p q ∧ Z ⊆ U' := fun hm => hs'.mem_vine hm
    -- a member of the prefix cannot lie inside the last vine
    have hnot : ∀ {Z : Finset V} {p q : V}, (Z, p, q) ∈ L' → ¬ Z ⊆ T := by
      intro Z p q hm hZT
      obtain ⟨hZv, hZU⟩ := hs'.mem_vine hm
      have hZe := isSomeVine_ends_RedSpliceSplit hZv
      have hp : p ∈ U' ∩ T := mem_inter.mpr ⟨hZU hZe.1, hZT hZe.1⟩
      have hq : q ∈ U' ∩ T := mem_inter.mpr ⟨hZU hZe.2.1, hZT hZe.2.1⟩
      rw [hi, mem_singleton] at hp hq
      exact hZe.2.2 (hp.trans hq.symm)
    have hnot2 : ∀ {Z : Finset V} {p q : V}, (Z, p, q) ∈ L' → ¬ T ⊆ Z := by
      intro Z p q hm hTZ
      obtain ⟨hZv, hZU⟩ := hs'.mem_vine hm
      have hp : c' ∈ U' ∩ T := mem_inter.mpr ⟨hZU (hTZ hends.2.1), hends.2.1⟩
      rw [hi, mem_singleton] at hp
      exact hends.2.2 hp.symm
    rcases List.mem_append.mp h1 with h1 | h1 <;> rcases List.mem_append.mp h2 with h2 | h2
    · exact ih h1 h2
    · simp only [List.mem_singleton, Prod.mk.injEq] at h2
      exact absurd (h2.1 ▸ hsub) (hnot h1)
    · simp only [List.mem_singleton, Prod.mk.injEq] at h1
      exact absurd (h1.1 ▸ hsub) (hnot2 h2)
    · simp only [List.mem_singleton, Prod.mk.injEq] at h1 h2
      rw [h1.1, h2.1]

end generic

variable {w : ℕ} {G : Garden w}

/-- **Every ingredient of an HVC group is a member of its spine**, whichever adjoint bond is used. -/
theorem isIngredient_hvc (hM : G.molecule.IsMolecule) {S T : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    {e : GardenDart G} (hends : G.molecule.ends e = s(a, b)) (hBe : (eraseBond G.molecule e).IsBlock S a b)
    {L : List (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree)}
    (hs : Spine (eraseBond G.molecule e) L S a b) (hlen : 2 ≤ L.length) (h : IsIngredient G.molecule S T) :
    ∃ p q, (T, p, q) ∈ L ∨ (T, q, p) ∈ L := by
  classical
  have hab : a ≠ b := hBe.2.2.2.1
  have hne : G.molecule.atom e ≠ G.molecule.atom (G.molecule.mate e) := by
    intro h
    unfold Molecule.ends at hends
    rw [h] at hends
    rcases Sym2.eq_iff.mp hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hab (h1.symm.trans h2)
    · exact hab (h2.symm.trans h1)
  have hN := eraseBond_isMolecule G.molecule hM e hne
  rcases h with ⟨a', b', n, x, y, hB', hI⟩ | ⟨a', b', e', n, x, y, hends', hn2, hBe', hI⟩
  · exact (vc_not_hyper hB' ⟨e, hends, hBe⟩).elim
  · have hab' : a' ≠ b' := hBe'.2.2.2.1
    have hne' : G.molecule.atom e' ≠ G.molecule.atom (G.molecule.mate e') := by
      intro h
      unfold Molecule.ends at hends'
      rw [h] at hends'
      rcases Sym2.eq_iff.mp hends' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hab' (h1.symm.trans h2)
      · exact hab' (h2.symm.trans h1)
    have hN' := eraseBond_isMolecule G.molecule hM e' hne'
    -- the joints of the two adjoint decompositions agree
    obtain ⟨da, db, dint⟩ := hyperBlock_degrees G.molecule (⟨e, hends, hBe⟩ : G.molecule.IsHyperBlock S a b)
    obtain ⟨da', db', -⟩ := hyperBlock_degrees G.molecule (⟨e', hends', hBe'⟩ : G.molecule.IsHyperBlock S a' b')
    have ha' : a' = a ∨ a' = b := by
      by_contra hc
      push Not at hc
      have := dint a' hBe'.2.1 hc.1 hc.2
      omega
    have hb' : b' = a ∨ b' = b := by
      by_contra hc
      push Not at hc
      have := dint b' hBe'.2.2.1 hc.1 hc.2
      omega
    -- the spine of the `e'`-chain
    obtain ⟨L', hs', hlen'⟩ := Spine.of_chain_len (chainIngredient_spec hI).1
    have hlen2' : 2 ≤ L'.length := hlen' ▸ hn2
    have hmem' : (T, x, y) ∈ L' := hs'.ingredient_mem hN' hBe' hI
    have hTv' : Src.IsSomeVine Src.γL (eraseBond G.molecule e') T x y := (hs'.mem_vine hmem').1
    have hnb' := hs'.not_both hlen2' hmem'
    -- `T` is a vine of `G.molecule` and of the `e`-adjoint
    have hTM : Src.IsSomeVine Src.γL G.molecule T x y := (vine_transfer G.molecule hends' hnb' x y).mp hTv'
    have hnb : ¬ (a ∈ T ∧ b ∈ T) := by
      rintro ⟨h1, h2⟩
      apply hnb'
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd rfl hab'
      · exact ⟨h1, h2⟩
      · exact ⟨h2, h1⟩
      · exact absurd rfl hab'
    have hTN : Src.IsSomeVine Src.γL (eraseBond G.molecule e) T x y := (vine_transfer G.molecule hends hnb x y).mpr hTM
    have hZ := hTN
    have hTS : T ⊆ S := (hs'.mem_vine hmem').2
    obtain ⟨Ti, p, q, hmi, hTTi⟩ := hs.vine_in_member hN hBe hZ hTS
    -- `Ti` is a vine of `G.molecule`, hence of the `e'`-adjoint
    have hTiN : Src.IsSomeVine Src.γL (eraseBond G.molecule e) Ti p q := (hs.mem_vine hmi).1
    have hnbi := hs.not_both hlen hmi
    have hTiM : Src.IsSomeVine Src.γL G.molecule Ti p q := (vine_transfer G.molecule hends hnbi p q).mp hTiN
    have hnbi' : ¬ (a' ∈ Ti ∧ b' ∈ Ti) := by
      rintro ⟨h1, h2⟩
      apply hnbi
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact absurd rfl hab'
      · exact ⟨h1, h2⟩
      · exact ⟨h2, h1⟩
      · exact absurd rfl hab'
    have hTiN' : Src.IsSomeVine Src.γL (eraseBond G.molecule e') Ti p q := (vine_transfer G.molecule hends' hnbi' p q).mpr hTiM
    have hTiS : Ti ⊆ S := (hs.mem_vine hmi).2
    obtain ⟨Tj, p', q', hmj, hTiTj⟩ := hs'.vine_in_member hN' hBe' hTiN' hTiS
    have hTT := hs'.members_not_nested hmem' hmj (hTTi.trans hTiTj)
    have hTiT : Ti = T := Finset.Subset.antisymm (hTT ▸ hTiTj) hTTi
    exact ⟨p, q, Or.inl (hTiT ▸ hmi)⟩

end WaveTurbulence.GammaLow.FinalCount.H
