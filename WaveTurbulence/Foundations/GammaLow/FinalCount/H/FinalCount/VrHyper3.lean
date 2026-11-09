/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VrHyper3
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3CompRun
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Flat
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3Steps
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.G3TVineRho
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.VrHyper3`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # VINE-RHO (8): the `ρ`-loss of vine chains, hyper objects and DV's (TARGET L2226, Operation 1)

All statements are for the universe's object definitions (`WaveTurbulence.LGSpine.SourceVine`: `Chain`, `IsVC`, `IsHV`,
`IsHVC`, `IsDV`).  A chain of `n` vines costs at most `42 n` (`chain_ladderLoss_le`); an HV costs `42`; an HVC with `n` ingredients
costs `42 n`; a DV costs `84`.  The loss genuinely grows with `n` (see PROGRESS.md: a chain of `n` double bonds).

Low-range change (L6-HG3): the objects are those of the low family (`Src … Src.γL`); the vine bound is
`someVine_ladderLoss_le_of_agree` (`G3TVineRho`: main's bound for (I), (II), L3's N3 Thm 6 (iv) for T-vines), so the
statements take the layer's named input `[Src.G3Inputs V D]` (`H/InputsG3.lean`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountAsm Finset
set_option linter.unusedSectionVars false
universe u1 u2 u3
variable {V : Type u1} [DecidableEq V] {D : Type u2} [Fintype D] [DecidableEq D] {D' : Type u3} [Fintype D'] [DecidableEq D']

theorem chain_ne {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) : a ≠ b := by
  induction h with
  | single hv => have hX := hv; exact hX.block.2.2.2.1
  | append _ _ _ hac _ => exact hac

theorem chain_left_mem {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) : a ∈ S := by
  induction h with
  | single hv => have hX := hv; exact hX.block.2.1
  | append _ _ _ _ ih => exact mem_union_left _ ih

/-- **A chain of `n` vines of `M'` (which agrees with `M` away from `p, q`) costs at most `42 n`.** -/
theorem chain_ladderLoss_le [Src.G3Inputs V D'] (M : Molecule V D) (hM : M.IsMolecule) (M' : Molecule V D')
    (hM' : M'.IsMolecule)
    {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M' S a b n) :
    ∀ {p q : V}, Agree M M' p q → (p ∈ S → p = a ∨ p = b) → (q ∈ S → q = a ∨ q = b) →
      ladderLoss M (M.atoms \ S) ≤ 42 * n := by
  induction h with
  | single hv =>
    intro p q hA hp hq
    have hX := hv
    have := someVine_ladderLoss_le_of_agree M hM M' hM' hA hX hp hq
    omega
  | @append S T a b c n hS hT hST hac ih =>
    intro p q hA hp hq
    have hX := hT
    have hbc : b ≠ c := hX.block.2.2.2.1
    have hcT : c ∈ T := hX.block.2.2.1
    have haS := chain_left_mem hS
    have hab := chain_ne hS
    have hcS : c ∉ S := fun hc => hbc (by
      have : c ∈ S ∩ T := mem_inter.2 ⟨hc, hcT⟩
      rw [hST] at this; exact ((mem_singleton.1 this)).symm)
    have haT : a ∉ T := fun ha => hab (by
      have : a ∈ S ∩ T := mem_inter.2 ⟨haS, ha⟩
      rw [hST] at this; exact mem_singleton.1 this)
    have h1 := ih hA (fun hpS => by
      rcases hp (mem_union_left _ hpS) with h | h
      · exact Or.inl h
      · exact absurd (h ▸ hpS) hcS) (fun hqS => by
      rcases hq (mem_union_left _ hqS) with h | h
      · exact Or.inl h
      · exact absurd (h ▸ hqS) hcS)
    have h2 := someVine_ladderLoss_le_of_agree M hM M' hM' hA hX (fun hpT => by
      rcases hp (mem_union_right _ hpT) with h | h
      · exact absurd (h ▸ hpT) haT
      · exact Or.inr h) (fun hqT => by
      rcases hq (mem_union_right _ hqT) with h | h
      · exact absurd (h ▸ hqT) haT
      · exact Or.inr h)
    have h3 := ladderLoss_union_le M S T
    omega

/-- **VC**: a vine chain with `n` ingredients costs at most `42 n`. -/
theorem vc_ladderLoss_le [Src.G3Inputs V D] (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : Src.IsVC Src.γL M S a b) :
    ∃ n, 1 ≤ n ∧ ladderLoss M (M.atoms \ S) ≤ 42 * n := by
  obtain ⟨_, n, hn⟩ := h
  refine ⟨n, ?_, chain_ladderLoss_le M hM M hM hn (Agree.refl M a b) (fun h => Or.inl rfl) (fun h => Or.inr rfl)⟩
  induction hn with
  | single _ => exact le_rfl
  | append _ _ _ _ _ => omega

/-- **HV**: the adjoint of a single vine costs at most `42`. -/
theorem hv_ladderLoss_le [Src.G3Inputs V D] (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : Src.IsHV Src.γL M S a b) :
    ladderLoss M (M.atoms \ S) ≤ 42 := by
  obtain ⟨e, he, hX⟩ := h
  have hM' := eraseBond_isMolecule_of_ends M hM e hX.block.2.2.2.1 he
  exact someVine_ladderLoss_le_of_agree M hM _ hM' (agree_eraseBond M e he) hX (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)

/-- **HVC**: the adjoint of a chain of `n ≥ 2` vines costs at most `42 n`. -/
theorem hvc_ladderLoss_le [Src.G3Inputs V D] (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : Src.IsHVC Src.γL M S a b) :
    ∃ n, 2 ≤ n ∧ ladderLoss M (M.atoms \ S) ≤ 42 * n := by
  obtain ⟨e, he, _, n, hn2, hn⟩ := h
  have hM' := eraseBond_isMolecule_of_ends M hM e (chain_ne hn) he
  exact ⟨n, hn2, chain_ladderLoss_le M hM _ hM' hn (agree_eraseBond M e he) (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)⟩

/-- **DV**: two type-V vines sharing both joints cost at most `84`. -/
theorem dv_ladderLoss_le [Src.G3Inputs V D] (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : Src.IsDV Src.γL M S a b) :
    ladderLoss M (M.atoms \ S) ≤ 84 := by
  obtain ⟨-, A, B, hA, hB, _, rfl⟩ := h
  have h1 := someVine_ladderLoss_le_of_agree M hM M hM (Agree.refl M a b) hA (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)
  have h2 := someVine_ladderLoss_le_of_agree M hM M hM (Agree.refl M a b) hB (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)
  have := ladderLoss_union_le M A B
  omega

end WaveTurbulence.GammaLow.FinalCount.H
