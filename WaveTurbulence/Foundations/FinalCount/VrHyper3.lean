/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.VrHyper2
public import WaveTurbulence.Foundations.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.Molecule.VineEraseBondMolecule
import Mathlib.Tactic

/-! # VINE-RHO (8): the `ρ`-loss of vine chains, hyper objects and DV's (TARGET L2226, Operation 1)

All statements are for the universe's object definitions (`WaveTurbulence.LGSpine.SourceVine`: `Chain`, `IsVC`, `IsHV`,
`IsHVC`, `IsDV`).  A chain of `n` vines costs at most `42 n` (`chain_ladderLoss_le`); an HV costs `42`; an HVC with `n` ingredients
costs `42 n`; a DV costs `84`.  The loss genuinely grows with `n` (see PROGRESS.md: a chain of `n` double bonds). -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineRho
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountAsm Finset
open WaveTurbulence.LGSpine.SourceVine (Chain IsSomeVine IsVC IsHV IsHVC IsDV)
set_option linter.unusedSectionVars false
universe u1 u2 u3
variable {V : Type u1} [DecidableEq V] {D : Type u2} [Fintype D] [DecidableEq D] {D' : Type u3} [Fintype D'] [DecidableEq D']

theorem chain_ne {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) : a ≠ b := by
  induction h with
  | single hv => obtain ⟨X, hX⟩ := hv; exact hX.1.2.2.2.1
  | append _ _ _ hac _ => exact hac

theorem chain_left_mem {M : Molecule V D} {S : Finset V} {a b : V} {n : ℕ} (h : Chain M S a b n) : a ∈ S := by
  induction h with
  | single hv => obtain ⟨X, hX⟩ := hv; exact hX.1.2.1
  | append _ _ _ _ ih => exact mem_union_left _ ih

/-- **A chain of `n` vines of `M'` (which agrees with `M` away from `p, q`) costs at most `42 n`.** -/
theorem chain_ladderLoss_le (M : Molecule V D) (hM : M.IsMolecule) (M' : Molecule V D') (hM' : M'.IsMolecule)
    {S : Finset V} {a b : V} {n : ℕ} (h : Chain M' S a b n) :
    ∀ {p q : V}, Agree M M' p q → (p ∈ S → p = a ∨ p = b) → (q ∈ S → q = a ∨ q = b) →
      ladderLoss M (M.atoms \ S) ≤ 42 * n := by
  induction h with
  | single hv =>
    intro p q hA hp hq
    obtain ⟨X, hX⟩ := hv
    have := vine_ladderLoss_le_of_agree M hM M' hM' hA hX hp hq
    omega
  | @append S T a b c n hS hT hST hac ih =>
    intro p q hA hp hq
    obtain ⟨X, hX⟩ := hT
    have hbc : b ≠ c := hX.1.2.2.2.1
    have hcT : c ∈ T := hX.1.2.2.1
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
    have h2 := vine_ladderLoss_le_of_agree M hM M' hM' hA hX (fun hpT => by
      rcases hp (mem_union_right _ hpT) with h | h
      · exact absurd (h ▸ hpT) haT
      · exact Or.inr h) (fun hqT => by
      rcases hq (mem_union_right _ hqT) with h | h
      · exact absurd (h ▸ hqT) haT
      · exact Or.inr h)
    have h3 := ladderLoss_union_le M S T
    omega

/-- **VC**: a vine chain with `n` ingredients costs at most `42 n`. -/
theorem vc_ladderLoss_le (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : IsVC M S a b) :
    ∃ n, 1 ≤ n ∧ ladderLoss M (M.atoms \ S) ≤ 42 * n := by
  obtain ⟨_, n, hn⟩ := h
  refine ⟨n, ?_, chain_ladderLoss_le M hM M hM hn (Agree.refl M a b) (fun h => Or.inl rfl) (fun h => Or.inr rfl)⟩
  induction hn with
  | single _ => exact le_rfl
  | append _ _ _ _ _ => omega

theorem eraseBond_isMolecule_of_ends (M : Molecule V D) (hM : M.IsMolecule) (e : D) {a b : V} (hab : a ≠ b)
    (he : M.ends e = s(a, b)) : (Molecule.eraseBond M e).IsMolecule := by
  have hne : M.atom e ≠ M.atom (M.mate e) := by
    intro h
    apply hab
    have : s(M.atom e, M.atom (M.mate e)) = s(a, b) := he
    rw [← h] at this
    exact (Sym2.eq_iff.1 this).elim (fun h => h.1.symm.trans h.2) (fun h => h.2.symm.trans h.1)
  exact WaveTurbulence.Vine.eraseBond_isMolecule M hM e hne

/-- **HV**: the adjoint of a single vine costs at most `42`. -/
theorem hv_ladderLoss_le (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : IsHV M S a b) :
    ladderLoss M (M.atoms \ S) ≤ 42 := by
  obtain ⟨e, he, X, hX⟩ := h
  have hM' := eraseBond_isMolecule_of_ends M hM e hX.1.2.2.2.1 he
  exact vine_ladderLoss_le_of_agree M hM _ hM' (agree_eraseBond M e he) hX (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)

/-- **HVC**: the adjoint of a chain of `n ≥ 2` vines costs at most `42 n`. -/
theorem hvc_ladderLoss_le (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : IsHVC M S a b) :
    ∃ n, 2 ≤ n ∧ ladderLoss M (M.atoms \ S) ≤ 42 * n := by
  obtain ⟨e, he, _, n, hn2, hn⟩ := h
  have hM' := eraseBond_isMolecule_of_ends M hM e (chain_ne hn) he
  exact ⟨n, hn2, chain_ladderLoss_le M hM _ hM' hn (agree_eraseBond M e he) (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)⟩

/-- **DV**: two type-V vines sharing both joints cost at most `84`. -/
theorem dv_ladderLoss_le (M : Molecule V D) (hM : M.IsMolecule) {S : Finset V} {a b : V} (h : IsDV M S a b) :
    ladderLoss M (M.atoms \ S) ≤ 84 := by
  obtain ⟨A, B, hA, hB, _, rfl⟩ := h
  have h1 := vine_ladderLoss_le_of_agree M hM M hM (Agree.refl M a b) hA (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)
  have h2 := vine_ladderLoss_le_of_agree M hM M hM (Agree.refl M a b) hB (fun _ => Or.inl rfl) (fun _ => Or.inr rfl)
  have := ladderLoss_union_le M A B
  omega

end WaveTurbulence.VineRho
