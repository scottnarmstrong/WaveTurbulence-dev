/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCCount2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VCCount1
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VCCount2`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 # VINE-COUNT part 19: cardinality of the set `Xset` of admissible chart coordinates for a fixed gap. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount hiding latticePoint_injective latticePoint_sub mem_ladderAtoms
open WaveTurbulence.VineCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.CountLemmas

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

section Cover
variable {M : Molecule V D} {X : VineType} {S : Finset V} {a b : V} (A : FullVineChart M X S a b)

end Cover

section Xs
variable {M : Molecule V D} (K : VineCut g M) {X : VineType} (A : FullVineChart M X K.C.atoms K.C.upper K.C.lower)

/-- The set of admissible chart coordinates for the integer gap `rr`. -/
noncomputable def Xset (L : ℝ) (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d) (β : V → ℝ) (τ : ℝ) (rr : Fin d → ℤ)
    (gainJ : Fin A.indexing.shape.m → Prop) [DecidablePred gainJ]
    (coreP : (Fin A.indexing.shape.n → Fin d → ℤ) → Prop) :
    Set (Fin A.indexing.shape.n → Fin d → ℤ) :=
  {x | Near4 L (cenI K A w k0 r₀ A.indexing.shape.x0) (x A.indexing.shape.x0) ∧
    (∀ j, (x (A.indexing.shape.xSlot j), x (A.indexing.shape.ySlot j)) ∈
      (if gainJ j then rungSet K A L w k0 r₀ β τ rr j else rungSet0 K A L w k0 r₀ β τ j)) ∧ coreP x}

theorem xset_bound_bad (hbad : X.IsBad = true) {L : ℝ} (hL0 : 0 < L) (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d)
    (β : V → ℝ) (τ : ℝ) (rr : Fin d → ℤ) (gainJ : Fin A.indexing.shape.m → Prop) [DecidablePred gainJ]
    (bP : Fin A.indexing.shape.m → ℝ)
    (hP : ∀ j, (if gainJ j then rungSet K A L w k0 r₀ β τ rr j else rungSet0 K A L w k0 r₀ β τ j).Finite ∧
      ((if gainJ j then rungSet K A L w k0 r₀ β τ rr j else rungSet0 K A L w k0 r₀ β τ j).ncard : ℝ) ≤ bP j) :
    (Xset K A L w k0 r₀ β τ rr gainJ (fun _ => True)).Finite ∧
    ((Xset K A L w k0 r₀ β τ rr gainJ (fun _ => True)).ncard : ℝ) ≤
      ((coverNum d : ℝ) * (2 * L + 1) ^ d) * (∏ j, bP j) * 1 := by
  have hcov : ∀ i : Fin A.indexing.shape.n, i = A.indexing.shape.x0 ∨
      (∃ j, i = A.indexing.shape.xSlot j ∨ i = A.indexing.shape.ySlot j) ∨
        ∃ c : Fin 0, i = (Fin.elim0 c : Fin A.indexing.shape.n) := by
    intro i
    rcases fin_cover A i with h | h | ⟨hn, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rw [hbad] at hn; exact absurd hn (by simp)
  refine ncard_blocks_le_real (A := Fin d → ℤ) (k := 0) A.indexing.shape.x0 A.indexing.shape.xSlot
    A.indexing.shape.ySlot Fin.elim0 hcov _
    {z | Near4 L (cenI K A w k0 r₀ A.indexing.shape.x0) z} (finite_near4 hL0 _)
    (fun j => if gainJ j then rungSet K A L w k0 r₀ β τ rr j else rungSet0 K A L w k0 r₀ β τ j)
    (fun j => (hP j).1) (Set.univ : Set (Fin 0 → Fin d → ℤ)) Set.finite_univ
    (fun x hx => hx.1) (fun x hx j => hx.2.1 j) (fun x _ => Set.mem_univ _) _
    (ncard_near4_le hL0 _) bP (fun j => (hP j).2) 1 ?_
  simp

theorem xset_bound_normal (hn : X.IsBad = false) {L : ℝ} (hL0 : 0 < L) (w : Mom d) (k0 : D → Mom d) (r₀ : Mom d)
    (β : V → ℝ) (τ : ℝ) (rr : Fin d → ℤ) (gainJ : Fin A.indexing.shape.m → Prop) [DecidablePred gainJ]
    (bP : Fin A.indexing.shape.m → ℝ)
    (hP : ∀ j, (if gainJ j then rungSet K A L w k0 r₀ β τ rr j else rungSet0 K A L w k0 r₀ β τ j).Finite ∧
      ((if gainJ j then rungSet K A L w k0 r₀ β τ rr j else rungSet0 K A L w k0 r₀ β τ j).ncard : ℝ) ≤ bP j)
    (α₀ β₀ : ℝ) (bU : ℝ)
    (hU : (TripleSet L (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 0)) (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 1))
        (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 2)) A.coreLinear α₀ β₀ τ).Finite ∧
      ((TripleSet L (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 0)) (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 1))
        (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 2)) A.coreLinear α₀ β₀ τ).ncard : ℝ) ≤ bU) :
    (Xset K A L w k0 r₀ β τ rr gainJ (fun x => (x (A.indexing.shape.uSlot hn 0), x (A.indexing.shape.uSlot hn 1),
      x (A.indexing.shape.uSlot hn 2)) ∈ TripleSet L (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 0))
        (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 1)) (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 2))
        A.coreLinear α₀ β₀ τ)).Finite ∧
    ((Xset K A L w k0 r₀ β τ rr gainJ (fun x => (x (A.indexing.shape.uSlot hn 0), x (A.indexing.shape.uSlot hn 1),
      x (A.indexing.shape.uSlot hn 2)) ∈ TripleSet L (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 0))
        (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 1)) (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 2))
        A.coreLinear α₀ β₀ τ)).ncard : ℝ) ≤
      ((coverNum d : ℝ) * (2 * L + 1) ^ d) * (∏ j, bP j) * bU := by
  set T := TripleSet L (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 0)) (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 1))
        (cenI K A w k0 r₀ (A.indexing.shape.uSlot hn 2)) A.coreLinear α₀ β₀ τ with hT
  let us : Fin 3 → Fin A.indexing.shape.n := fun c => A.indexing.shape.uSlot hn c
  have hcov : ∀ i : Fin A.indexing.shape.n, i = A.indexing.shape.x0 ∨
      (∃ j, i = A.indexing.shape.xSlot j ∨ i = A.indexing.shape.ySlot j) ∨ ∃ c : Fin 3, i = us c := by
    intro i
    rcases fin_cover A i with h | h | ⟨hn', c, hc⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨c, hc⟩)
  let U : Set (Fin 3 → Fin d → ℤ) := {f | (f 0, f 1, f 2) ∈ T}
  have hUinj : ∀ f ∈ U, ∀ f' ∈ U, (f 0, f 1, f 2) = (f' 0, f' 1, f' 2) → f = f' := by
    intro f _ f' _ h
    have h0 : f 0 = f' 0 := congrArg Prod.fst h
    have h1 : f 1 = f' 1 := congrArg (fun t => t.2.1) h
    have h2 : f 2 = f' 2 := congrArg (fun t => t.2.2) h
    funext i; fin_cases i <;> assumption
  have hUfin : U.Finite := by
    apply hU.1.preimage
    intro f hf f' hf' h; exact hUinj f hf f' hf' h
  have hUcard : (U.ncard : ℝ) ≤ bU := by
    refine le_trans ?_ hU.2
    have := Set.ncard_le_ncard_of_injOn (fun f : Fin 3 → Fin d → ℤ => (f 0, f 1, f 2)) (s := U) (t := T)
      (fun f hf => hf) (fun f hf f' hf' h => hUinj f hf f' hf' h) hU.1
    exact_mod_cast this
  refine ncard_blocks_le_real (A := Fin d → ℤ) (k := 3) A.indexing.shape.x0 A.indexing.shape.xSlot
    A.indexing.shape.ySlot us hcov _
    {z | Near4 L (cenI K A w k0 r₀ A.indexing.shape.x0) z} (finite_near4 hL0 _)
    (fun j => if gainJ j then rungSet K A L w k0 r₀ β τ rr j else rungSet0 K A L w k0 r₀ β τ j)
    (fun j => (hP j).1) U hUfin
    (fun x hx => hx.1) (fun x hx j => hx.2.1 j) (fun x hx => hx.2.2) _
    (ncard_near4_le hL0 _) bP (fun j => (hP j).2) bU hUcard

end Xs

end WaveTurbulence.GammaLow.FinalCount.Step1
