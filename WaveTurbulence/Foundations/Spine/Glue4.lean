/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Glue3
public import WaveTurbulence.Foundations.Spine.GenClass4
import Mathlib.Tactic
/-! The paired atoms: distinctness, valley property, the forest data. -/
@[expose] public section
open WaveTurbulence.Induct
open Finset
namespace WaveTurbulence.Ladder
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.LadderDisjoint
variable {w d : ℕ} {G : Garden w}

/-- The atom of presentation `π0` at ladder `S`, side `b` (`true` = upper row), position `i`. -/
def atomAt (π0 : PF G) (S : LQ G) (b : Bool) (i : ℕ) : GBranch G.tree :=
  if b then rowN (π0.u S) i else rowN (π0.v S) i

theorem atomAt_mem (π0 : PF G) (S : LQ G) (b : Bool) {i : ℕ} (hi : i ≤ π0.m S) : atomAt π0 S b i ∈ S.1 := by
  have h := π0.atoms S
  unfold atomAt
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [rowN_of_le (π0.v S) hi, ← h]
    simp [Molecule.ladderAtoms]
  · simp only [if_true]
    rw [rowN_of_le (π0.u S) hi, ← h]
    simp [Molecule.ladderAtoms]

theorem atomAt_inj (π0 : PF G) (S S' : LQ G) (b b' : Bool) {i i' : ℕ} (hi : i ≤ π0.m S) (hi' : i' ≤ π0.m S')
    (h : atomAt π0 S b i = atomAt π0 S' b' i') : S = S' ∧ b = b' ∧ i = i' := by
  have hSS : S = S' := by
    by_contra hne
    have hdis := WaveTurbulence.Molecule.maximalLadders_pairwiseDisjoint G.molecule
      (WaveTurbulence.Mole.garden_isMolecule G) S.2 S'.2 (fun h' => hne (Subtype.ext h'))
    have h1 := atomAt_mem π0 S b hi
    have h2 := atomAt_mem π0 S' b' hi'
    rw [h] at h1
    exact Finset.disjoint_left.mp hdis h1 h2
  subst hSS
  unfold atomAt at h
  cases b <;> cases b'
  · simp only [Bool.false_eq_true, if_false] at h
    refine ⟨rfl, rfl, ?_⟩
    by_contra hne
    exact ladderN_vv G.molecule (π0.ladder S) hi hi' hne h
  · simp only [Bool.false_eq_true, if_false, if_true] at h
    exact absurd h.symm (ladderN_uv G.molecule (π0.ladder S) hi' hi)
  · simp only [Bool.false_eq_true, if_false, if_true] at h
    exact absurd h (ladderN_uv G.molecule (π0.ladder S) hi hi')
  · simp only [if_true] at h
    refine ⟨rfl, rfl, ?_⟩
    by_contra hne
    exact ladderN_uu G.molecule (π0.ladder S) hi hi' hne h

variable {D : SplicedKernelData G d} {L γ δ : ℝ} {base : Mom d} {roots : Fin w → (Fin d → ℤ)}
  {hp : G.IsPlain} {π0 : PF G} {εS : LQ G → ℝ}

/-- The paired rungs, as upper and lower atoms. -/
noncomputable def CD.ua (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (s : Jr (cd.Kn isSmall)) : GBranch G.tree := atomAt π0 s.1 true (cd.enum isSmall s.1 s.2)

noncomputable def CD.va (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (s : Jr (cd.Kn isSmall)) : GBranch G.tree := atomAt π0 s.1 false (cd.enum isSmall s.1 s.2)

theorem CD.enum_le (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) (S : LQ G)
    (i : Fin (cd.Kn isSmall S)) : cd.enum isSmall S i ≤ π0.m S :=
  ((cd.JS_sub isSmall S (cd.enum_mem isSmall S i)).1.2).le

theorem CD.elim_injective (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop) :
    Function.Injective (Sum.elim (cd.ua isSmall) (cd.va isSmall)) := by
  have key : ∀ (s s' : Jr (cd.Kn isSmall)) (b b' : Bool),
      atomAt π0 s.1 b (cd.enum isSmall s.1 s.2) = atomAt π0 s'.1 b' (cd.enum isSmall s'.1 s'.2) →
      s = s' ∧ b = b' := by
    rintro ⟨S, i⟩ ⟨S', i'⟩ b b' h
    obtain ⟨h1, h2, h3⟩ := atomAt_inj π0 S S' b b' (cd.enum_le isSmall S i) (cd.enum_le isSmall S' i') h
    subst h1
    refine ⟨?_, h2⟩
    have : i = i' := (cd.enum_strictMono isSmall S).injective h3
    rw [this]
  rintro (s | s) (s' | s') h
  · have := key s s' true true h
    rw [this.1]
  · have := key s s' true false h; simp at this
  · have := key s s' false true h; simp at this
  · have := key s s' false false h
    rw [this.1]

theorem CD.hval (cd : CD G D L γ δ base roots hp π0 εS) (isSmall : LQ G → Prop)
    (t : GBranch G.tree → ℝ) (ht : ∀ b' b : GBranch G.tree, b'.IsChildOf b → t b' < t b)
    (S : LQ G) :
    NP (fun j : Fin (cd.Kn isSmall S) =>
      max (t (cd.ua isSmall ⟨S, j⟩)) (t (cd.va isSmall ⟨S, j⟩))) := by
  have hP : ∀ j, 1 ≤ j → j < π0.m S →
      max (t (rowN (π0.u S) j)) (t (rowN (π0.v S) j)) <
        max (t (rowN (π0.u S) (j - 1))) (t (rowN (π0.v S) (j - 1))) ∨
      max (t (rowN (π0.u S) j)) (t (rowN (π0.v S) j)) <
        max (t (rowN (π0.u S) (j + 1))) (t (rowN (π0.v S) (j + 1))) :=
    fun j h1 h2 => no_peak G (π0.ladder S) t ht h1 h2
  exact NP_sub (fun j => max (t (rowN (π0.u S) j)) (t (rowN (π0.v S) j))) (π0.m S) hP
    (cd.enum isSmall S) (cd.enum_strictMono isSmall S) (cd.enum_le isSmall S)

end WaveTurbulence.Ladder
