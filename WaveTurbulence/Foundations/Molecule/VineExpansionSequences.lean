/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineEndpointBounds
import Mathlib.Tactic

/-! # Actual rung sequences in complete literal template expansions -/

public section
namespace WaveTurbulence.Vine

/-- Slot endpoints in every pinned core lie in its original atom range. -/
theorem template_slot_endpoints (X : VineType) :
    ∀ s ∈ X.template.slots,s.1.1<X.template.n ∧ s.1.2<X.template.n ∧
      s.2.1<X.template.n ∧ s.2.2<X.template.n := by
  cases X <;> decide

/-- The selected insertion in an arbitrary fold supplies a full-rung
sequence in the final template, with the exact allocated labels retained. -/
theorem fold_has_insertedSequence_ports (T : VineTemplate)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hT : ∀ p ∈ T.bonds,p.1<T.n ∧ p.2<T.n)
    (hs : ∀ sk ∈ pre++(s,k)::post,sk.1.1.1<T.n ∧ sk.1.1.2<T.n ∧
      sk.1.2.1<T.n ∧ sk.1.2.2<T.n) :
    let U := pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T
    ∃ L : LiteralFullRungSequence
        ((pre++(s,k)::post).foldl (fun U sk => insertRungs U sk.1 sk.2) T) k,
      ((L.u 0).1=s.1.1 ∧ (L.v 0).1=s.2.1 ∧
        (L.u (k+1)).1=s.1.2 ∧ (L.v (k+1)).1=s.2.2) ∧
      ∀ i,1 ≤ i → i ≤ k → (L.u i).1=U.n+(i-1) ∧ (L.v i).1=U.n+k+(i-1) := by
  dsimp only
  let U := pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T
  have hmono : T.n ≤ U.n := by dsimp only [U]; rw [fold_insertRungs_atoms]; omega
  have hU := fold_insertRungs_endpoints pre T hT (fun z hz => hs z (List.mem_append_left _ hz))
  have hs0 := hs (s,k) (List.mem_append_right _ List.mem_cons_self)
  dsimp only at hs0
  have hsU : s.1.1<U.n ∧ s.1.2<U.n ∧ s.2.1<U.n ∧ s.2.2<U.n := by
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  let L := insertedSequence U s k hU hsU
  have hu : ∀ sk ∈ post,∀ i,1 ≤ i → i ≤ k →
      sk.1.1.1 ≠ (L.u i).1 ∧ sk.1.1.2 ≠ (L.u i).1 ∧
      sk.1.2.1 ≠ (L.u i).1 ∧ sk.1.2.2 ≠ (L.u i).1 := by
    intro z hz i hi hin
    have hh := hs z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))
    dsimp only [L,insertedSequence]
    rw [railAtom_interior _ _ _ _ _ hi hin]
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  have hv : ∀ sk ∈ post,∀ i,1 ≤ i → i ≤ k →
      sk.1.1.1 ≠ (L.v i).1 ∧ sk.1.1.2 ≠ (L.v i).1 ∧
      sk.1.2.1 ≠ (L.v i).1 ∧ sk.1.2.2 ≠ (L.v i).1 := by
    intro z hz i hi hin
    have hh := hs z (List.mem_append_right _ (List.mem_cons_of_mem _ hz))
    dsimp only [L,insertedSequence]
    rw [railAtom_interior _ _ _ _ _ hi hin]
    constructor
    · omega
    constructor
    · omega
    constructor <;> omega
  rw [List.foldl_append,List.foldl_cons]
  refine ⟨L.afterInsertions post hu hv,⟨rfl,rfl,?_,?_⟩,?_⟩
  · change railAtom U.n s.1.1 s.1.2 k (k+1)=s.1.2
    simp [railAtom]
  · change railAtom (U.n+k) s.2.1 s.2.2 k (k+1)=s.2.2
    simp [railAtom]
  intro i hi hin
  change railAtom U.n s.1.1 s.1.2 k i=U.n+(i-1) ∧
    railAtom (U.n+k) s.2.1 s.2.2 k i=U.n+k+(i-1)
  exact ⟨railAtom_interior _ _ _ _ _ hi hin,railAtom_interior _ _ _ _ _ hi hin⟩

/-- The allocation-interval projection of the endpoint-preserving sequence. -/
theorem fold_has_insertedSequence (T : VineTemplate)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hT : ∀ p ∈ T.bonds,p.1<T.n ∧ p.2<T.n)
    (hs : ∀ sk ∈ pre++(s,k)::post,sk.1.1.1<T.n ∧ sk.1.1.2<T.n ∧
      sk.1.2.1<T.n ∧ sk.1.2.2<T.n) :
    let U := pre.foldl (fun U sk => insertRungs U sk.1 sk.2) T
    ∃ L : LiteralFullRungSequence
        ((pre++(s,k)::post).foldl (fun U sk => insertRungs U sk.1 sk.2) T) k,
      ∀ i,1 ≤ i → i ≤ k → (L.u i).1=U.n+(i-1) ∧ (L.v i).1=U.n+k+(i-1) := by
  obtain ⟨L,_hports,hL⟩ := fold_has_insertedSequence_ports T pre post s k hT hs
  exact ⟨L,hL⟩

/-- Every slot of a complete pinned expansion supplies its literal rung
sequence, retaining its allocation interval. The list equality simply locates
the slot in the expansion fold. -/
theorem expand_has_insertedSequence (X : VineType) (ks : List ℕ)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip ks=pre++(s,k)::post) :
    let U := pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template
    ∃ L : LiteralFullRungSequence (X.expand ks) k,
      ∀ i,1 ≤ i → i ≤ k → (L.u i).1=U.n+(i-1) ∧ (L.v i).1=U.n+k+(i-1) := by
  have hh := fold_has_insertedSequence X.template pre post s k (template_endpoints X) (by
    intro sk hsk
    rw [← hloc] at hsk
    exact template_slot_endpoints X sk.1 (List.of_mem_zip hsk).1)
  rw [← hloc] at hh
  exact hh

/-- In the actual molecule, every expanded slot carries the full sequence
of its allocated rungs. This consumes only the pinned realization data. -/
theorem VineRealization.has_rungSequence {V D : Type*} [DecidableEq V]
    [Fintype D] [DecidableEq D] {M : Molecule V D} {X : VineType}
    {S : Finset V} {a b : V} (R : VineRealization M X S a b)
    (pre post : List (((ℕ×ℕ)×(ℕ×ℕ))×ℕ)) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hloc : X.template.slots.zip R.k=pre++(s,k)::post) :
    let U := pre.foldl (fun U sk => insertRungs U sk.1 sk.2) X.template
    ∃ Q : FullRungSequence M k,∀ i,1 ≤ i → i ≤ k →
      Q.u i ∈ S ∧ Q.v i ∈ S ∧ R.f (Q.u i)=U.n+(i-1) ∧
        R.f (Q.v i)=U.n+k+(i-1) := by
  obtain ⟨L,hL⟩ := expand_has_insertedSequence X R.k pre post s k hloc
  refine ⟨L.realize R,?_⟩
  intro i hi hin
  refine ⟨(R.atomAt (L.u i)).2,(R.atomAt (L.v i)).2,?_,?_⟩
  · exact (R.label_atomAt (L.u i)).trans (hL i hi hin).1
  · exact (R.label_atomAt (L.v i)).trans (hL i hi hin).2

end WaveTurbulence.Vine
