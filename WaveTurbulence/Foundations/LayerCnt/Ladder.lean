/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.Interior
public import WaveTurbulence.Foundations.LayerCnt.ParentChain
public import WaveTurbulence.Foundations.LayerCnt.Count

/-! # Interior bound for a rung sequence (TARGET layerlad)

For a rung sequence (interior atoms of degree four) in a molecule in which every degree-four atom has a
parent (an adjacent atom of smaller depth and larger-or-equal layer), the rail variation of a layering with
`k` incoherent rungs is at most `8𝔇(k+1)` and the interior dart sum at most `20𝔇(k+1)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open Finset WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Every atom of degree at least four has a parent. -/
@[expose] def ParentProp (f depth : V → ℕ) : Prop :=
  ∀ x : V, 4 ≤ M.deg x → ∃ d, M.atom d = x ∧ depth (M.atom (M.mate d)) < depth x ∧
    f x ≤ f (M.atom (M.mate d))

theorem hasParents_of_molecule (hM : M.IsMolecule) {n : ℕ} (R : FullRungSequence M n) {f depth : V → ℕ}
    (hP : ParentProp M f depth) : HasParents f depth R.u R.v n := by
  have key : ∀ {x : V} {ns : Fin 4 → V} (R4 : FourIncidences M x ns),
      ∃ y, (∃ j, y = ns j) ∧ depth y < depth x ∧ f x ≤ f y := by
    intro x ns R4
    have hdeg : 4 ≤ M.deg x := by
      unfold Molecule.deg
      rw [← fourIncidences_image M hM R4, Finset.card_image_of_injective _ R4.injective]
      simp
    obtain ⟨d, hd1, hd2, hd3⟩ := hP x hdeg
    have hmem : d ∈ M.dartsAt x := (Mole.mem_dartsAt M x d).mpr hd1
    rw [← fourIncidences_image M hM R4] at hmem
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hmem
    rw [R4.neighbor_eq] at hd2 hd3
    exact ⟨ns j, ⟨j, rfl⟩, hd2, hd3⟩
  intro i hi1 hi2
  constructor
  · obtain ⟨y, ⟨j, rfl⟩, h2, h3⟩ := key (R.upper i hi1 hi2)
    refine ⟨_, ?_, h2, h3⟩
    fin_cases j <;> simp
  · obtain ⟨y, ⟨j, rfl⟩, h2, h3⟩ := key (R.lower i hi1 hi2)
    refine ⟨_, ?_, h2, h3⟩
    fin_cases j <;> simp

/-- The interior dart sum for a layering with `k` incoherent interior rungs. -/
theorem interior_dartSum_bound (hM : M.IsMolecule) {n : ℕ} (R : FullRungSequence M n) {f depth : V → ℕ}
    {𝔇 : ℕ} (hf : ∀ x, f x ≤ 𝔇) (hP : ParentProp M f depth) (A B : ℕ → ℕ)
    (hA : ∀ i, A i = f (R.u i)) (hB : ∀ i, B i = f (R.v i)) {k : ℕ} (hk : incCnt A B 1 n ≤ k) :
    tvab A B 1 n ≤ 8 * 𝔇 * (k + 1) ∧
    ∑ a ∈ intAtoms R.u R.v n, ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) ≤ 20 * 𝔇 * (k + 1) := by
  have hnp : NoPeak A B n := by
    have := noPeak_of_parents (hasParents_of_molecule M hM R hP)
    have eA : A = fun i => f (R.u i) := funext hA
    have eB : B = fun i => f (R.v i) := funext hB
    rw [eA, eB]; exact this
  have ht := tvab_le (𝔇 := 𝔇) hnp k 1 n le_rfl (le_refl n) hk
    (fun i _ _ => ⟨(hA i) ▸ hf _, (hB i) ▸ hf _⟩)
  refine ⟨ht, ?_⟩
  have := interior_dartSum_le M hM R hf A B hA hB
  have h2 : 𝔇 * incCnt A B 1 n ≤ 𝔇 * k := Nat.mul_le_mul_left _ hk
  nlinarith

/-- Dart sum splits into an interior part and at most `4𝔇` per remaining atom. -/
theorem dartExp_le_split (hM : M.IsMolecule) {S I : Finset V} (hI : I ⊆ S) {f : V → ℕ} {𝔇 : ℕ}
    (hf : ∀ x, f x ≤ 𝔇) :
    dartExp M S f ≤ ∑ a ∈ I, ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) +
      4 * 𝔇 * (S \ I).card := by
  unfold dartExp
  rw [← Finset.sum_sdiff hI, add_comm]
  refine Nat.add_le_add (le_refl _) ?_
  calc ∑ a ∈ S \ I, ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x)))
      ≤ ∑ a ∈ S \ I, 4 * 𝔇 := by
        apply Finset.sum_le_sum
        intro a ha
        have hdeg : (M.dartsAt a).card ≤ 4 := by
          by_cases ha : a ∈ M.atoms
          · exact Mole.deg_le_four M hM ha
          · have : M.dartsAt a = ∅ := by
              apply Finset.eq_empty_of_forall_notMem
              intro d hd
              exact ha (((Mole.mem_dartsAt M a d).mp hd) ▸ M.atom_mem d)
            rw [this]; simp
        calc ∑ x ∈ M.dartsAt a, dst (f a) (f (M.atom (M.mate x))) ≤ ∑ x ∈ M.dartsAt a, 𝔇 :=
              Finset.sum_le_sum (fun x _ => dst_le (hf _) (hf _))
          _ = (M.dartsAt a).card * 𝔇 := by simp
          _ ≤ 4 * 𝔇 := Nat.mul_le_mul_right _ hdeg
    _ = 4 * 𝔇 * (S \ I).card := by simp [mul_comm]

end WaveTurbulence.LayerCnt
