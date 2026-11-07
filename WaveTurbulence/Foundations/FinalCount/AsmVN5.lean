/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN4
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 5): the twin gaps of an object.**  For an object `O` (ordinary or hyper) and a labelling `k`
that is mate-symmetric and conserved at degree-four atoms, the oriented gaps at the two joints are opposite:
`(k p - k q) + (k p' - k q') = 0` for the `ContainsDart` pairs `(p,q)` at the upper and `(p',q')` at the lower joint
(`object_gap_twin`).  The proof sums `dartSign • k` over all `ContainsDart` darts (an involution-cancelling sum), whose interior atoms
contribute their full conservation; it covers both shapes without passing to the adjoint molecule. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}
  {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem sum_containsDart_zero (O : Object M) (k : D → E) (hk : ∀ x, k (M.mate x) = k x) :
    ∑ z ∈ univ.filter (fun z => O.ContainsDart z), M.dartSign z • k z = 0 := by
  apply Finset.sum_involution (fun x _ => M.mate x)
  · intro x _
    rw [hk x, Mole.dartSign_mate, neg_smul, add_neg_cancel]
  · intro x _ _
    exact M.mate_ne x
  · intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx ⊢
    exact containsDart_mate O hx
  · intro x _
    exact M.mate_mate x

theorem object_gap_twin (O : Object M) (hdeg : ∀ b ∈ M.atoms, M.deg b ≤ 4) (k : D → E) (hk : ∀ x, k (M.mate x) = k x)
    (hc : ∀ v ∈ M.atoms, M.deg v = 4 → ∑ x ∈ M.dartsAt v, M.dartSign x • k x = 0) {p q p' q' : D}
    (hP : SourceObjectJointPair O O.upper p q) (hQ : SourceObjectJointPair O O.lower p' q') :
    (k p - k q) + (k p' - k q') = 0 := by
  have hb := (object_oh O).basic
  have hint := hb.2.2.2.2.2.2
  have hne : O.upper ≠ O.lower := hb.2.2.2.1
  set T := univ.filter (fun z => O.ContainsDart z) with hT
  have h0 := sum_containsDart_zero O k hk
  have hfib := Finset.sum_fiberwise_of_maps_to (s := T) (t := O.atoms) (g := M.atom)
    (fun z hz => (containsDart_inGroup O (mem_filter.mp hz).2).1) (fun z => M.dartSign z • k z)
  rw [h0] at hfib
  -- the fibre over a joint
  have hfibU : T.filter (fun z => M.atom z = O.upper) = {p, q} := by
    ext z
    simp only [hT, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hz, ha⟩
      exact cd_at_joint_eq O (Or.inl rfl) hP.1 hP.2.1 hP.2.2.1 hP.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2 ha hz
    · rintro (rfl | rfl)
      · exact ⟨hP.2.2.1, hP.1⟩
      · exact ⟨hP.2.2.2.1, hP.2.1⟩
  have hfibL : T.filter (fun z => M.atom z = O.lower) = {p', q'} := by
    ext z
    simp only [hT, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨hz, ha⟩
      exact cd_at_joint_eq O (Or.inr rfl) hQ.1 hQ.2.1 hQ.2.2.1 hQ.2.2.2.1 hQ.2.2.2.2.1 hQ.2.2.2.2.2 ha hz
    · rintro (rfl | rfl)
      · exact ⟨hQ.2.2.1, hQ.1⟩
      · exact ⟨hQ.2.2.2.1, hQ.2.1⟩
  have hpq : p ≠ q := fun e => by have := hP.2.2.2.2.1; have := hP.2.2.2.2.2; simp_all
  have hpq' : p' ≠ q' := fun e => by have := hQ.2.2.2.2.1; have := hQ.2.2.2.2.2; simp_all
  have hsp : M.dartSign p = 1 := by simp [Molecule.dartSign, hP.2.2.2.2.1]
  have hsq : M.dartSign q = -1 := by simp [Molecule.dartSign, hP.2.2.2.2.2]
  have hsp' : M.dartSign p' = 1 := by simp [Molecule.dartSign, hQ.2.2.2.2.1]
  have hsq' : M.dartSign q' = -1 := by simp [Molecule.dartSign, hQ.2.2.2.2.2]
  have hlow : O.lower ∈ O.atoms.erase O.upper := Finset.mem_erase.mpr ⟨hne.symm, hb.2.2.1⟩
  rw [← Finset.add_sum_erase _ _ hb.2.1, ← Finset.add_sum_erase _ _ hlow, hfibU, hfibL] at hfib
  have hrest : ∑ v ∈ (O.atoms.erase O.upper).erase O.lower, ∑ z ∈ T.filter (fun z => M.atom z = v), M.dartSign z • k z = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    obtain ⟨h1, h2⟩ := Finset.mem_erase.mp hv
    obtain ⟨h3, h4⟩ := Finset.mem_erase.mp h2
    have hfv : T.filter (fun z => M.atom z = v) = M.dartsAt v := by
      ext z
      simp only [hT, mem_filter, mem_univ, true_and, Molecule.dartsAt]
      constructor
      · exact fun h => h.2
      · intro hz
        exact ⟨containsDart_of_interior O hdeg hint (hz ▸ h4) (hz ▸ h3) (hz ▸ h1), hz⟩
    rw [hfv]
    have hvm : v ∈ M.atoms := hb.1 h4
    have hd4 : M.deg v = 4 := by
      have h5 := hint v h4 h3 h1
      have h6 := hdeg v hvm
      have h7 : M.degIn O.atoms v ≤ M.deg v := Mole.degIn_le_deg M O.atoms v
      omega
    exact hc v hvm hd4
  rw [hrest, add_zero, Finset.sum_pair hpq, Finset.sum_pair hpq', hsp, hsq, hsp', hsq'] at hfib
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hfib

/-- **The gap of an object is the gap of its oriented joint pair** (both shapes): if the object has gap kind `kind` for `κ`, the
`ContainsDart` pair `(p, q)` at its upper joint (out `p`, in `q`) has `gapKind (gapAt p q) = kind`. -/
theorem object_gapKind_pair {d : ℕ} (O : Object M) (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (kind : Molecule.GapKind)
    (hP : O.HasGapKind L γ η w κ kind) {p q : D} (hpq : SourceObjectJointPair O O.upper p q) :
    Molecule.gapKind L γ η (Molecule.gapAt L w κ p q) = kind := by
  rcases O with ⟨S, a, b, shape⟩
  rcases hP with ⟨r, hr, hkind⟩
  cases shape with
  | vc hVC =>
    obtain ⟨x, y, hx, hy, hgx, hgy, hox, hoy, hgap⟩ := hr
    have hu := source_object_joint_pair_unique (⟨S, a, b, .vc hVC⟩ : Object M) (v := a) (Or.inl rfl)
      (x := x) (y := y) (x' := p) (y' := q) ⟨hx, hy, hgx, hgy, hox, hoy⟩ hpq
    rw [hgap] at hkind
    rw [← hu.1, ← hu.2]; exact hkind
  | hyper R =>
    obtain ⟨x, y, hx, hy, hgx, hgy, hox, hoy, hgap⟩ := hr
    have hgap' : r = Molecule.gapAt L w κ x.1 y.1 := hgap
    have hu := source_object_joint_pair_unique (⟨S, a, b, .hyper R⟩ : Object M) (v := a) (Or.inl rfl)
      (x := x.1) (y := y.1) (x' := p) (y' := q)
      ⟨hx, hy, ⟨x.2.1, x.2.2, hgx⟩, ⟨y.2.1, y.2.2, hgy⟩, hox, hoy⟩ hpq
    rw [hgap'] at hkind
    rw [← hu.1, ← hu.2]; exact hkind

end WaveTurbulence.FinalCountAsm
