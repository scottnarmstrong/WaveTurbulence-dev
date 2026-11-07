/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN1
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 2): a `VineCut` along an arbitrary object.**  For an object `O` of a molecule `M` (degrees `≤ 4`,
no loops) and two fresh atoms `fa ≠ fb`, cutting at the two joints along the oriented `ContainsDart` pairs gives a `VineCut` with `C = O`:
a dart of the doubly cut molecule has its atom in `O.atoms` iff it is a `ContainsDart` dart of `O` (`cut2_atom_mem_iff`), and `ContainsDart`
is mate-symmetric, so the complement is closed (`closed`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem cut2_atom_mem_iff (O : Object M) (hdeg : ∀ b ∈ M.atoms, M.deg b ≤ 4) (fa fb : V) (hfa : fa ∉ M.atoms)
    (hfb : fb ∉ M.atoms) {x₁ x₂ y₁ y₂ : D}
    (hx : SourceObjectJointPair O O.upper x₂ x₁) (hy : SourceObjectJointPair O O.lower y₂ y₁) (z : D) :
    ((M.cut O.upper fa x₁ x₂).cut O.lower fb y₁ y₂).atom z ∈ O.atoms ↔ O.ContainsDart z := by
  have hb := (object_oh O).basic
  have hint := hb.2.2.2.2.2.2
  have hsub : O.atoms ⊆ M.atoms := hb.1
  have hne : O.upper ≠ O.lower := hb.2.2.2.1
  have e : ((M.cut O.upper fa x₁ x₂).cut O.lower fb y₁ y₂).atom z =
      if (if M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂ then fa else M.atom z) = O.lower ∧ z ≠ y₁ ∧ z ≠ y₂ then fb
      else (if M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂ then fa else M.atom z) := rfl
  rw [e]
  constructor
  · intro h
    by_cases h1 : M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂
    · rw [if_pos h1] at h
      split_ifs at h with h2
      · exact absurd (hsub h) hfb
      · exact absurd (hsub h) hfa
    · rw [if_neg h1] at h
      by_cases h2 : M.atom z = O.lower ∧ z ≠ y₁ ∧ z ≠ y₂
      · rw [if_pos h2] at h; exact absurd (hsub h) hfb
      · rw [if_neg h2] at h
        by_cases ha : M.atom z = O.upper
        · have : z = x₁ ∨ z = x₂ := by
            by_contra hc; push Not at hc; exact h1 ⟨ha, hc.1, hc.2⟩
          rcases this with rfl | rfl
          · exact hx.2.2.2.1
          · exact hx.2.2.1
        · by_cases hl : M.atom z = O.lower
          · have : z = y₁ ∨ z = y₂ := by
              by_contra hc; push Not at hc; exact h2 ⟨hl, hc.1, hc.2⟩
            rcases this with rfl | rfl
            · exact hy.2.2.2.1
            · exact hy.2.2.1
          · exact containsDart_of_interior O hdeg hint h ha hl
  · intro h
    have hg := containsDart_inGroup O h
    have hza : M.atom z ∈ O.atoms := hg.1
    by_cases ha : M.atom z = O.upper
    · have hz12 : z = x₂ ∨ z = x₁ := cd_at_joint_eq O (Or.inl rfl) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1
        hx.2.2.2.2.2 ha h
      have h1 : ¬ (M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂) := by
        rintro ⟨-, h3, h4⟩; rcases hz12 with r | r <;> contradiction
      rw [if_neg h1, if_neg (by rintro ⟨h5, -⟩; exact hne (ha.symm.trans h5))]
      exact hza
    · by_cases hl : M.atom z = O.lower
      · have hz12 : z = y₂ ∨ z = y₁ := cd_at_joint_eq O (Or.inr rfl) hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1
          hy.2.2.2.2.2 hl h
        have h1 : ¬ (M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂) := fun h5 => ha h5.1
        have h2 : ¬ (M.atom z = O.lower ∧ z ≠ y₁ ∧ z ≠ y₂) := by
          rintro ⟨-, h3, h4⟩; rcases hz12 with r | r <;> contradiction
        rw [if_neg h1, if_neg (fun h5 => h2 ⟨hl, h5.2⟩)]
        exact hza
      · have h1 : ¬ (M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂) := fun h5 => ha h5.1
        have h2 : ¬ (M.atom z = O.lower ∧ z ≠ y₁ ∧ z ≠ y₂) := fun h5 => hl h5.1
        rw [if_neg h1, if_neg (fun h5 => h2 ⟨h5.1.trans rfl |>.trans rfl, h5.2⟩)]
        exact hza

theorem cut2_atom_eq_of_cd (O : Object M) (fa fb : V) {x₁ x₂ y₁ y₂ : D}
    (hx : SourceObjectJointPair O O.upper x₂ x₁) (hy : SourceObjectJointPair O O.lower y₂ y₁) (z : D)
    (h : O.ContainsDart z) : ((M.cut O.upper fa x₁ x₂).cut O.lower fb y₁ y₂).atom z = M.atom z := by
  have hne : O.upper ≠ O.lower := (object_oh O).basic.2.2.2.1
  have e : ((M.cut O.upper fa x₁ x₂).cut O.lower fb y₁ y₂).atom z =
      if (if M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂ then fa else M.atom z) = O.lower ∧ z ≠ y₁ ∧ z ≠ y₂ then fb
      else (if M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂ then fa else M.atom z) := rfl
  rw [e]
  by_cases ha : M.atom z = O.upper
  · have hz12 : z = x₂ ∨ z = x₁ := cd_at_joint_eq O (Or.inl rfl) hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hx.2.2.2.2.1
      hx.2.2.2.2.2 ha h
    have h1 : ¬ (M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂) := by
      rintro ⟨-, h3, h4⟩; rcases hz12 with r | r <;> contradiction
    rw [if_neg h1, if_neg (by rintro ⟨h5, -⟩; exact hne (ha.symm.trans h5))]
  · by_cases hl : M.atom z = O.lower
    · have hz12 : z = y₂ ∨ z = y₁ := cd_at_joint_eq O (Or.inr rfl) hy.1 hy.2.1 hy.2.2.1 hy.2.2.2.1 hy.2.2.2.2.1
        hy.2.2.2.2.2 hl h
      have h1 : ¬ (M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂) := fun h5 => ha h5.1
      have h2 : ¬ (M.atom z = O.lower ∧ z ≠ y₁ ∧ z ≠ y₂) := by
        rintro ⟨-, h3, h4⟩; rcases hz12 with r | r <;> contradiction
      rw [if_neg h1, if_neg (fun h5 => h2 ⟨hl, h5.2⟩)]
    · have h1 : ¬ (M.atom z = O.upper ∧ z ≠ x₁ ∧ z ≠ x₂) := fun h5 => ha h5.1
      have h2 : ¬ (M.atom z = O.lower ∧ z ≠ y₁ ∧ z ≠ y₂) := fun h5 => hl h5.1
      rw [if_neg h1, if_neg (fun h5 => h2 ⟨h5.1, h5.2⟩)]

/-- **A `VineCut` along an arbitrary object** (fresh joints `fa ≠ fb`, loop-free molecule of degrees `≤ 4`). -/
theorem exists_vineCut_of_object (O : Object M) (hdeg : ∀ b ∈ M.atoms, M.deg b ≤ 4)
    (hnl : ∀ x, M.atom x ≠ M.atom (M.mate x)) (fa fb : V) (hfa : fa ∉ M.atoms) (hfb : fb ∉ M.atoms) (hfab : fa ≠ fb) :
    ∃ K : VineCut M, K.C = O ∧ K.fa = fa ∧ K.fb = fb := by
  have hb := (object_oh O).basic
  have hne : O.upper ≠ O.lower := hb.2.2.2.1
  obtain ⟨p, q, hp⟩ := object_joint_pair_exists O (v := O.upper) (Or.inl rfl)
  obtain ⟨p', q', hq⟩ := object_joint_pair_exists O (v := O.lower) (Or.inr rfl)
  have hP : SourceObjectJointPair O O.upper p q := hp
  have hQ : SourceObjectJointPair O O.lower p' q' := hq
  have key := cut2_atom_mem_iff O hdeg fa fb hfa hfb hP hQ
  have hmemU : O.upper ∈ M.atoms := hb.1 hb.2.1
  have hmemL : O.lower ∈ M.atoms := hb.1 hb.2.2.1
  refine ⟨⟨O, fa, fb, q, p, q', p', hb.2.1, hb.2.2.1, hne, ?_, ?_, ⟨hP.2.2.2.1, hP.2.2.1⟩,
    ⟨hQ.2.2.2.1, hQ.2.2.1⟩, ?_⟩, rfl, rfl, rfl⟩
  · refine ⟨hmemU, hfa, hP.2.1, hP.1, ?_, hP.2.2.2.2.2, hP.2.2.2.2.1⟩
    intro e
    exact hnl q (by rw [hP.2.1, ← e, hP.1])
  · refine ⟨Finset.mem_insert_of_mem hmemL, ?_, ?_, ?_, ?_, hQ.2.2.2.2.2, hQ.2.2.2.2.1⟩
    · intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hfab h.symm
      · exact hfb h
    · show (if M.atom q' = O.upper ∧ q' ≠ q ∧ q' ≠ p then fa else M.atom q') = O.lower
      rw [if_neg (by rintro ⟨h, -⟩; exact hne (h.symm.trans hQ.2.1)), hQ.2.1]
    · show (if M.atom p' = O.upper ∧ p' ≠ q ∧ p' ≠ p then fa else M.atom p') = O.lower
      rw [if_neg (by rintro ⟨h, -⟩; exact hne (h.symm.trans hQ.1)), hQ.1]
    · intro e
      have e' : p' = M.mate q' := e
      exact hnl q' (by rw [hQ.2.1, ← e', hQ.1])
  · intro z hz hz'
    exact hz ((key z).mpr (by
      have := containsDart_mate O ((key (M.mate z)).mp hz')
      rwa [M.mate_mate] at this))

end WaveTurbulence.FinalCountAsm
