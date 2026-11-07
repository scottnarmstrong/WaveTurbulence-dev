/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3VineExt
public import WaveTurbulence.Foundations.Spine.SourceVineData
/-! **FINALCOUNT-G3: identification of a final vine component, part 4** (E10): the final vine component, with its
joints replaced by their ancestors, is an `Object M_sub` (a VC if no extra bond, an HV whose added bond is the unique
extra bond otherwise). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀} {hf : HSt V D₀} {a₀ j₁ j₂ : V}

theorem extras_cases {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hS : SubHyp R M₀) :
    (∀ z, ¬ IsExtra hf a₀ M₀ z) ∨ ∃ e, IsExtra hf a₀ M₀ e ∧ ∀ z, IsExtra hf a₀ M₀ z → z = e ∨ z = M₀.mate e := by
  by_cases h : ∃ e, IsExtra hf a₀ M₀ e
  · right
    obtain ⟨e, he⟩ := h
    refine ⟨e, he, fun z hz => ?_⟩
    by_cases hat : M₀.atom z = M₀.atom e
    · left; exact extra_unique J hA hD hS he hz hat.symm
    · right
      have hanc := anc_ne_joints hA hD hS J.m1 J.m2 J.ne J.d1 J.d2 J.n1 J.n2 J.same J.comp'
      have hat2 : M₀.atom z = M₀.atom (M₀.mate e) := by
        rcases hz.ends J hA hD hS with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rcases he.ends J hA hD hS with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · exact absurd (h1.trans h2.symm) hat
        · rw [h1, h3]
        · rw [h1, h3]
        · exact absurd (h1.trans h2.symm) hat
      exact extra_unique J hA hD hS (he.mate hD) hz hat2.symm
  · left; exact fun z hz => h ⟨z, hz⟩

theorem ancGroup_sub (hA : AncRel M₀ hf.s hf.anc) : AncGroup hf a₀ ⊆ M₀.atoms := by
  intro b hb
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hb
  exact hA.mem c ((mem_compMol _ _).1 hc).1

/-- no extra bond: the component is a vine of `M_sub` on the ancestor group. -/
theorem final_vine_vc {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hS : SubHyp R M₀) {X : VineType} (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂)
    (hne : ∀ z, ¬ IsExtra hf a₀ M₀ z) : M₀.IsVine X (AncGroup hf a₀) (hf.anc j₁) (hf.anc j₂) := by
  have G := comp_groupIso hA hD a₀ (J.injOn hA hD hS) (fun z hz => by
    by_contra hc
    exact hne z ⟨hz, hc⟩)
  exact G.isVine (ancGroup_sub hA) hv

theorem hv_groupIso {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hS : SubHyp R M₀) {e : D₀} (he : IsExtra hf a₀ M₀ e)
    (hall : ∀ z, IsExtra hf a₀ M₀ z → z = e ∨ z = M₀.mate e) :
    ∃ ι : PDart hf.s.M (compP hf.s.M a₀) → {x : D₀ // x ≠ e ∧ x ≠ M₀.mate e},
      (∀ x, (ι x).1 = compEmb hf a₀ x) ∧
      GroupIso (compMol hf.s.M a₀) (compMol hf.s.M a₀).atoms (Molecule.eraseBond M₀ e) (AncGroup hf a₀) hf.anc ι := by
  have hem := he.mate hD
  have hne : ∀ x : PDart hf.s.M (compP hf.s.M a₀), compEmb hf a₀ x ≠ e ∧ compEmb hf a₀ x ≠ M₀.mate e :=
    fun x => ⟨fun h => he.2 ⟨x, h⟩, fun h => hem.2 ⟨x, h⟩⟩
  refine ⟨fun x => ⟨compEmb hf a₀ x, hne x⟩, fun x => rfl, ?_⟩
  refine ⟨fun x => hA.atom x.1, fun x => Subtype.ext (hD.mate x.1), fun x => hD.out x.1,
    fun x y h => Subtype.ext (hA.inj (congrArg Subtype.val h)),
    fun x => ⟨(compMol hf.s.M a₀).atom_mem x, (compMol hf.s.M a₀).atom_mem _⟩, ?_, J.injOn hA hD hS, rfl⟩
  intro z hz
  by_cases hx : ∃ x, compEmb hf a₀ x = z.1
  · obtain ⟨x, hx⟩ := hx
    exact ⟨x, Subtype.ext hx⟩
  · exfalso
    have hex : IsExtra hf a₀ M₀ z.1 := ⟨hz, hx⟩
    rcases hall _ hex with h | h
    · exact z.2.1 h
    · exact z.2.2 h

/-- one extra bond `e`: the component is a vine of the molecule `M_sub` with the bond `e` erased (the adjoint). -/
theorem final_vine_hv {R : ℕ} (J : FinalJoints hf a₀ j₁ j₂) (hA : AncRel M₀ hf.s hf.anc) (hD : DartRel M₀ hf.s)
    (hS : SubHyp R M₀) {X : VineType} (hv : (compMol hf.s.M a₀).IsVine X (compMol hf.s.M a₀).atoms j₁ j₂)
    {e : D₀} (he : IsExtra hf a₀ M₀ e) (hall : ∀ z, IsExtra hf a₀ M₀ z → z = e ∨ z = M₀.mate e) :
    M₀.ends e = s(hf.anc j₁, hf.anc j₂) ∧
      (Molecule.eraseBond M₀ e).IsVine X (AncGroup hf a₀) (hf.anc j₁) (hf.anc j₂) := by
  obtain ⟨ι, -, G⟩ := hv_groupIso J hA hD hS he hall
  refine ⟨?_, G.isVine (ancGroup_sub hA) hv⟩
  rcases he.ends J hA hD hS with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp [Molecule.ends, h1, h2]
  · simp [Molecule.ends, h1, h2, Sym2.eq_swap]

end WaveTurbulence.FinalCountG3
