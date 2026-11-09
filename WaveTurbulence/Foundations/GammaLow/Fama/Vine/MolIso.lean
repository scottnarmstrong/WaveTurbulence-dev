/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Vine.Iso
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvIso
import Mathlib.Tactic
/-! # `𝒱_γ` is invariant under molecule isomorphisms (packet L5a, item F)

Main's `Stage1.MolIso` (a bijection of atoms and darts commuting with the molecule structure) restricts to an
isomorphism of induced subgraphs (`RedSplice.InducedIso`) on every atom set of the molecule, so T-vines transport by
`tvineIsoInvariant`; the drawn vines by main's `MolIso.isVine_img`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama
open WaveTurbulence.GammaLow.FinalCount

variable {V V' D D' : Type} [DecidableEq V] [Fintype D] [DecidableEq D] [DecidableEq V'] [Fintype D']
  [DecidableEq D']

/-- The induced isomorphism of a molecule isomorphism on an atom set of the molecule. -/
noncomputable def molIsoInduced {M : Molecule V D} {N : Molecule V' D'} (F : Stage1.MolIso M N) (S : Finset V)
    (hS : S ⊆ M.atoms) : RedSplice.InducedIso M N S (F.img S) where
  π := F.e
  inj := F.e.injective.injOn
  img := rfl
  sub := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact (F.atoms_iff v).mpr (hS hv)
  e :=
    { toFun := fun x => ⟨F.d x.1, by
        refine ⟨?_, ?_⟩
        · rw [F.atom_comm]; exact Finset.mem_image_of_mem _ x.2.1
        · rw [F.mate_comm, F.atom_comm]; exact Finset.mem_image_of_mem _ x.2.2⟩
      invFun := fun y => ⟨F.d.symm y.1, by
        have h1 := y.2.1
        have h2 := y.2.2
        refine ⟨?_, ?_⟩
        · obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp h1
          have : F.e (M.atom (F.d.symm y.1)) = N.atom y.1 := by rw [← F.atom_comm, Equiv.apply_symm_apply]
          rw [← hve] at this
          exact F.e.injective this ▸ hv
        · obtain ⟨v, hv, hve⟩ := Finset.mem_image.mp h2
          have : F.e (M.atom (M.mate (F.d.symm y.1))) = N.atom (N.mate y.1) := by
            rw [← F.atom_comm, ← F.mate_comm, Equiv.apply_symm_apply]
          rw [← hve] at this
          exact F.e.injective this ▸ hv⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  atom_comm := fun x => F.atom_comm x.1
  mate_comm := fun x => (F.mate_comm x.1).symm
  out_comm := fun x => F.out_comm x.1

/-- **`𝒱_γ` is invariant under molecule isomorphisms.** -/
theorem isSomeVine_molIso {γ : ℝ} {M : Molecule V D} {N : Molecule V' D'} (F : Stage1.MolIso M N) {S : Finset V}
    {a b : V} (h : Src.IsSomeVine γ M S a b) : Src.IsSomeVine γ N (F.img S) (F.e a) (F.e b) := by
  rcases h with ⟨hγ, h | h | h⟩ | ⟨hγ, X, h⟩
  · exact Or.inl ⟨hγ, Or.inl (F.isVine_img h)⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inl (F.isVine_img h))⟩
  · exact Or.inl ⟨hγ, Or.inr (Or.inr (tvineIsoInvariant (molIsoInduced F S h.1.1) h))⟩
  · exact Or.inr ⟨hγ, X, F.isVine_img h⟩

/-- `σ` is invariant under molecule isomorphisms (on atoms of the molecule). -/
theorem sigma_molIso {M : Molecule V D} {N : Molecule V' D'} (F : Stage1.MolIso M N) {a b : V}
    (ha : a ∈ M.atoms) (hb : b ∈ M.atoms) : N.sigma (F.e a) (F.e b) = M.sigma a b := by
  have hS : ({a, b} : Finset V) ⊆ M.atoms := by
    intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv
    · exact ha
    · rw [Finset.mem_singleton.mp hv]; exact hb
  exact IsoMol.bondsBetween_eq (molIsoInduced F {a, b} hS) (by simp) (by simp)

/-- **DV′ is invariant under molecule isomorphisms.** -/
theorem isDV_molIso {γ : ℝ} {M : Molecule V D} {N : Molecule V' D'} (F : Stage1.MolIso M N) {S : Finset V}
    {a b : V} (h : Src.IsDV γ M S a b) : Src.IsDV γ N (F.img S) (F.e a) (F.e b) := by
  obtain ⟨hσ, A, B, hA, hB, hi, rfl⟩ := h
  have hAB := Src.isBlock_of_isSomeVine hA
  refine ⟨by rw [sigma_molIso F (hAB.1 hAB.2.1) (hAB.1 hAB.2.2.1), hσ], F.img A, F.img B,
    isSomeVine_molIso F hA, isSomeVine_molIso F hB, ?_, F.img_union A B⟩
  rw [← F.img_inter, hi]
  unfold Stage1.MolIso.img
  simp [Finset.image_insert]

end WaveTurbulence.GammaLow.Fama
