/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineHyperDesignation
public import WaveTurbulence.Foundations.Molecule.VineLocalDartGaps
public import WaveTurbulence.Foundations.Molecule.VineEraseBondDecoration
/-! Hyper gap kinds ignore joint order and the orientation of the same deleted
bond. Actual HVC uniqueness can supply this identification; arbitrary HV choices cannot be assumed equal. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 LGSpine.SourceVine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {d : ℕ}

/-- Ordered joints of one fixed designated adjoint give the same gap kind. -/
theorem erased_block_gapKind_joint_iff (hM : M.IsMolecule) {S : Finset V} {a b c e : V}
    (f : D) (hf : M.ends f = s(a, b)) (hB : (Mole.eraseBond M f).IsBlock S a b)
    (hC : (Mole.eraseBond M f).IsBlock S c e) (scale γ η : ℝ) (base : Mom d)
    (charge : V → Mom d) (κ : D → (Fin d → ℤ)) (hκ : M.IsDecoration scale base charge κ)
    (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → charge v = 0) (kind : Molecule.GapKind) :
    (∃ r, (Mole.eraseBond M f).IsBlockGap scale base (fun z => κ z.1) S a r ∧
      Molecule.gapKind scale γ η r = kind) ↔
    ∃ r, (Mole.eraseBond M f).IsBlockGap scale base (fun z => κ z.1) S c r ∧
      Molecule.gapKind scale γ η r = kind := by
  have hne := Vine.ends_distinct_of_pair M f hf hB.2.2.2.1
  have hN := Vine.eraseBond_isMolecule M hM f hne
  obtain ⟨cN, hκN, hcN⟩ := Vine.eraseBond_decoration_exists M hM f hne scale base charge κ hκ hc0
  exact block_gapKind_joint_iff hN hB hC scale γ η base cN (fun z => κ z.1) hκN hcN kind

/-- The same actual deleted bond, up to mates, suffices for hyper gap-kind independence. -/
theorem hyper_gapKind_iff_of_same_bond (hM : M.IsMolecule) {S : Finset V} {a b c e : V}
    (P : HyperLikeRealization M S a b) (Q : HyperLikeRealization M S c e)
    (hbond : P.added = Q.added ∨ P.added = M.mate Q.added)
    (scale γ η : ℝ) (base : Mom d) (charge : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration scale base charge κ) (hc0 : ∀ v ∈ M.atoms, M.deg v = 4 → charge v = 0)
    (kind : Molecule.GapKind) :
    (∃ r, P.IsGap scale base κ r ∧ Molecule.gapKind scale γ η r = kind) ↔
      ∃ r, Q.IsGap scale base κ r ∧ Molecule.gapKind scale γ η r = kind := by
  rcases P with ⟨f, hf, hF⟩
  rcases Q with ⟨g, hg, hG⟩
  change f = g ∨ f = M.mate g at hbond
  rcases hbond with heq | heq
  · subst g
    exact erased_block_gapKind_joint_iff hM f hf hF.1 hG.1 scale γ η base charge κ hκ hc0 kind
  · have heq' : g = M.mate f := by
      have hh := congrArg M.mate heq
      rw [M.mate_mate] at hh
      exact hh.symm
    subst g
    let I := Vine.eraseBond_mate_local_embedding M f S
    have hC : (Mole.eraseBond M f).IsBlock S c e := (I.isBlock_iff S (Subset.refl S) c e).mp hG.1
    have he := erased_block_gapKind_joint_iff hM f hf hF.1 hC scale γ η base charge κ hκ hc0 kind
    have hi (r : Mom d) :
        (Mole.eraseBond M (M.mate f)).IsBlockGap scale base (fun z => κ z.1) S c r ↔
          (Mole.eraseBond M f).IsBlockGap scale base (fun z => κ z.1) S c r :=
      I.blockGap_iff S (Subset.refl S) scale base (fun z => κ z.1) c r
    exact he.trans ((exists_congr fun r => and_congr (hi r) Iff.rfl).symm)

end WaveTurbulence.VineA
