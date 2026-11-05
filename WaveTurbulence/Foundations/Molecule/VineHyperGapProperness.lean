/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.Molecule.VineHyperMissingJoint
public import WaveTurbulence.Foundations.Molecule.VineHyperBothJoints
public import WaveTurbulence.Foundations.Molecule.VineLocalDartGaps
public import WaveTurbulence.Foundations.Molecule.VineEraseBondDecoration
public import WaveTurbulence.Foundations.Molecule.VineGapProperness
import Mathlib.Tactic

/-! # Compatible designated hyper-objects of different gap kinds have different atom groups -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET subsetvc, using the owner's compatible-containment reading:
an SG designated hyper-object in an LG/ZG designated hyper-object has a
proper atom subset. Matched mate representatives are identified on actual
darts before comparing the adjoint block gaps. -/
theorem SG_hyperLike_ne_outer (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V}
    (R : HyperLikeRealization M U a b) (P : HyperLikeRealization M A x y) (hcont : P.IsContained R)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : R.IsGap L w κ r) (hr' : P.IsGap L w κ r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) : A ≠ U := by
  intro hAU
  subst A
  obtain ⟨e,he,hVC⟩ := R
  obtain ⟨f,hf,hVCf⟩ := P
  change U ⊆ U ∧ (U=U → f=e ∨ f=M.mate e) at hcont
  change (Mole.eraseBond M e).IsBlockGap L w (fun z => κ z.1) U a r at hr
  change (Mole.eraseBond M f).IsBlockGap L w (fun z => κ z.1) U x r' at hr'
  have hne := ends_distinct_of_pair M e he hVC.1.2.2.2.1
  have hN := eraseBond_isMolecule M hM e hne
  obtain ⟨cN,hκN,hcN⟩ := eraseBond_decoration_exists M hM e hne L w c κ hκ hc
  have absurd (hPB : (Mole.eraseBond M e).IsBlock U x y)
      (hPG : (Mole.eraseBond M e).IsBlockGap L w (fun z => κ z.1) U x r') : False := by
    have heq := same_block_gapKind_eq (Mole.eraseBond M e) hN hVC.1 hPB
      L γ η w cN (fun z => κ z.1) hκN hcN hr hPG
    rw [hsmall] at heq
    rcases houter with ho | ho <;> rw [ho] at heq <;> cases heq
  rcases hcont.2 rfl with hfe | hfe
  · subst f
    exact absurd hVCf.1 hr'
  · subst f
    let F := eraseBond_mate_local_embedding M e U
    exact absurd ((F.isBlock_iff U (Finset.Subset.refl _) x y).mp hVCf.1)
      ((F.blockGap_iff U (Finset.Subset.refl _) L w (fun z => κ z.1) x r').mp hr')

/-- TARGET subsetvc, full hyper-object structural clause for an outer
HV/HVC, with compatible designated containment and the source gap premises. -/
theorem SG_hyperLike_in_hyperLike_adjoint (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {a b x y : V}
    (R : HyperLikeRealization M U a b) (P : HyperLikeRealization M A x y) (hcont : P.IsContained R)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : R.IsGap L w κ r) (hr' : P.IsGap L w κ r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    ∃ f : D,M.ends f=s(x,y) ∧
      (DoubleChain (Mole.eraseBond M f) A x y 2 ∨ (Mole.eraseBond M f).IsVine .V A x y) := by
  have hU := hyperLike_iff_realization.mpr ⟨R⟩
  have hA := hyperLike_iff_realization.mpr ⟨P⟩
  have hproper := SG_hyperLike_ne_outer M hM R P hcont L γ η w c κ hκ hc hr hr' houter hsmall
  have hmiss : ¬(a ∈ A ∧ b ∈ A) := by
    intro hab
    exact hproper (hyperBlock_in_hyperLike_both_joints_eq M hU
      ⟨P.added,P.ends_eq,P.adjoint.1⟩ hcont.1 hab.1 hab.2)
  exact hyperLike_in_hyperLike_missing_joint_adjoint M hM hU hA hcont.1 hmiss

end WaveTurbulence.Vine
