/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineVCLocalization
public import WaveTurbulence.Foundations.Molecule.VineBlockGapExists
public import WaveTurbulence.Foundations.Molecule.VineSGSingleVine
import Mathlib.Tactic

/-! # The ordinary subsetvc classification for an outer VC -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET Lemma subsetvc, ordinary inner/outer VC clause. Conservation
localizes the SG inner VC in one actual LG/ZG vine ingredient; all eight
arbitrary-rung classifications then give one/two double bonds or Vine V. -/
theorem SG_VC_in_VC (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {x y a b : V} (hA : IsVC M A x y) (hU : IsVC M U a b) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ U a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsVine .V A x y := by
  obtain ⟨n,T,p,q,hI,hAT⟩ := SG_VC_in_VC_ingredient M hM hA hU hAU L γ η w c κ hκ hc hr hr' houter hsmall
  obtain ⟨_hchain,⟨X,hX⟩,_hTU⟩ := chainIngredient_spec hI
  let k := Molecule.kvec L w κ
  have hk (z : D) : k (M.mate z)=k z := by simp only [k,Molecule.kvec,hκ.1 z]
  have hcons : ∀ v ∈ M.atoms,M.deg v=4 → ∑ z ∈ M.dartsAt v,M.dartSign z • k z=0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc v hv hd)
  have he : groupFlow M T k p=r :=
    ((chainIngredient_flow_eq M hM k hk hcons hI hU.1).1).trans
      (groupGap_eq_flow M (Mole.block_joint_degrees M hU.1).1 hr).symm
  have hgap : M.IsBlockGap L w κ T p (groupFlow M T k p) := block_groupGap_exists M hX.1 k
  have ho : Molecule.gapKind L γ η (groupFlow M T k p)=.LG ∨
      Molecule.gapKind L γ η (groupFlow M T k p)=.ZG := by rwa [he]
  rcases SG_VC_in_single_vine M hM hX hA hAT L γ η w c κ hκ hc hgap hr' ho hsmall with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h.2)

end WaveTurbulence.Vine
