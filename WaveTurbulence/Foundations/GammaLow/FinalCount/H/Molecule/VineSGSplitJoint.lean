/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSGSplitJoint
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainJointNorm
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSGSplitJoint`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # Ordinary SG pieces avoid every junction of an LG/ZG vine chain -/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- Source conservation excludes a split junction from any nested SG VC
in an LG/ZG chain. The two actual gap norms would otherwise coincide. -/
theorem SG_VC_split_joint_absent (M : Molecule V D) (hM : M.IsMolecule)
    {S T A : Finset V} {a b c x y : V} {n : ℕ} (hS : Src.Chain Src.γL M S a b n)
    (hT : Src.IsSomeVine Src.γL M T b c) (hi : S ∩ T={b})
    (hU : M.IsBlock (S ∪ T) a c) (hA : Src.IsVC Src.γL M A x y) (hAU : A ⊆ S ∪ T)
    (L γ η : ℝ) (w : Mom d) (z : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w z κ) (hz : ∀ v ∈ M.atoms,M.deg v=4 → z v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ (S ∪ T) a r)
    (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) : b ∉ A := by
  intro hb
  let k := Molecule.kvec L w κ
  have hk (d : D) : k (M.mate d)=k d := by simp only [k,Molecule.kvec,hκ.1 d]
  have hcons : ∀ v ∈ M.atoms,M.deg v=4 → ∑ d ∈ M.dartsAt v,M.dartSign d • k d=0 :=
    fun v hv hd => (hκ.2 v hv).trans (hz v hv hd)
  have hn := VC_at_chain_split_joint_norm M hM hS hT hi hU hA hAU hb k hk hcons
  have he : ‖r'‖=‖r‖ := by
    rw [groupGap_eq_flow M (Mole.block_joint_degrees M hA.1).1 hr',
      groupGap_eq_flow M (Mole.block_joint_degrees M hU).1 hr]
    exact hn
  have heq := gapKind_eq_of_norm_eq L γ η he
  rw [hsmall] at heq
  rcases houter with ho | ho <;> rw [ho] at heq <;> cases heq

end WaveTurbulence.GammaLow.FinalCount.H
