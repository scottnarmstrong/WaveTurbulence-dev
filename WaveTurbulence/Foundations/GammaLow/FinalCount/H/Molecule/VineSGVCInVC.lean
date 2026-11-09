/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Molecule.VineSGVCInVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSGSingleVine
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineVCLocalization
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Molecule.VineSGVCInVC`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 # The ordinary subsetvc classification for an outer VC 

**Low-range change (L6-HDS).** The adjoint/inner alternative "vine (V)" of main is a T-vine (N3 Cor 1.16′(2), via
`Src.DSInputs`, proved by L3: `Src.DSInputs.holds`); transports of `IsTVine` along local dart
embeddings are L6-HTV's `LocalDartEmbedding.isVine_iffT`. The localization steps are main's, ported.-/
@[expose] public section
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- TARGET Lemma subsetvc, ordinary inner/outer VC clause. Conservation
localizes the SG inner VC in one actual LG/ZG vine ingredient; all eight
arbitrary-rung classifications then give one/two double bonds or Vine V. -/
theorem SG_VC_in_VC (M : Molecule V D) (hM : M.IsMolecule)
    {A U : Finset V} {x y a b : V} (hA : Src.IsVC Src.γL M A x y) (hU : Src.IsVC Src.γL M U a b) (hAU : A ⊆ U)
    (L γ η : ℝ) (w : Mom d) (c : V → Mom d) (κ : D → (Fin d → ℤ))
    (hκ : M.IsDecoration L w c κ) (hc : ∀ v ∈ M.atoms,M.deg v=4 → c v=0)
    {r r' : Mom d} (hr : M.IsBlockGap L w κ U a r) (hr' : M.IsBlockGap L w κ A x r')
    (houter : Molecule.gapKind L γ η r=.LG ∨ Molecule.gapKind L γ η r=.ZG)
    (hsmall : Molecule.gapKind L γ η r'=.SG) :
    DoubleChain M A x y 1 ∨ DoubleChain M A x y 2 ∨ M.IsTVine A x y := by
  obtain ⟨n,T,p,q,hI,hAT⟩ := SG_VC_in_VC_ingredient M hM hA hU hAU L γ η w c κ hκ hc hr hr' houter hsmall
  obtain ⟨_hchain,hX,_hTU⟩ := chainIngredient_spec hI
  let k := Molecule.kvec L w κ
  have hk (z : D) : k (M.mate z)=k z := by simp only [k,Molecule.kvec,hκ.1 z]
  have hcons : ∀ v ∈ M.atoms,M.deg v=4 → ∑ z ∈ M.dartsAt v,M.dartSign z • k z=0 :=
    fun v hv hd => (hκ.2 v hv).trans (hc v hv hd)
  have he : groupFlow M T k p=r :=
    ((chainIngredient_flow_eq M hM k hk hcons hI hU.1).1).trans
      (groupGap_eq_flow M (Mole.block_joint_degrees M hU.1).1 hr).symm
  have hgap : M.IsBlockGap L w κ T p (groupFlow M T k p) := block_groupGap_exists M hX.block k
  have ho : Molecule.gapKind L γ η (groupFlow M T k p)=.LG ∨
      Molecule.gapKind L γ η (groupFlow M T k p)=.ZG := by rwa [he]
  rcases SG_VC_in_single_vine M hM hX hA hAT L γ η w c κ hκ hc hgap hr' ho hsmall with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end WaveTurbulence.GammaLow.FinalCount.H
