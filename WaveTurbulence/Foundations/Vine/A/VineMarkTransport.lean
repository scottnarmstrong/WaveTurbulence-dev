/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineBatchIso
/-! B1b (R11, ruling R166): transport of a marked vine set along an actual molecule isomorphism.

`MarkTransported F M M'` (B0 probe, verbatim; the world's `Flower.MkDefs.MarkTransported` has the same body) says that
`F` carries the marked set `M` of the source skeleton onto the marked set `M'` of the target, vine by vine through the
atom map.  The twist-side transport lemmas (`vinesV0_imageMk`, `isV0Fam_twistMk`, `BatchIso.selectedMk`,
`fine_outputs_rebaseMk`) take it as a hypothesis; the world supplies it through `MarkInvariantBatchV` (Lemma 2⁺).
A composite transport splits through the intermediate skeleton (`markTransported_split`), with the intermediate marked
set `midMark`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Stage1Mk
open WaveTurbulence.Stage1 WaveTurbulence.VineA

variable {w : ℕ}

/-- Transport of a marked set along a molecule isomorphism of skeletons. -/
def MarkTransported {S S' : Garden w} (F : Stage1.MolIso S.molecule S'.molecule)
    (M : Set (Stage1.CLVine S)) (M' : Set (Stage1.CLVine S')) : Prop :=
  ∀ (c : Stage1.CLVine S) (c' : Stage1.CLVine S'), c'.atoms = F.img c.atoms → (c ∈ M ↔ c' ∈ M')

/-- Along the identity a marked set is transported only onto itself. -/
theorem markTransported_refl_eq {S : Garden w} {M M' : Set (CLVine S)}
    (h : MarkTransported (molIsoRefl S) M M') : M = M' :=
  Set.ext fun c => h c c (by
    change c.atoms = c.atoms.image (Equiv.refl _)
    rw [Equiv.coe_refl, Finset.image_id])

/-- B1b-2: the empty marking is carried by every isomorphism (the `∅`-instance of the twist-side `…Mk` lemmas). -/
theorem markTransported_empty {S S' : Garden w} (F : Stage1.MolIso S.molecule S'.molecule) :
    MarkTransported F (∅ : Set (CLVine S)) (∅ : Set (CLVine S')) := fun _ _ _ => Iff.rfl

theorem molIsoTrans_img {S S' S'' : Garden w} (F : MolIso S.molecule S'.molecule)
    (J : MolIso S'.molecule S''.molecule) (U : Finset (GBranch S.tree)) :
    (molIsoTrans F J).img U = J.img (F.img U) := by
  unfold MolIso.img
  rw [Finset.image_image]
  rfl

/-- The intermediate marked set of a composite transport: the pull-back of `M''` along `J`, together with the push-forward
of `M` along `F`. -/
def midMark {S S' S'' : Garden w} (F : MolIso S.molecule S'.molecule) (J : MolIso S'.molecule S''.molecule)
    (M : Set (CLVine S)) (M'' : Set (CLVine S'')) : Set (CLVine S') :=
  {c' | (∃ c'' ∈ M'', c''.atoms = J.img c'.atoms) ∨ ∃ c ∈ M, c'.atoms = F.img c.atoms}

/-- A transport along a composite splits through `midMark`. -/
theorem markTransported_split {S S' S'' : Garden w} (F : MolIso S.molecule S'.molecule)
    (J : MolIso S'.molecule S''.molecule) {M : Set (CLVine S)} {M'' : Set (CLVine S'')}
    (h : MarkTransported (molIsoTrans F J) M M'') :
    MarkTransported F M (midMark F J M M'') ∧ MarkTransported J (midMark F J M M'') M'' := by
  constructor
  · intro c c' hc
    constructor
    · intro hm
      exact Or.inr ⟨c, hm, hc⟩
    · rintro (⟨c'', hm'', he⟩ | ⟨d, hd, he⟩)
      · exact (h c c'' (by rw [he, hc, molIsoTrans_img])).mpr hm''
      · have := F.img_injective (he.symm.trans hc)
        rw [← clVine_eq_of_atoms this]
        exact hd
  · intro c' c'' hc
    constructor
    · rintro (⟨e, he, hea⟩ | ⟨d, hd, hda⟩)
      · rw [← clVine_eq_of_atoms (hea.trans hc.symm)]
        exact he
      · exact (h d c'' (by rw [hc, hda, molIsoTrans_img])).mp hd
    · intro hm
      exact Or.inl ⟨c'', hm, hc⟩

end WaveTurbulence.Stage1Mk
