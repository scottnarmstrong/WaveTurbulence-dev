/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedGapIndicator
public import WaveTurbulence.Foundations.Vine.A.VineBatchOrderedNormalization
/-! The literal normalized garden with its entire actual gap functional. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Stage1 RedSplice LGSpine LFTwist
variable {w d : ℕ} {G H : Garden w}

def gardenNodeCast (h : H = G) (n : GNode H.tree) : GNode G.tree := h ▸ n

theorem gardenNodeCast_val (h : H = G) (n : GNode H.tree) : (gardenNodeCast h n).1 = n.1 := by
  cases h; rfl

def gardenGenCast (h : H = G) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration H d roots 0) : GenDecoration G d roots 0 := h ▸ z

theorem gardenGenCast_val (h : H = G) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration H d roots 0) (n : GNode G.tree) :
    (gardenGenCast h z).1 n = z.1 (gardenNodeCast h.symm n) := by cases h; rfl

/-- The full gap functional, on all genuine spliced decorations and nonzero lattice scales. -/
structure GapProfile (w : ℕ) where
  garden : Garden w
  value : ∀ (d : ℕ) (L _γ _η : ℝ), L ≠ 0 → (base : Mom d) → (roots : Fin w → (Fin d → ℤ)) →
    GenDecoration garden d roots 0 → ℝ

/-- Extensional equality accounts only for the cast forced by literal garden equality. -/
theorem GapProfile.eq_of_cast {P Q : GapProfile w} (h : Q.garden = P.garden)
    (hv : ∀ d L γ η hL base roots z, Q.value d L γ η hL base roots z =
      P.value d L γ η hL base roots (gardenGenCast h z)) : Q = P := by
  rcases P with ⟨G, f⟩
  rcases Q with ⟨H, g⟩
  change H = G at h
  subst H
  congr
  funext d L γ η hL base roots z
  exact hv d L γ η hL base roots z

/-- B1b-3: B2c's dart-label gap identity at every garden of width `w`, prescription and marking (needed along
batches, whose intermediate markings are arbitrary). -/
def GapValueSelDartsMk (w : ℕ) : Prop :=
  ∀ (H : Garden w) (τ : Prescription H) (M : Set (CLVine H)), NormalizedSplice.GapValueSelDartsAt H τ M

/-- B1b-3 (Mk-general form of `gapProfile`). -/
noncomputable def gapProfileMk (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) : GapProfile w :=
  ⟨(stSt G σ Mk).G, fun _ L γ η _ base _ z => NormalizedSplice.gapValueMk G σ Mk L γ η base z.1⟩

/-- B1b-3 (Mk-general form of `gapProfile_twist`). -/
theorem gapProfile_twistMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (hH : Z.target.IsPlain)
    (hgS : NormalizedSplice.GapValueSelDartsAt G σ Mk)
    (hgT : NormalizedSplice.GapValueSelDartsAt Z.target (transportPrescription Z.iso σ) Mk') :
    gapProfileMk Z.target (transportPrescription Z.iso σ) Mk' = gapProfileMk G σ Mk := by
  apply GapProfile.eq_of_cast (unitSplice_garden_eqMk Z σ hT hsel)
  intro d L γ η hL base roots z
  change GenDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G d roots 0 at z
  change NormalizedSplice.gapValueMk Z.target _ Mk' L γ η base z.1 =
    NormalizedSplice.gapValueMk G σ Mk L γ η base (gardenGenCast (unitSplice_garden_eqMk Z σ hT hsel) z).1
  refine (NormalizedSplice.unitSplice_actual_gapValueMk Z σ hT hsel hH hgS hgT hL γ η base roots z).symm.trans ?_
  apply congrArg (NormalizedSplice.gapValueMk G σ Mk L γ η base)
  funext n
  have he : unitSpliceNodeEquivMk Z σ hT hsel n = gardenNodeCast (unitSplice_garden_eqMk Z σ hT hsel).symm n :=
    Subtype.ext ((unitSpliceNodeEquiv_addressMk Z σ hT hsel n).trans (gardenNodeCast_val _ n).symm)
  exact (congrArg z.1 he).trans (gardenGenCast_val (unitSplice_garden_eqMk Z σ hT hsel) z n).symm

/-- B1b-3 (Mk-general form of `operation_gapProfile`). -/
theorem operation_gapProfileMk {p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} {Mk : Set (CLVine A.skeleton)} (hA : IsV0Fam A.family σ Mk)
    (op : FamilyOperation (p := p) (kind := kind) A i)
    {Mk' : Set (CLVine op.output.skeleton)} (hT : Stage1Mk.MarkTransported (operationMolIso op) Mk Mk')
    (hgS : NormalizedSplice.GapValueSelDartsAt A.skeleton σ Mk)
    (hgT : NormalizedSplice.GapValueSelDartsAt op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk') :
    gapProfileMk op.output.skeleton (transportPrescription (operationMolIso op) σ) Mk' = gapProfileMk A.skeleton σ Mk := by
  have hp := op.output.plain
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · obtain rfl : Mk = Mk' := Stage1Mk.markTransported_refl_eq hT
      exact congrArg (fun τ => gapProfileMk A.skeleton τ Mk) (transportPrescription_refl σ)
    · exact gapProfile_twistMk (selectedMemberSite hA i) σ hT ⟨familyVine A.family i, hA.1 i, rfl⟩ hp hgS hgT

/-- B1b-3 (Mk-general form of `BatchIso.gapProfile`): the gap profile at markings carried by the batch, given B2c's
dart-label gap identity everywhere (`GapValueSelDartsMk w`). -/
theorem BatchIso.gapProfileMk {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) {Mk : Set (CLVine A.skeleton)}
    {Mk' : Set (CLVine B.skeleton)} (hT : Stage1Mk.MarkTransported F Mk Mk') (hA : IsV0Fam A.family σ Mk)
    (hg : GapValueSelDartsMk w) :
    VineA.gapProfileMk B.skeleton (transportPrescription F σ) Mk' = VineA.gapProfileMk A.skeleton σ Mk := by
  induction h with
  | nil =>
    obtain rfl := Stage1Mk.markTransported_refl_eq hT
    exact congrArg (fun τ => VineA.gapProfileMk _ τ Mk) (transportPrescription_refl σ)
  | skip _ _ ih => exact ih σ hT hA
  | @apply L A B i op F h ih =>
    obtain ⟨h1, h2⟩ := Stage1Mk.markTransported_split (operationMolIso op) F hT
    have hb := ih _ h2 (isV0Fam_operationMk hA op h1)
    rw [transportPrescription_trans] at hb
    exact hb.trans (operation_gapProfileMk hA op h1 (hg _ _ _) (hg _ _ _))

/-- The actual independently constructed successor gap profile. -/
noncomputable def gapProfile (G : Garden w) (σ : Prescription G) : GapProfile w :=
  ⟨(stSt G σ).G, fun _ L γ η _ base _ z => NormalizedSplice.gapValue G σ L γ η base z.1⟩

/-- Both actual operation choices preserve the constructed gap profile. -/
theorem operation_gapProfile {p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    gapProfile op.output.skeleton (transportPrescription (operationMolIso op) σ) = gapProfile A.skeleton σ :=
  operation_gapProfileMk hA op (Stage1Mk.markTransported_empty _)
    (NormalizedSplice.gapValueSelDartsAt_empty _ σ) (NormalizedSplice.gapValueSelDartsAt_empty _ _)

/-- Every actual fine batch preserves the complete independently chosen gap product. -/
theorem BatchIso.gapProfile {p : ℕ} {kind : Bool} {ι : Type*} {L : List ι}
    {A B : FamilyReconstruction w ι} {F : MolIso A.skeleton.molecule B.skeleton.molecule}
    (h : BatchIso p kind L A B F) (σ : Prescription A.skeleton) (hA : IsV0Fam A.family σ) :
    VineA.gapProfile B.skeleton (transportPrescription F σ) = VineA.gapProfile A.skeleton σ := by
  induction h with
  | nil => exact congrArg (VineA.gapProfile _) (transportPrescription_refl σ)
  | skip _ _ ih => exact ih σ hA
  | apply op _ ih =>
    have hb := ih _ (isV0Fam_operation hA op)
    rw [transportPrescription_trans] at hb
    exact hb.trans (operation_gapProfile hA op)

end WaveTurbulence.VineA
