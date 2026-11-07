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

/-- The actual independently constructed successor gap profile. -/
noncomputable def gapProfile (G : Garden w) (σ : Prescription G) : GapProfile w :=
  ⟨(stSt G σ).G, fun _ L γ η _ base _ z => NormalizedSplice.gapValue G σ L γ η base z.1⟩

/-- The entire actual gap profile is constant under a selected unit LF twist. -/
theorem gapProfile_twist (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (hH : Z.target.IsPlain) :
    gapProfile Z.target (transportPrescription Z.iso σ) = gapProfile G σ := by
  apply GapProfile.eq_of_cast (unitSplice_garden_eq Z σ hsel)
  intro d L γ η hL base roots z
  change GenDecoration (stSt Z.target (transportPrescription Z.iso σ)).G d roots 0 at z
  change NormalizedSplice.gapValue Z.target _ L γ η base z.1 =
    NormalizedSplice.gapValue G σ L γ η base (gardenGenCast (unitSplice_garden_eq Z σ hsel) z).1
  refine (NormalizedSplice.unitSplice_actual_gapValue Z σ hsel hH hL γ η base roots z).symm.trans ?_
  apply congrArg (NormalizedSplice.gapValue G σ L γ η base)
  funext n
  have he : unitSpliceNodeEquiv Z σ hsel n = gardenNodeCast (unitSplice_garden_eq Z σ hsel).symm n :=
    Subtype.ext ((unitSpliceNodeEquiv_address Z σ hsel n).trans (gardenNodeCast_val _ n).symm)
  exact (congrArg z.1 he).trans (gardenGenCast_val (unitSplice_garden_eq Z σ hsel) z n).symm

/-- Both actual operation choices preserve the constructed gap profile. -/
theorem operation_gapProfile {p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
    {σ : Prescription A.skeleton} (hA : IsV0Fam A.family σ)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    gapProfile op.output.skeleton (transportPrescription (operationMolIso op) σ) = gapProfile A.skeleton σ := by
  have hp := op.output.plain
  cases op with
  | mk hc he ht hq ε C =>
    cases ε
    · exact congrArg (gapProfile A.skeleton) (transportPrescription_refl σ)
    · exact gapProfile_twist (selectedMemberSite hA i) σ ⟨familyVine A.family i, hA.1 i, rfl⟩ hp

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
