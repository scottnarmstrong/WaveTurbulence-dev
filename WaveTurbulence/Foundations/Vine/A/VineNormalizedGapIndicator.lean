/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedGroupGap
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRepGap
public import WaveTurbulence.Foundations.Vine.A.VineMolDecoration
public import WaveTurbulence.Foundations.Vine.A.VineCoarseWordBatch
public import WaveTurbulence.Foundations.Vine.A.VineSpliceDecorationLift
/-! Complete actual successor gap indicators on the spliced decoration carrier. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
namespace WaveTurbulence.VineA.NormalizedSplice
open Finset Stage1 RedSplice LGSpine Mole
variable {w d : ℕ} {G : Garden w}

/-- The literal product for a supplied family of local gap entries. -/
noncomputable def gapProduct (H : Garden w)
    (entries : (v : GBranch H.tree) → Option (LocalGapSpecification H v))
    (L γ η : ℝ) (base : Mom d) (z : GNode H.tree → (Fin d → ℤ)) : ℝ := by
  classical
  exact ∏ v : GBranch H.tree, match entries v with
    | none => 1
    | some q => if Molecule.gapKind L γ η
        (base + latticePoint L (bondIndex H z q.first) -
          (base + latticePoint L (bondIndex H z q.second))) = q.kind then 1 else 0

/-- This product is precisely the gap factor in the literal source kernel. -/
theorem indicator_eq_gapProduct (H : Garden w) (D : SplicedKernelData H d)
    (L γ η : ℝ) (base : Mom d) (z : GNode H.tree → (Fin d → ℤ)) :
    splicedGapIndicator H D L γ η base z = gapProduct H D.gapSpecification L γ η base z := rfl

/-- The actual successor gap product, with its independently constructed entries. -/
noncomputable def gapValue (G : Garden w) (σ : Prescription G) (L γ η : ℝ) (base : Mom d)
    (z : GNode (stSt G σ).G.tree → (Fin d → ℤ)) : ℝ :=
  gapProduct (stSt G σ).G (gapSpecification G σ) L γ η base z

/-- B1b-3 (Mk-general form of `gapValue`): the gap product with the entries `gapSpecificationMk G σ Mk`. -/
noncomputable def gapValueMk (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) (L γ η : ℝ) (base : Mom d)
    (z : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ)) : ℝ :=
  gapProduct (stSt G σ Mk).G (gapSpecificationMk G σ Mk) L γ η base z

/-- B1b-3 (Mk-general form of `gapValue_eq_indicator`). -/
theorem gapValue_eq_indicatorMk (σ : Prescription G) {Mk : Set (CLVine G)} (D : SplicedKernelData (stSt G σ Mk).G d)
    (hD : D.gapSpecification = gapSpecificationMk G σ Mk) (L γ η : ℝ) (base : Mom d)
    (z : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ)) :
    gapValueMk G σ Mk L γ η base z = splicedGapIndicator (stSt G σ Mk).G D L γ η base z := by
  rw [indicator_eq_gapProduct, hD]
  rfl

open scoped Classical in
/-- B1b-3: **the exact statement of B2c's `VineA.NormalizedSplice.splicedGapIndicator_eq_selOfMk`** (branch
w/mk-subpro, ruling R171), at one garden, prescription and marking. A HYPOTHESIS here, discharged at the joint
landing by `fun … => splicedGapIndicator_eq_selOfMk (Mole.garden_isMolecule G) σ …`. -/
def SplicedGapIndicatorSelOfAt (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) : Prop :=
  ∀ {d : ℕ} (L γ η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (_hκ : G.molecule.IsDecoration L base c (bondIndex G z))
    (_hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (_hlab : ∀ y, bondIndex (stSt G σ Mk).G zsb y = bondIndex G z ((stSt G σ Mk).M.od y))
    (D : SplicedKernelData (stSt G σ Mk).G d) (_hD : D.gapSpecification = gapSpecificationMk G σ Mk),
    splicedGapIndicator (stSt G σ Mk).G D L γ η base zsb =
      if selOf (GroupPrescription.ofPrescription σ) L γ η base z then 1 else 0

/-- B1b-3: at the empty marking the hypothesis is main's `splicedGapIndicator_eq_selOf`. -/
theorem splicedGapIndicatorSelOfAt_empty (G : Garden w) (σ : Prescription G) : SplicedGapIndicatorSelOfAt G σ ∅ :=
  fun L γ η base c z hκ hc0 zsb hlab D hD =>
    splicedGapIndicator_eq_selOf (Mole.garden_isMolecule G) σ L γ η base c z hκ hc0 zsb hlab D hD

open scoped Classical in
/-- B1b-3: the dart-label form of the same identity (the Mk-general form of main's `gapValue_eq_selDarts`), at one
garden, prescription and marking. B2c's per-group lemma `gapSpecificationMk_indicator_iff` is already dart-label,
and B2c's proof of `splicedGapIndicator_eq_selOfMk` proves this verbatim with `bondIndex G z` replaced by `κ`. It is
needed for twist invariance (`unitSplice_actual_gapValueMk`), where the source labels are the pull-back
`κ ∘ Z.iso.d` of a target decoration (no node decoration of the source is available). A HYPOTHESIS here. -/
def GapValueSelDartsAt (G : Garden w) (σ : Prescription G) (Mk : Set (CLVine G)) : Prop :=
  ∀ {d : ℕ} (L γ η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (_hκ : G.molecule.IsDecoration L base c κ)
    (_hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt G σ Mk).G.tree → (Fin d → ℤ))
    (_hlab : ∀ y, bondIndex (stSt G σ Mk).G zsb y = κ ((stSt G σ Mk).M.od y)),
    gapValueMk G σ Mk L γ η base zsb = if selDarts (GroupPrescription.ofPrescription σ) L γ η base κ then 1 else 0

/-- B1b-3: the dart-label form implies B2c's exact statement (take `κ = bondIndex G z`). -/
theorem splicedGapIndicatorSelOfAt_of_selDarts {G : Garden w} {σ : Prescription G} {Mk : Set (CLVine G)}
    (h : GapValueSelDartsAt G σ Mk) : SplicedGapIndicatorSelOfAt G σ Mk := by
  intro d L γ η base c z hκ hc0 zsb hlab D hD
  rw [← gapValue_eq_indicatorMk σ D hD]
  exact h L γ η base c (bondIndex G z) hκ hc0 zsb hlab

/-- The literal kernel's gap indicator is this product when it carries the constructed entries. -/
theorem gapValue_eq_indicator (σ : Prescription G) (D : SplicedKernelData (stSt G σ).G d)
    (hD : D.gapSpecification = gapSpecification G σ) (L γ η : ℝ) (base : Mom d)
    (z : GNode (stSt G σ).G.tree → (Fin d → ℤ)) :
    gapValue G σ L γ η base z = splicedGapIndicator (stSt G σ).G D L γ η base z := by
  rw [indicator_eq_gapProduct, hD]
  rfl

open scoped Classical in
/-- The exact gap product is the restriction on original conserving dart labels. -/
theorem gapValue_eq_selDarts (hM : G.molecule.IsMolecule) (σ : Prescription G) {d : ℕ}
    (L γ η : ℝ) (base : Mom d) (c : GBranch G.tree → Mom d) (κ : GardenDart G → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (κ))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0)
    (zsb : GNode (stSt G σ).G.tree → (Fin d → ℤ))
    (hlab : ∀ y, bondIndex (stSt G σ).G zsb y = κ ((stSt G σ).M.od y))
    :
    gapValue G σ L γ η base zsb =
      if selDarts (GroupPrescription.ofPrescription σ) L γ η base κ then 1 else 0 := by
  classical
  set Q : GBranch (stSt G σ).G.tree → Prop := fun v => ∀ q, gapSpecification G σ v = some q →
        Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (stSt G σ).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt G σ).G zsb q.second))) = q.kind with hQ
  have hf : gapValue G σ L γ η base zsb = if ∀ v, Q v then 1 else 0 := by
    unfold gapValue gapProduct
    have hb := Finset.prod_boole (M₀ := ℝ) (s := (Finset.univ : Finset (GBranch (stSt G σ).G.tree))) (p := fun v => Q v)
    simp only [Finset.mem_univ, true_implies] at hb
    rw [← hb]
    refine Finset.prod_congr rfl fun v _ => ?_
    split
    next heq =>
      have hQv : Q v := fun q hq => by rw [heq] at hq; cases hq
      simp [hQv]
    next q heq =>
      have hiff : Q v ↔ Molecule.gapKind L γ η ((base + latticePoint L (bondIndex (stSt G σ).G zsb q.first)) -
          (base + latticePoint L (bondIndex (stSt G σ).G zsb q.second))) = q.kind := by
        constructor
        · intro h; exact h q heq
        · intro h q' hq'; rw [heq] at hq'; cases hq'; exact h
      simp only [hiff]
  rw [hf]
  have key : (∀ v, Q v) ↔ selDarts (GroupPrescription.ofPrescription σ) L γ η base κ := by
    constructor
    · intro hall
      unfold selDarts
      intro S
      obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecification_indicator_iff hM σ S.2 L γ η base c _ hκ hc0
        (bondIndex (stSt G σ).G zsb) hlab
      obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (κ) hO
      have := (hind k hk).mp (hall _ e he)
      exact hgk.trans this
    · intro hsel v q hq
      have hsome : (gapSpecification G σ v).isSome := by rw [hq]; rfl
      obtain ⟨S, hS, hSv⟩ := (gapSpecification_isSome_iff hM σ v).mp hsome
      obtain ⟨a, O, ha, hO, e, he, hind⟩ := gapSpecification_indicator_iff hM σ hS L γ η base c _ hκ hc0
        (bondIndex (stSt G σ).G zsb) hlab
      have hat : groupAtom G σ S = some ((stSt G σ).M.pi (stSt G σ).hcls a) := by
        unfold groupAtom; rw [ha]; rfl
      rw [hat] at hSv
      cases hSv
      rw [he] at hq
      cases hq
      obtain ⟨k, hk, hgk⟩ := exists_groupGapKind_eq (G := G) L γ η base (κ) hO
      exact (hind k hk).mpr (hgk.symm.trans (hsel ⟨S, hS⟩))
  simp only [key]

/-- B1b-3: at the empty marking the dart-label hypothesis is main's `gapValue_eq_selDarts`. -/
theorem gapValueSelDartsAt_empty (G : Garden w) (σ : Prescription G) : GapValueSelDartsAt G σ ∅ :=
  fun L γ η base c κ hκ hc0 zsb hlab =>
    gapValue_eq_selDarts (Mole.garden_isMolecule G) σ L γ η base c κ hκ hc0 zsb hlab

/-- B1b-3 (Mk-general form of `unitSplice_actual_gapValue`): twist invariance of the gap product at markings carried
by the twist, given the dart-label gap identity at the source and target (`GapValueSelDartsAt`, B2c). -/
theorem unitSplice_actual_gapValueMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (hH : Z.target.IsPlain)
    (hgS : GapValueSelDartsAt G σ Mk) (hgT : GapValueSelDartsAt Z.target (transportPrescription Z.iso σ) Mk')
    {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))
    (z : GenDecoration (stSt Z.target (transportPrescription Z.iso σ) Mk').G d roots 0) :
    gapValueMk G σ Mk L γ η base (z.1 ∘ unitSpliceNodeEquivMk Z σ hT hsel) =
      gapValueMk Z.target (transportPrescription Z.iso σ) Mk' L γ η base z.1 := by
  classical
  obtain ⟨κ, hlab⟩ := splice_labels_extendMk hH (transportPrescription Z.iso σ) hL base roots z
  let c := gardenSource Z.target hH (fun i => base + latticePoint L (roots i))
  have hκ := spliced_molecule_decoration Z.target hH hL base roots κ
  have hc0 : ∀ v ∈ Z.target.molecule.atoms, Z.target.molecule.deg v = 4 → c v = 0 :=
    fun v _ hv => gardenSource_eq_zero_of_deg_four Z.target hH _ v hv
  have hpull := molIso_decoration_pull Z.iso L base c (bondIndex Z.target κ.1) hκ
  have hzero : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → (c ∘ Z.iso.e) v = 0 := by
    intro v hv hd
    exact hc0 (Z.iso.e v) ((Z.iso.atoms_iff v).mpr hv) ((Z.iso.deg_img v).trans hd)
  have hsLab : ∀ y, bondIndex (stSt G σ Mk).G (z.1 ∘ unitSpliceNodeEquivMk Z σ hT hsel) y =
      (bondIndex Z.target κ.1 ∘ Z.iso.d) ((stSt G σ Mk).M.od y) := by
    intro y
    exact (unitSplice_bondIndexMk Z σ hT hsel z.1 y).trans
      ((hlab _).trans (congrArg (bondIndex Z.target κ.1) (unitSpliceMolIso_dart_namesMk Z σ hT hsel y)))
  rw [hgS L γ η base _ _ hpull hzero _ hsLab, hgT L γ η base c _ hκ hc0 _ hlab]
  obtain ⟨u, hu, ha⟩ := hsel
  have hc := selDarts_twist Z ⟨u, mem_allSG hu.1, ha⟩ (Represents.GroupPrescription.ofPrescription σ)
    L γ η base c (bondIndex Z.target κ.1) hκ hc0
  exact if_congr hc.symm rfl rfl

end WaveTurbulence.VineA.NormalizedSplice
