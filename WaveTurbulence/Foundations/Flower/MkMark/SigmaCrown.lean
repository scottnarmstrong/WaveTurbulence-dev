/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.SigmaGroup
public import WaveTurbulence.Foundations.Molecule.BlockSlots
public import WaveTurbulence.Foundations.Molecule.GardenPositionReconstruction
public import WaveTurbulence.Foundations.Spine.GardenPos
public import WaveTurbulence.Foundations.Spine.SplicedMoleculeDecoration
public import WaveTurbulence.Foundations.Spine.KernelCosetDecoration
public import WaveTurbulence.Foundations.Spine.GardenDegreeFourSource
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLIngredientGaps

/-! # B2b-3 MK-MARK σ-bridge: the crown gap of a `𝒱₀(σ)` vine is SG

* **(A) the dart/node dictionary at a CL lower joint** (`lower_blockGap_eq`, `crown_eq_blockGap`): at the lower joint
  `b` of a CL block `U` the two darts internal to `U` sit at the positions `0` (the parent bond, label `z b`) and
  `kept.succ` (the kept child, label `z (b.child kept)`) — main `CLSpliceSlots.lower`, `zero_mem_internalPositions`,
  `atom_position_injective`, `bondIndex_position`. So every block gap of `U` at `b` is `±(z b − z kept)/L`, and by
  main `cl_lower_gap` it is `±` the crown gap `k(b.child pos) − k(b.child neg)` of any coset decoration
  `k = k₀ + z/L`.
* `crown_gapKind_of_ingredient`: if the group `S ∈ 𝒞` has gap kind `kind` and `U` is (the atom set of) an ingredient
  of `S`, the crown gap at the lower joint of any CL block presentation of `U` has kind `kind`.
* **The σ-bridge** (`crown_gapKind_SG_of_selDarts`, `crown_gapKind_SG_of_vinesV0`, `crown_gap_le_of_vinesV0`): under
  main's σ-restriction (`selDarts`/`selOf` with labels `bondIndex G z`), every `𝕍 ∈ vinesV0 G σ` has an SG crown gap:
  `0 < ‖k(u₂₁) − k(u₂₂)‖ ≤ L^{-γ+η}`. The molecule decoration is produced from the garden decoration for plain
  gardens (`moleculeDecoration_bondIndex`, main `moleculeDecoration_of_garden`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical

namespace WaveTurbulence.Flower.MkMark
open WaveTurbulence WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine

variable {w : ℕ} {G : Garden w}

/-! ## (A) the dictionary at a CL lower joint -/

/-- A dart internal to `U` at the lower joint `b` sits at position `0` (label `z b`) or at the kept child. -/
theorem lower_dart_cases {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : RegRed.CLRegionData G U a b)
    {d : ℕ} (z : GNode G.tree → (Fin d → ℤ)) (x : GardenDart G) (hx : G.molecule.atom x = b)
    (hg : G.molecule.InGroup U x) :
    (LGSpine.bondIndex G z x = z b.toNode ∧ Mole.dartPosition G x = 0) ∨
      (LGSpine.bondIndex G z x = z (b.child R.kept) ∧ Mole.dartPosition G x = R.kept.succ) := by
  have hm : Mole.dartPosition G x ∈ Mole.internalPositions G U b :=
    (Mole.mem_internalPositions G).mpr ⟨x, hx, hg, rfl⟩
  rw [LadderDecay.bondIndex_position z x]
  by_cases h0 : Mole.dartPosition G x = 0
  · left
    rw [dite_eq_left h0, hx]
    exact ⟨rfl, h0⟩
  · right
    rw [dite_eq_right h0, hx]
    have hk : (Mole.dartPosition G x).pred h0 = R.kept :=
      (R.toCLSpliceSlots.lower _).mp (by rw [Fin.succ_pred]; exact hm)
    refine ⟨by rw [hk], ?_⟩
    rw [← hk, Fin.succ_pred]

/-- **(A).** Every block gap of `U` at its CL lower joint `b` is `±(z b − z (b.child kept))/L`. -/
theorem lower_blockGap_eq {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : RegRed.CLRegionData G U a b)
    {d : ℕ} (L : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) {r : Mom d}
    (hr : G.molecule.IsBlockGap L base (LGSpine.bondIndex G z) U b r) :
    r = latticePoint L (z b.toNode) - latticePoint L (z (b.child R.kept)) ∨
      r = -(latticePoint L (z b.toNode) - latticePoint L (z (b.child R.kept))) := by
  obtain ⟨x₁, x₂, h1, h2, hg1, hg2, ho1, ho2, rfl⟩ := hr
  have hne : x₁ ≠ x₂ := by
    rintro rfl
    rw [ho1] at ho2
    exact Bool.noConfusion ho2
  have hpne : Mole.dartPosition G x₁ ≠ Mole.dartPosition G x₂ := fun h =>
    hne (Mole.atom_position_injective G (Prod.ext (h1.trans h2.symm) h))
  unfold Molecule.gapAt Molecule.kvec
  rcases lower_dart_cases R z x₁ h1 hg1 with ⟨e1, p1⟩ | ⟨e1, p1⟩ <;>
    rcases lower_dart_cases R z x₂ h2 hg2 with ⟨e2, p2⟩ | ⟨e2, p2⟩
  · exact absurd (p1.trans p2.symm) hpne
  · left
    rw [e1, e2]
    abel
  · right
    rw [e1, e2]
    abel
  · exact absurd (p1.trans p2.symm) hpne

/-- The crown gap of a coset decoration `k = k₀ + z/L` at a CL lower joint. -/
theorem crown_coset {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : RegRed.CLRegionData G U a b)
    {d : ℕ} (L : ℝ) (k₀ : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) :
    cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative) =
      ((G.sign b.toNode : ℤ) : ℝ) • (latticePoint L (z b.toNode) - latticePoint L (z (b.child R.kept))) := by
  rw [← RegRed.cl_lower_gap R (cosetDecoration G L k₀ z) (LGSpine.isDecoration_cosetDecoration G L k₀ z hz)]
  unfold cosetDecoration
  congr 1
  abel

theorem sign_smul_eq_or_neg {d : ℕ} (s : ℤˣ) (v : Mom d) : ((s : ℤ) : ℝ) • v = v ∨ ((s : ℤ) : ℝ) • v = -v := by
  rcases Int.units_eq_one_or s with h | h
  · left
    rw [h]
    simp
  · right
    rw [h]
    simp

/-- **(A), crown form.** The crown gap of a coset decoration at the CL lower joint `b` is `±` any block gap of `U` at
`b`. -/
theorem crown_eq_blockGap {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : RegRed.CLRegionData G U a b)
    {d : ℕ} (L : ℝ) (base k₀ : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) {r : Mom d}
    (hr : G.molecule.IsBlockGap L base (LGSpine.bondIndex G z) U b r) :
    cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative) = r ∨
      cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative) = -r := by
  rw [crown_coset R L k₀ z hz]
  rcases lower_blockGap_eq R L base z hr with e | e <;>
    rcases sign_smul_eq_or_neg (G.sign b.toNode)
      (latticePoint L (z b.toNode) - latticePoint L (z (b.child R.kept))) with s | s
  · exact Or.inl (s.trans e.symm)
  · right
    rw [s, e]
  · right
    rw [s, e, neg_neg]
  · left
    rw [s, e]

/-! ## The crown gap of an ingredient has the group's kind -/

/-- The crown gap at the lower joint of any CL block presentation `(U, a, b)` of an ingredient `U` of a group `S ∈ 𝒞`
has the gap kind of `S`. -/
theorem crown_gapKind_of_ingredient (hM : G.molecule.IsMolecule) {d : ℕ} (L γ η : ℝ) (base : Mom d)
    (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (LGSpine.bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hz : IsDecoration G z)
    {S U : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) {kind : Molecule.GapKind}
    (hk : VineA.NormalizedSplice.groupGapKind G L γ η base (LGSpine.bondIndex G z) S = kind)
    (hI : IsIngredient G.molecule S U) {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b)
    (R : RegRed.CLRegionData G U a b) (k₀ : Mom d) :
    Molecule.gapKind L γ η
      (cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative)) = kind := by
  obtain ⟨r, hr, hkr⟩ := ingredient_blockGap_of_groupGapKind hM L γ η base c _ hκ hc0 hS hk hI (isBlock_swap hB)
  rcases crown_eq_blockGap R L base k₀ z hz hr with e | e
  · rw [e, hkr]
  · rw [e, Vine.gapKind_neg, hkr]

theorem norm_le_of_gapKind_SG {d : ℕ} {L γ η : ℝ} {r : Mom d} (h : Molecule.gapKind L γ η r = .SG) :
    r ≠ 0 ∧ ‖r‖ ≤ L ^ (-γ + η) := by
  unfold Molecule.gapKind at h
  split_ifs at h with h0 h1
  exact ⟨h0, h1⟩

/-! ## The σ-bridge -/

/-- **σ-bridge, dart-label form.** Under main's σ-restriction `selDarts σ` on the labels `bondIndex G z`, the crown
gap at the lower joint of every CL block presentation of an ingredient of an SG group is SG. -/
theorem crown_gapKind_SG_of_selDarts (hM : G.molecule.IsMolecule) {d : ℕ} (L γ η : ℝ) (base : Mom d)
    (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (LGSpine.bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hz : IsDecoration G z)
    (σ : VineA.NormalizedSplice.GroupPrescription G)
    (hsel : VineA.NormalizedSplice.selDarts σ L γ η base (LGSpine.bondIndex G z))
    {S U : Finset (GBranch G.tree)} (hS : S ∈ maximalGroups G.molecule) (hσ : σ ⟨S, hS⟩ = .SG)
    (hI : IsIngredient G.molecule S U) {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b)
    (R : RegRed.CLRegionData G U a b) (k₀ : Mom d) :
    Molecule.gapKind L γ η
      (cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative)) = .SG :=
  crown_gapKind_of_ingredient hM L γ η base c z hκ hc0 hz hS ((hsel ⟨S, hS⟩).trans hσ) hI hB R k₀

/-- **σ-bridge, `𝒱₀(σ)` form.** Under main's σ-restriction `selOf (ofPrescription σ)` (Stage-1 form), every vine
`𝕍 ∈ vinesV0 G σ` has an SG crown gap at the lower joint of any CL block presentation of its atoms. -/
theorem crown_gapKind_SG_of_vinesV0 (hM : G.molecule.IsMolecule) {d : ℕ} (L γ η : ℝ) (base : Mom d)
    (c : GBranch G.tree → Mom d) (z : GNode G.tree → (Fin d → ℤ))
    (hκ : G.molecule.IsDecoration L base c (LGSpine.bondIndex G z))
    (hc0 : ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0) (hz : IsDecoration G z)
    (σ : RedSplice.Prescription G)
    (hsel : VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z)
    {V : CLVine G} (hV : V ∈ RedSplice.vinesV0 G σ) {U : Finset (GBranch G.tree)} (hVU : V.atoms = U)
    {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b) (R : RegRed.CLRegionData G U a b) (k₀ : Mom d) :
    Molecule.gapKind L γ η
      (cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative)) = .SG := by
  obtain ⟨-, S, hS, hI, hσ, -⟩ := hV
  exact crown_gapKind_SG_of_selDarts hM L γ η base c z hκ hc0 hz _ hsel hS hσ (hVU ▸ hI) hB R k₀

/-- The molecule decoration of the dart labels `bondIndex G z` of a plain garden decoration (main
`moleculeDecoration_of_garden`, `gardenSource_eq_zero_of_deg_four`). -/
theorem moleculeDecoration_bondIndex (hp : G.IsPlain) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) :
    ∃ c, G.molecule.IsDecoration L base c (LGSpine.bondIndex G z) ∧
      ∀ v ∈ G.molecule.atoms, G.molecule.deg v = 4 → c v = 0 := by
  refine ⟨Mole.gardenSource G hp (fun i => base + latticePoint L (z (GNode.root G.tree i))), ?_, ?_⟩
  · rw [LGSpine.bondIndex_eq_restrictLabels]
    exact Mole.moleculeDecoration_of_garden G hp _ hL base z (LGSpine.isDecoration_cosetDecoration G L base z hz)
      (fun _ => rfl)
  · intro v _ hv
    exact LGSpine.gardenSource_eq_zero_of_deg_four G hp _ v hv

/-- **σ-bridge, plain-garden form (the export).** For a plain garden `G`, an integer decoration `z` satisfying main's
σ-restriction `selOf (ofPrescription σ) L γ η base z`, and `𝕍 ∈ vinesV0 G σ`: at the lower joint `b` of any CL block
presentation `(U, a, b)` of the atoms of `𝕍`, the crown gap of `k = k₀ + z/L` is SG,
`0 < ‖k(b.child pos) − k(b.child neg)‖ ≤ L^{-γ+η}`. -/
theorem crown_gap_le_of_vinesV0 (hp : G.IsPlain) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (hz : IsDecoration G z) (σ : RedSplice.Prescription G)
    (hsel : VineA.NormalizedSplice.selOf (VineA.NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z)
    {V : CLVine G} (hV : V ∈ RedSplice.vinesV0 G σ) {U : Finset (GBranch G.tree)} (hVU : V.atoms = U)
    {a b : GBranch G.tree} (hB : G.molecule.IsBlock U a b) (R : RegRed.CLRegionData G U a b) (k₀ : Mom d) :
    cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative) ≠ 0 ∧
      ‖cosetDecoration G L k₀ z (b.child R.positive) - cosetDecoration G L k₀ z (b.child R.negative)‖ ≤
        L ^ (-γ + η) := by
  obtain ⟨c, hκ, hc0⟩ := moleculeDecoration_bondIndex hp hL base z hz
  exact norm_le_of_gapKind_SG (crown_gapKind_SG_of_vinesV0 (Mole.garden_isMolecule G) L γ η base c z hκ hc0 hz σ
    hsel hV hVU hB R k₀)

end WaveTurbulence.Flower.MkMark
