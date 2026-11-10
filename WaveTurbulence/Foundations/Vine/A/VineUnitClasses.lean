/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitList
public import WaveTurbulence.Foundations.Vine.A.VineSpliceQuotient
/-! Actual selected unit transport intertwines the complete merge classes.
The active lower node and every active internal dart are merged away. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- B1b-2 (Mk-general form of `unitBlocks_cls_twist`, two marked sets carried by the twist). -/
theorem unitBlocks_cls_twistMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (v : GBranch G.tree) :
    (spliceFold Z.target (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).cls (Z.iso.e v) =
      ((spliceFold G (unitBlocks G σ Mk)).cls v).map Z.iso.e := by
  classical
  have hs := unitBlocks_pairwiseMk (Mole.garden_isMolecule G) σ Mk
  have ht := unitBlocks_pairwiseMk (Mole.garden_isMolecule Z.target) (transportPrescription Z.iso σ) Mk'
  by_cases hv : ∃ u ∈ unitBlocks G σ Mk, v ∈ u.atoms
  · obtain ⟨u, hu, hv⟩ := hv
    have hmu := unitImage_memMk Z σ hT hsel hu
    have hmv : Z.iso.e v ∈ (unitImage Z u (unitBlocks_goodMk Z σ hsel hu)).atoms :=
      (Z.iso.mem_img u.atoms v).mpr hv
    rw [spliceFold_cls_mem _ hs hu hv, spliceFold_cls_mem _ ht hmu hmv]
    rfl
  · have hn : ∀ u ∈ unitBlocks G σ Mk, v ∉ u.atoms := fun u hu h => hv ⟨u, hu, h⟩
    have hn' : ∀ u' ∈ unitBlocks Z.target (transportPrescription Z.iso σ) Mk', Z.iso.e v ∉ u'.atoms := by
      intro u' hu' hm
      obtain ⟨u, hu, hat, _, _⟩ := unitBlocks_preimageMk Z σ hT hsel hu'
      rw [hat] at hm
      exact hn u hu ((Z.iso.mem_img u.atoms v).mp hm)
    rw [spliceFold_cls_notMem _ hs hn, spliceFold_cls_notMem _ ht hn']
    rfl

/-- B1b-2 (Mk-general form of `unitBlocks_repC_twist`). -/
theorem unitBlocks_repC_twistMk (Z : TwistGroupSite G) (σ : Prescription G) {Mk : Set (CLVine G)}
    {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (v : GBranch G.tree) :
    repC (spliceFold Z.target (unitBlocks Z.target (transportPrescription Z.iso σ) Mk')).cls (Z.iso.e v) =
      Z.iso.e (repC (spliceFold G (unitBlocks G σ Mk)).cls v) := by
  unfold repC
  rw [unitBlocks_cls_twistMk Z σ hT hsel v]
  cases (spliceFold G (unitBlocks G σ Mk)).cls v <;> rfl

/-- B1b (Mk-general form of `active_support_unit`). -/
theorem active_support_unitMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (Stage1.CLVine _)} (hsel : ∃ c ∈ vinesV0 (Mk := Mk) G σ, c.atoms = Z.S0) :
    ∃ u ∈ unitBlocks (Mk := Mk) G σ, Z.S0 ⊆ u.atoms := by
  obtain ⟨c, hc, hat⟩ := hsel
  obtain ⟨_, u, hu, hsub⟩ := (vinesV0_iff_unit_cover_diffMk (Mk := Mk) G σ c).mp hc
  exact ⟨u, hu, hat ▸ hsub⟩

/-- B1b (Mk-general form of `active_lower_merged`). -/
theorem active_lower_mergedMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (Stage1.CLVine _)} (hsel : ∃ c ∈ vinesV0 (Mk := Mk) G σ, c.atoms = Z.S0) :
    ∃ u ∈ unitBlocks (Mk := Mk) G σ, (spliceFold G (unitBlocks (Mk := Mk) G σ)).cls Z.P.lower = some u.upper ∧ u.upper ≠ Z.P.lower := by
  obtain ⟨u, hu, hsub⟩ := active_support_unitMk (Mk := Mk) Z σ hsel
  have hp := internalParent_mono hsub Z.hCL.2
  refine ⟨u, hu, spliceFold_cls_mem _ (unitBlocks_pairwiseMk (Mk := Mk) (Mole.garden_isMolecule G) σ) hu
    (hsub Z.hB.2.2.1), ?_⟩
  intro he
  exact u.cl.1 (he.symm ▸ hp)

/-- B1b (Mk-general form of `active_internal_dart_merged`). -/
theorem active_internal_dart_mergedMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (Stage1.CLVine _)} (hsel : ∃ c ∈ vinesV0 (Mk := Mk) G σ, c.atoms = Z.S0) {d : GardenDart G}
    (hd : G.molecule.InGroup Z.S0 d) :
    ∃ a, (spliceFold G (unitBlocks (Mk := Mk) G σ)).cls (G.molecule.atom d) = some a ∧
      (spliceFold G (unitBlocks (Mk := Mk) G σ)).cls (G.molecule.atom (G.molecule.mate d)) = some a := by
  obtain ⟨u, hu, hsub⟩ := active_support_unitMk (Mk := Mk) Z σ hsel
  have hmem : ∀ {v}, v ∈ u.atoms → (spliceFold G (unitBlocks (Mk := Mk) G σ)).cls v = some u.upper :=
    fun hv => spliceFold_cls_mem (unitBlocks (Mk := Mk) G σ) (unitBlocks_pairwiseMk (Mk := Mk) (Mole.garden_isMolecule G) σ) hu hv
  exact ⟨u.upper, hmem (hsub hd.1), hmem (hsub hd.2)⟩

end WaveTurbulence.VineA
