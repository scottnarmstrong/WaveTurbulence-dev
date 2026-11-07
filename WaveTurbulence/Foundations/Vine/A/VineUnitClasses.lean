/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitList
public import WaveTurbulence.Foundations.Vine.A.VineSpliceOrder
/-! Actual selected unit transport intertwines the complete merge classes.
The active lower node and every active internal dart are merged away. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.RedSplice WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- The actual spliceFold merge classes commute with the unit twist atom map. -/
theorem unitBlocks_cls_twist (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (v : GBranch G.tree) :
    (spliceFold Z.target (unitBlocks Z.target (transportPrescription Z.iso σ))).cls (Z.iso.e v) =
      ((spliceFold G (unitBlocks G σ)).cls v).map Z.iso.e := by
  classical
  have hs := unitBlocks_pairwise (Mole.garden_isMolecule G) σ
  have ht := unitBlocks_pairwise (Mole.garden_isMolecule Z.target) (transportPrescription Z.iso σ)
  by_cases hv : ∃ u ∈ unitBlocks G σ, v ∈ u.atoms
  · obtain ⟨u, hu, hv⟩ := hv
    have hmu := unitImage_mem Z σ hsel hu
    have hmv : Z.iso.e v ∈ (unitImage Z u (unitBlocks_good Z σ hsel hu)).atoms :=
      (Z.iso.mem_img u.atoms v).mpr hv
    rw [spliceFold_cls_mem _ hs hu hv, spliceFold_cls_mem _ ht hmu hmv]
    rfl
  · have hn : ∀ u ∈ unitBlocks G σ, v ∉ u.atoms := fun u hu h => hv ⟨u, hu, h⟩
    have hn' : ∀ u' ∈ unitBlocks Z.target (transportPrescription Z.iso σ), Z.iso.e v ∉ u'.atoms := by
      intro u' hu' hm
      obtain ⟨u, hu, hat, _, _⟩ := unitBlocks_preimage Z σ hsel hu'
      rw [hat] at hm
      exact hn u hu ((Z.iso.mem_img u.atoms v).mp hm)
    rw [spliceFold_cls_notMem _ hs hn, spliceFold_cls_notMem _ ht hn']
    rfl

/-- The actual quotient retractions commute as well. -/
theorem unitBlocks_repC_twist (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (v : GBranch G.tree) :
    repC (spliceFold Z.target (unitBlocks Z.target (transportPrescription Z.iso σ))).cls (Z.iso.e v) =
      Z.iso.e (repC (spliceFold G (unitBlocks G σ)).cls v) := by
  unfold repC
  rw [unitBlocks_cls_twist Z σ hsel v]
  cases (spliceFold G (unitBlocks G σ)).cls v <;> rfl

/-- The entire active selected support lies in one actual unit. -/
theorem active_support_unit (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    ∃ u ∈ unitBlocks G σ, Z.S0 ⊆ u.atoms := by
  obtain ⟨c, hc, hat⟩ := hsel
  obtain ⟨_, u, hu, hsub⟩ := (vinesV0_iff_unit_cover G σ c).mp hc
  exact ⟨u, hu, hat ▸ hsub⟩

/-- The active lower node is merged into a distinct surviving crown. -/
theorem active_lower_merged (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) :
    ∃ u ∈ unitBlocks G σ, (spliceFold G (unitBlocks G σ)).cls Z.P.lower = some u.upper ∧ u.upper ≠ Z.P.lower := by
  obtain ⟨u, hu, hsub⟩ := active_support_unit Z σ hsel
  have hp := internalParent_mono hsub Z.hCL.2
  refine ⟨u, hu, spliceFold_cls_mem _ (unitBlocks_pairwise (Mole.garden_isMolecule G) σ) hu
    (hsub Z.hB.2.2.1), ?_⟩
  intro he
  exact u.cl.1 (he.symm ▸ hp)

/-- Every active internal dart is deleted by the actual simultaneous splice. -/
theorem active_internal_dart_merged (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) {d : GardenDart G}
    (hd : G.molecule.InGroup Z.S0 d) :
    ∃ a, (spliceFold G (unitBlocks G σ)).cls (G.molecule.atom d) = some a ∧
      (spliceFold G (unitBlocks G σ)).cls (G.molecule.atom (G.molecule.mate d)) = some a := by
  obtain ⟨u, hu, hsub⟩ := active_support_unit Z σ hsel
  have hmem : ∀ {v}, v ∈ u.atoms → (spliceFold G (unitBlocks G σ)).cls v = some u.upper :=
    fun hv => spliceFold_cls_mem (unitBlocks G σ) (unitBlocks_pairwise (Mole.garden_isMolecule G) σ) hu hv
  exact ⟨u.upper, hmem (hsub hd.1), hmem (hsub hd.2)⟩

end WaveTurbulence.VineA
