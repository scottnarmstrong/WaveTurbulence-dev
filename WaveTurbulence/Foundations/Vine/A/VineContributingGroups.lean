/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineCollectionSupport
/-! Intrinsic classification of the maximal groups contributing actual C1 objects. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset Stage1 RedSplice LGSpine.SourceVine
variable {w : ℕ} {G : Garden w}

/-- The group has one of the three whole-group vine-like shapes. -/
def VineLikeGroup (G : Garden w) (S : Finset (GBranch G.tree)) : Prop :=
  ∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b

/-- A genuine skipped ingredient prevents a whole-group unit. -/
theorem skipped_unit_ne_group {S : Finset (GBranch G.tree)} (U : GroupUnits G S)
    (sk : SkipData G S) (hsk : U.skip = some sk) {u : CLBlock G} (hu : u ∈ U.units) : u.atoms ≠ S := by
  intro he
  have hxA := sk.vine.choose_spec.1.2.1
  have hyA := sk.vine.choose_spec.1.2.2.1
  have hxy := sk.vine.choose_spec.1.2.2.2.1
  have hAS : sk.A ⊆ S := by
    intro z hz
    have hh : z ∈ sk.L0 ∪ sk.A ∪ sk.R0 := mem_union_left _ (mem_union_right _ hz)
    exact sk.hS.symm ▸ hh
  rcases (U.skip_units sk hsk).1 u hu with ⟨hL, _⟩ | ⟨hR, _⟩
  · have hyL : sk.y ∈ sk.L0 := he.symm.trans hL ▸ hAS hyA
    rcases sk.left with ⟨hn, _⟩ | ⟨_, _, _, hi⟩
    · exact notMem_empty sk.y (hn ▸ hyL)
    · have hh : sk.y = sk.x := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hyL, hyA⟩)
      exact hxy hh.symm
  · have hxR : sk.x ∈ sk.R0 := he.symm.trans hR ▸ hAS hxA
    rcases sk.right with ⟨hn, _⟩ | ⟨_, _, _, hi⟩
    · exact notMem_empty sk.x (hn ▸ hxR)
    · have hh : sk.x = sk.y := mem_singleton.mp (hi ▸ mem_inter.mpr ⟨hxR, hxA⟩)
      exact hxy hh

/-- Every skipped group is a VC or HVC group, regardless of the chosen skipped presentation. -/
theorem skipped_vineLikeGroup {S : Finset (GBranch G.tree)} (sk : SkipData G S) : VineLikeGroup G S := by
  rcases hb : sk.bond with _ | e
  · obtain ⟨n, hi⟩ := sk.chainM hb
    exact ⟨sk.a, sk.b, Or.inr (Or.inl ⟨sk.blockM hb, n, chain_ofVine (Vine.chainIngredient_spec hi).1⟩)⟩
  · obtain ⟨n, hn, hi⟩ := sk.chainN e hb
    exact ⟨sk.a, sk.b, Or.inr (Or.inr
      ⟨e, (sk.blockN e hb).1, (sk.blockN e hb).2, n, hn, chain_ofVine (Vine.chainIngredient_spec hi).1⟩)⟩

/-- The actual contributing predicate is whole-group shape minus whole-group contraction. -/
theorem hasObj_iff (S : Finset (GBranch G.tree)) (hS : S ∈ maximalGroups G.molecule) :
    HasObj G S ↔ VineLikeGroup G S ∧ ¬ ∃ u ∈ (groupUnitsOf G S).units, u.atoms = S := by
  constructor
  · rintro (⟨hHV, hN⟩ | ⟨sk, hsk⟩)
    · obtain ⟨a, b, hv⟩ := hHV
      refine ⟨⟨a, b, Or.inl hv⟩, ?_⟩
      rintro ⟨u, hu, _⟩
      rw [(groupUnitsOf G S).hv_empty ⟨a, b, hv⟩ hN] at hu
      exact List.not_mem_nil hu
    · exact ⟨skipped_vineLikeGroup sk, fun ⟨u, hu, he⟩ => skipped_unit_ne_group _ sk hsk hu he⟩
  · rintro ⟨hVL, hwhole⟩
    rcases hs : (groupUnitsOf G S).skip with _ | sk
    · by_cases hHV : (∃ a b, IsHV G.molecule S a b) ∧ ¬ ∃ a b, IsHVC G.molecule S a b
      · exact Or.inl hHV
      · have hVC : ∃ a b, IsVC G.molecule S a b ∨ IsHVC G.molecule S a b := by
          obtain ⟨a, b, hv | hv | hv⟩ := hVL
          · by_cases hh : ∃ a b, IsHVC G.molecule S a b
            · obtain ⟨c, d, hh⟩ := hh; exact ⟨c, d, Or.inr hh⟩
            · exact (hHV ⟨⟨a, b, hv⟩, hh⟩).elim
          · exact ⟨a, b, Or.inl hv⟩
          · exact ⟨a, b, Or.inr hv⟩
        rcases (groupUnitsOf G S).vl (Mole.garden_isMolecule G) hS hVC with hn | ⟨sk, hsk⟩
        · obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hn
          exact (hwhole ⟨u, hu, (groupUnitsOf G S).noskip_units hs u hu⟩).elim
        · rw [hs] at hsk; cases hsk
    · exact Or.inr ⟨sk, hs⟩

end WaveTurbulence.VineA
