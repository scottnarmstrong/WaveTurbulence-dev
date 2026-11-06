/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentFiniteCarrier
public import WaveTurbulence.Foundations.Molecule.B2CharacterizationProofs
/-! Source regular-code equivalence for the literal full top-layer couple carrier. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Reg

noncomputable def uniformDecodedCouple (p : ℕ) (Q : RegCpl) : LayeredGarden 2 where
  garden := decodedCouple Q
  layer := fun _ => p
  isLayering := ⟨fun _ _ => le_rfl, fun _ => rfl⟩

theorem uniformDecodedCouple_decodes (p : ℕ) (Q : RegCpl) :
    Q.Decodes (uniformDecodedCouple p Q).garden := decodedCouple_decodes Q

theorem uniformDecodedCouple_layer (p : ℕ) (Q : RegCpl) :
    ∀ a, (uniformDecodedCouple p Q).layer a = p := fun _ => rfl

theorem uniformDecodedCouple_canonical (p : ℕ) (Q : RegCpl) :
    IsCanonC (p + 1) (uniformDecodedCouple p Q) :=
  ⟨(uniformDecodedCouple_decodes p Q).1,
    canonCriterion_of_uniform_layer _ _ (uniformDecodedCouple_layer p Q)⟩

theorem uniformDecodedCouple_incoherency (p : ℕ) (Q : RegCpl) :
    (uniformDecodedCouple p Q).incoherency Q.links = 0 := by
  classical
  simp only [LayeredGarden.incoherency, uniformDecodedCouple_layer, ne_self_iff_false,
    and_false, Finset.filter_false, Finset.card_empty]

theorem uniformDecodedCouple_regular (p : ℕ) (Q : RegCpl) (hwf : Q.wf = true) :
    IsRegularCouple (uniformDecodedCouple p Q).garden := by
  obtain ⟨G, hQ, hG⟩ := Q.exists_decodes hwf
  have he := carrier_unique hQ (uniformDecodedCouple_decodes p Q)
  exact he ▸ hG

theorem layered_eq_of_garden_eq_uniform {w p : ℕ} {LG LH : LayeredGarden w}
    (hg : LG.garden = LH.garden) (hl : ∀ a, LG.layer a = p) (hl' : ∀ a, LH.layer a = p) : LG = LH := by
  rcases LG with ⟨G, l, hG⟩
  rcases LH with ⟨H, m, hH⟩
  dsimp only at hg
  subst H
  have he : l = m := funext fun a => (hl a).trans (hl' a).symm
  subst m
  rfl

noncomputable def codeToTopRegular (p n : ℕ) :
    {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n} → {LG // LG ∈ topRegularCarrier p (2 * n)} :=
  fun Q => ⟨uniformDecodedCouple p Q.1, uniformDecodedCouple_regular p Q.1 Q.2.1,
    (decodedCouple_order Q.1).trans Q.2.2, uniformDecodedCouple_layer p Q.1⟩

theorem codeToTopRegular_bijective (p n : ℕ) : Function.Bijective (codeToTopRegular p n) := by
  constructor
  · intro Q Q' he
    have hLG := congrArg Subtype.val he
    change uniformDecodedCouple p Q.1 = uniformDecodedCouple p Q'.1 at hLG
    have hQ := uniformDecodedCouple_decodes p Q.1
    have hQ' : Q'.1.Decodes (uniformDecodedCouple p Q.1).garden := by
      rw [hLG]
      exact uniformDecodedCouple_decodes p Q'.1
    have hu := existsUnique_regCpl_decodes (uniformDecodedCouple p Q.1).garden
      (uniformDecodedCouple_regular p Q.1 Q.2.1)
    exact Subtype.ext (hu.unique ⟨Q.2.1, hQ⟩ ⟨Q'.2.1, hQ'⟩)
  · intro LG
    obtain ⟨Q, hw, hQ⟩ := isRegularCouple_exists_wf_decodes LG.1.garden LG.2.1
    have hsize : Q.size = 2 * n := (size_eq_order hQ).symm.trans LG.2.2.1
    refine ⟨⟨Q, hw, hsize⟩, Subtype.ext ?_⟩
    exact layered_eq_of_garden_eq_uniform
      (carrier_unique (uniformDecodedCouple_decodes p Q) hQ)
      (uniformDecodedCouple_layer p Q) LG.2.2.2

/-- A proved equivalence, with the source uniqueness theorem discharged by REG-STRUCT. -/
noncomputable def topRegularCodeEquiv (p n : ℕ) :
    {Q : RegCpl // Q.wf = true ∧ Q.size = 2 * n} ≃ {LG // LG ∈ topRegularCarrier p (2 * n)} :=
  Equiv.ofBijective (codeToTopRegular p n) (codeToTopRegular_bijective p n)

end WaveTurbulence.LGSpine
