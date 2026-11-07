/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Shared.GardenReconstructionUniqueness
public import WaveTurbulence.Foundations.Stage1.Shared.MoleculeCodes
import Mathlib.Tactic

/-!
# Finite encoding of all gardens with a fixed molecule

DH21-2 Proposition 6.4. The isomorphism to the fixed molecule is chosen
once per garden; it is not counted as additional data. Injectivity is
proved from actual tree and pairing reconstruction.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
variable {V D : Type*} (M : Molecule V D) (w : ℕ)

/-- The exact family counted in molecular reconstruction, using the actual
ordinary-garden and directed multigraph carriers. -/
abbrev GardensWithMolecule := {G : Garden w // G.IsPlain ∧ Nonempty (GardenMoleculeIso G M)}

/-- Incidence codes, root records and one sign bit for each ordered root. -/
abbrev GardenEncoding := (D → Fin 4) × (Fin w → RootRecord M.atoms w) × (Fin w → Bool)

noncomputable instance [Fintype D] : Fintype (GardenEncoding M w) := by
  classical
  exact inferInstanceAs (Fintype ((D → Fin 4) × (Fin w → RootRecord M.atoms w) × (Fin w → Bool)))

/-- Choosing an actual molecular isomorphism does not change which garden
is encoded; no multiplicity for isomorphism choices is introduced. -/
@[expose] noncomputable def encodeGarden (G : GardensWithMolecule M w) : GardenEncoding M w :=
  let f := Classical.choice G.2.2
  (encodePositions G.1 M f,encodeRoot G.1 M f,fun i => decide (G.1.sig i = 1))

/-- The actual garden, not a quotient of labeled isomorphisms, is uniquely
recovered from its encoding. -/
theorem encodeGarden_injective : Function.Injective (encodeGarden M w) := by
  intro G H he
  have hc := congrArg Prod.fst he
  have hr := congrArg (fun x : GardenEncoding M w => x.2.1) he
  have hs := congrArg (fun x : GardenEncoding M w => x.2.2) he
  apply Subtype.ext
  apply garden_reconstruction_unique (Classical.choice G.2.2) (Classical.choice H.2.2) G.2.1 H.2.1 hc hr
  funext i
  have hi := congrFun hs i
  change decide (G.1.sig i = 1) = decide (H.1.sig i = 1) at hi
  rcases Int.units_eq_one_or (G.1.sig i) with hG | hG <;>
    rcases Int.units_eq_one_or (H.1.sig i) with hH | hH <;> simp_all

variable [Fintype D]

/-- Exact cardinality of the unrestricted encoding type. -/
theorem card_gardenEncoding :
    Fintype.card (GardenEncoding M w) = 4^(Fintype.card D)*(4*M.atoms.card+w)^w*2^w := by
  classical
  have hroot : Fintype.card (RootRecord M.atoms w) = 4*M.atoms.card+w := by
    simp only [RootRecord,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_coe]
    omega
  simp only [GardenEncoding,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,
    Fintype.card_bool,hroot,mul_assoc]


/-- Finiteness of the actual fiber over a fixed directed molecule. -/
theorem finite_gardensWithMolecule : Finite (GardensWithMolecule M w) :=
  Finite.of_injective (encodeGarden M w) (encodeGarden_injective M w)

/-- The raw reconstruction count, prior to factorial/exponential absorption. -/
theorem card_gardensWithMolecule_raw :
    Nat.card (GardensWithMolecule M w) ≤ 4^(Fintype.card D)*(4*M.atoms.card+w)^w*2^w := by
  have h := Nat.card_le_card_of_injective (encodeGarden M w) (encodeGarden_injective M w)
  rw [Nat.card_eq_fintype_card (α := GardenEncoding M w),card_gardenEncoding] at h
  exact h

end WaveTurbulence.Mole
