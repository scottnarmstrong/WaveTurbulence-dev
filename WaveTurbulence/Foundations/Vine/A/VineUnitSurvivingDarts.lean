/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceChildren
/-! The exceptional PC/LP exchange fixes all surviving original darts.
Thus the actual quotient dart map has ordinary branch/leaf names. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Twist
variable {w : ℕ} {G : Garden w}

/-- A swap of two points satisfying a predicate fixes every point outside it. -/
theorem swap_fixed_of_not_predicate {A : Type*} [DecidableEq A] (P : A → Prop)
    {a b x : A} (ha : P a) (hb : P b) (hx : ¬ P x) : Equiv.swap a b x = x :=
  Equiv.swap_apply_of_ne_of_ne (fun h => hx (h.symm ▸ ha)) (fun h => hx (h.symm ▸ hb))

/-- B1b-2 (Mk-general form of `exceptionalDartSwap_fixed_of_not_deleted`). -/
theorem exceptionalDartSwap_fixed_of_not_deletedMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)}
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (d : GardenDart G)
    (hd : ¬ DeletedDart (stSt G σ Mk).cls d) : exceptionalDartSwap G Z.P d = d := by
  classical
  let R := DeletedDart (stSt G σ Mk).cls
  have hp : R (lowerPC G Z.P false) := active_internal_dart_mergedMk Z σ hsel
    ⟨Z.hB.2.2.1, Z.hCL.2.choose_spec⟩
  have hl : R (retainedLP G Z.P) := active_internal_dart_mergedMk Z σ hsel (retainedLP_inGroup Z)
  have hp' : R (lowerPC G Z.P true) := (deletedDart_mate_iff _ _).mpr hp
  have hl' : R (G.molecule.mate (retainedLP G Z.P)) := (deletedDart_mate_iff _ _).mpr hl
  change Equiv.swap _ _ (Equiv.swap _ _ d) = d
  rw [swap_fixed_of_not_predicate R hp hl hd, swap_fixed_of_not_predicate R hp' hl' hd]

/-- B1b-2 (Mk-general form of `twistDartEquiv_eq_naive_of_not_deleted`). -/
theorem twistDartEquiv_eq_naive_of_not_deletedMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)}
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (d : GardenDart G)
    (hd : ¬ DeletedDart (stSt G σ Mk).cls d) : twistDartEquiv G Z.P d = naiveDartEquiv G Z.P d :=
  congrArg (naiveDartEquiv G Z.P) (exceptionalDartSwap_fixed_of_not_deletedMk Z σ hsel d hd)

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_surviving_dart_names`). -/
theorem unitSpliceMolIso_surviving_dart_namesMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (d : GardenDart (stSt G σ Mk).G) :
    (stSt Z.target (transportPrescription Z.iso σ) Mk').M.od ((unitSpliceMolIsoMk Z σ hT hsel).d d) =
      naiveDartEquiv G Z.P ((stSt G σ Mk).M.od d) := by
  have hd : ¬ DeletedDart (stSt G σ Mk).cls ((stSt G σ Mk).M.od d) :=
    ((stSt G σ Mk).M.od_range _).mp ⟨d, rfl⟩
  exact (unitSpliceMolIso_dart_namesMk Z σ hT hsel d).trans
    (twistDartEquiv_eq_naive_of_not_deletedMk Z σ hsel _ hd)

end WaveTurbulence.VineA
