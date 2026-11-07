/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceEpsilon
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

/-- The actual exceptional exchange fixes every dart retained by the selected simultaneous splice. -/
theorem exceptionalDartSwap_fixed_of_not_deleted (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (d : GardenDart G)
    (hd : ¬ DeletedDart (stSt G σ).cls d) : exceptionalDartSwap G Z.P d = d := by
  classical
  let R := DeletedDart (stSt G σ).cls
  have hp : R (lowerPC G Z.P false) := active_internal_dart_merged Z σ hsel
    ⟨Z.hB.2.2.1, Z.hCL.2.choose_spec⟩
  have hl : R (retainedLP G Z.P) := active_internal_dart_merged Z σ hsel (retainedLP_inGroup Z)
  have hp' : R (lowerPC G Z.P true) := (deletedDart_mate_iff _ _).mpr hp
  have hl' : R (G.molecule.mate (retainedLP G Z.P)) := (deletedDart_mate_iff _ _).mpr hl
  change Equiv.swap _ _ (Equiv.swap _ _ d) = d
  rw [swap_fixed_of_not_predicate R hp hl hd, swap_fixed_of_not_predicate R hp' hl' hd]

/-- The actual LF dart map agrees with ordinary subtree transport at every retained old dart. -/
theorem twistDartEquiv_eq_naive_of_not_deleted (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (d : GardenDart G)
    (hd : ¬ DeletedDart (stSt G σ).cls d) : twistDartEquiv G Z.P d = naiveDartEquiv G Z.P d :=
  congrArg (naiveDartEquiv G Z.P) (exceptionalDartSwap_fixed_of_not_deleted Z σ hsel d hd)

/-- Literal old dart names commute with ordinary branch/leaf transport on the actual splice quotient. -/
theorem unitSpliceMolIso_surviving_dart_names (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (d : GardenDart (stSt G σ).G) :
    (stSt Z.target (transportPrescription Z.iso σ)).M.od ((unitSpliceMolIso Z σ hsel).d d) =
      naiveDartEquiv G Z.P ((stSt G σ).M.od d) := by
  have hd : ¬ DeletedDart (stSt G σ).cls ((stSt G σ).M.od d) :=
    ((stSt G σ).M.od_range _).mp ⟨d, rfl⟩
  exact (unitSpliceMolIso_dart_names Z σ hsel d).trans
    (twistDartEquiv_eq_naive_of_not_deleted Z σ hsel _ hd)

end WaveTurbulence.VineA
