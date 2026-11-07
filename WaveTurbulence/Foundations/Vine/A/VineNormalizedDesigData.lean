/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedRedSpliceDesig
public import WaveTurbulence.Foundations.Vine.A.VineObjectExt
public import WaveTurbulence.Foundations.Vine.A.VineObjectGeometry
/-! Exact HV/DV data forced by the R83 successor designation predicate. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.Mole WaveTurbulence.LGSpine.SourceVine
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}

/-- A single-HV group has no skipped VC/HVC ingredient. -/
theorem SingleHVGroup.skip_none (hS : SingleHVGroup G S) : (groupUnitsOf G S).skip = none := by
  cases hs : (groupUnitsOf G S).skip with
  | none => rfl
  | some sk =>
    obtain ⟨a, b, hv | hv⟩ := ingredient_vc_or_hvc sk.ingredient
    · obtain ⟨c, d, e, he, hV⟩ := hS.2.1
      exact (block_not_hyper hv.1 e he hV.choose_spec.1).elim
    · exact (hS.2.2 ⟨a, b, hv⟩).elim

/-- A pure-DV group has no skipped VC/HVC ingredient. -/
theorem PureDVGroup.skip_none (hS : PureDVGroup G S) : (groupUnitsOf G S).skip = none := by
  cases hs : (groupUnitsOf G S).skip with
  | none => rfl
  | some sk =>
    obtain ⟨a, b, hv⟩ := ingredient_vc_or_hvc sk.ingredient
    exact (hS.2.2 ⟨a, b, Or.inr hv⟩).elim

/-- Every successor single-HV designation uses exactly the unique normalized triple. -/
theorem normalizedDesig_hv_data (hS : SingleHVGroup G S) {a : GBranch G.tree} {O : Object G.molecule}
    (h : NormalizedSplice.IsDesig G S a O) :
    ∃ b e, hvGroupPick G S = some (a, b, e) ∧ O.atoms = S ∧ O.upper = a ∧ O.lower = b ∧
      objectAdded O = some e := by
  obtain ⟨b, e, hp, hA, hL, R, hR, he⟩ := h.2.2.2.2.2.1 hS.skip_none
    ((groupUnitsOf G S).hv_empty hS.2.1 hS.2.2) hS.2.1 hS.2.2
  exact ⟨b, e, hp, hA, h.1.symm, hL, by simp only [objectAdded, hR, he]⟩

/-- Every successor pure-DV designation is the selected entire type-V constituent. -/
theorem normalizedDesig_dv_data (hS : PureDVGroup G S) {a : GBranch G.tree} {O : Object G.molecule}
    (h : NormalizedSplice.IsDesig G S a O) :
    ∃ A b, dvGroupPick G S = some (A, a, b) ∧ O.atoms = A ∧ O.upper = a ∧ O.lower = b ∧
      G.molecule.IsVine .V O.atoms O.upper O.lower ∧ objectAdded O = none := by
  obtain ⟨A, b, hp, hA, hL, hv, hV⟩ := h.2.2.2.2.2.2.2 hS.skip_none hS.units_empty hS.2.2
  exact ⟨A, b, hp, hA, h.1.symm, hL, hv, by simp only [objectAdded, hV]⟩

/-- Single-HV designated objects are unique, even when joint witnesses were chosen independently. -/
theorem normalizedDesig_hv_unique (hS : SingleHVGroup G S)
    {a b : GBranch G.tree} {O P : Object G.molecule}
    (hO : NormalizedSplice.IsDesig G S a O) (hP : NormalizedSplice.IsDesig G S b P) : O = P := by
  obtain ⟨c, e, hp, hA, hU, hL, hD⟩ := normalizedDesig_hv_data hS hO
  obtain ⟨d, f, hq, kA, kU, kL, kD⟩ := normalizedDesig_hv_data hS hP
  have he := Option.some.inj (hp.symm.trans hq)
  have hab := congrArg Prod.fst he
  have hcd := congrArg (fun t => t.2.1) he
  have hef := congrArg (fun t => t.2.2) he
  exact object_eq_of_data O P (hA.trans kA.symm) (hU.trans (hab.trans kU.symm))
    (hL.trans (hcd.trans kL.symm)) (hD.trans ((congrArg some hef).trans kD.symm))

/-- Pure-DV designated objects are unique on the selected whole constituent. -/
theorem normalizedDesig_dv_unique (hS : PureDVGroup G S)
    {a b : GBranch G.tree} {O P : Object G.molecule}
    (hO : NormalizedSplice.IsDesig G S a O) (hP : NormalizedSplice.IsDesig G S b P) : O = P := by
  obtain ⟨A, c, hp, hA, hU, hL, _, hD⟩ := normalizedDesig_dv_data hS hO
  obtain ⟨B, d, hq, kA, kU, kL, _, kD⟩ := normalizedDesig_dv_data hS hP
  have he := Option.some.inj (hp.symm.trans hq)
  exact object_eq_of_data O P (hA.trans ((congrArg Prod.fst he).trans kA.symm))
    (hU.trans ((congrArg (fun t => t.2.1) he).trans kU.symm))
    (hL.trans ((congrArg (fun t => t.2.2) he).trans kL.symm)) (hD.trans kD.symm)

end WaveTurbulence.VineA
