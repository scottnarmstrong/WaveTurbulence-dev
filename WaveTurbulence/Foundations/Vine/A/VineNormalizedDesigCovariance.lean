/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedDesigData
public import WaveTurbulence.Foundations.Vine.A.VineGroupPickCovariance
/-! Exact object covariance of the R83 single-HV and pure-DV designations. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
variable {w : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)}
variable (Z : TwistGroupSite G) (hsel : ∃ c ∈ vinesV0 G (fun _ => .SG), c.atoms = Z.S0)
include hsel

/-- Any source and target successor HV designations agree under the actual object map. -/
theorem normalizedDesig_hv_transport (hS : SingleHVGroup G S)
    {a : GBranch G.tree} {a' : GBranch Z.target.tree} {O : Object G.molecule} {P : Object Z.target.molecule}
    (hO : NormalizedSplice.IsDesig G S a O) (hP : NormalizedSplice.IsDesig Z.target (Z.iso.img S) a' P) :
    P = mapObject Z.iso O := by
  obtain ⟨b, e, hp, hA, hU, hL, hD⟩ := normalizedDesig_hv_data hS hO
  obtain ⟨b', e', hq, kA, kU, kL, kD⟩ := normalizedDesig_hv_data (hS.map Z.iso) hP
  have hpk := hvGroupPick_twist Z hsel (S := S)
  rw [hp, hq] at hpk
  have he : (a', b', e') = (Z.iso.e a, Z.iso.e b, Z.iso.d e) := Option.some.inj hpk
  apply object_eq_of_data
  · change P.atoms = Z.iso.img O.atoms
    exact kA.trans (congrArg Z.iso.img hA).symm
  · change P.upper = Z.iso.e O.upper
    exact kU.trans ((congrArg Prod.fst he).trans (congrArg Z.iso.e hU).symm)
  · change P.lower = Z.iso.e O.lower
    exact kL.trans ((congrArg (fun t => t.2.1) he).trans (congrArg Z.iso.e hL).symm)
  · rw [mapObject_added, hD, kD]
    exact congrArg some (congrArg (fun t => t.2.2) he)

/-- Any source and target successor DV designations carry the entire chosen constituent. -/
theorem normalizedDesig_dv_transport (hS : PureDVGroup G S)
    {a : GBranch G.tree} {a' : GBranch Z.target.tree} {O : Object G.molecule} {P : Object Z.target.molecule}
    (hO : NormalizedSplice.IsDesig G S a O) (hP : NormalizedSplice.IsDesig Z.target (Z.iso.img S) a' P) :
    P = mapObject Z.iso O := by
  obtain ⟨A, b, hp, hA, hU, hL, _, hD⟩ := normalizedDesig_dv_data hS hO
  obtain ⟨B, b', hq, kA, kU, kL, _, kD⟩ := normalizedDesig_dv_data (hS.map Z.iso) hP
  have hpk := dvGroupPick_twist Z hsel (S := S)
  rw [hp, hq] at hpk
  have he : (B, a', b') = (Z.iso.img A, Z.iso.e a, Z.iso.e b) := Option.some.inj hpk
  apply object_eq_of_data
  · change P.atoms = Z.iso.img O.atoms
    exact kA.trans ((congrArg Prod.fst he).trans (congrArg Z.iso.img hA).symm)
  · change P.upper = Z.iso.e O.upper
    exact kU.trans ((congrArg (fun t => t.2.1) he).trans (congrArg Z.iso.e hU).symm)
  · change P.lower = Z.iso.e O.lower
    exact kL.trans ((congrArg (fun t => t.2.2) he).trans (congrArg Z.iso.e hL).symm)
  · rw [mapObject_added, hD, kD]
    rfl

/-- The actual single-HV designatedObject function commutes with the actual LF map. -/
theorem designatedObject_singleHV_twist (hS : SingleHVGroup G S) :
    NormalizedSplice.designatedObject Z.target (Z.iso.img S) =
      (NormalizedSplice.designatedObject G S).map (mapObject Z.iso) := by
  obtain ⟨a, O, _, hO, hd⟩ := NormalizedSplice.designatedObject_spec hS.1
  obtain ⟨b, P, _, hP, he⟩ := NormalizedSplice.designatedObject_spec (hS.map Z.iso).1
  rw [hO, hP]
  exact congrArg some (normalizedDesig_hv_transport Z hsel hS hd he)

/-- The actual pure-DV designatedObject function commutes with the actual LF map. -/
theorem designatedObject_pureDV_twist (hS : PureDVGroup G S) :
    NormalizedSplice.designatedObject Z.target (Z.iso.img S) =
      (NormalizedSplice.designatedObject G S).map (mapObject Z.iso) := by
  obtain ⟨a, O, _, hO, hd⟩ := NormalizedSplice.designatedObject_spec hS.1
  obtain ⟨b, P, _, hP, he⟩ := NormalizedSplice.designatedObject_spec (hS.map Z.iso).1
  rw [hO, hP]
  exact congrArg some (normalizedDesig_dv_transport Z hsel hS hd he)

end WaveTurbulence.VineA
