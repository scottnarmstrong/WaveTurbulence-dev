/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineOperationPieceData
public import WaveTurbulence.Foundations.Molecule.VineCoherenceIndependent
/-! Actual vine realizations and their incoherency indices transport
along molecular isomorphisms, independently of the atom-list order. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.Vine
variable {w : ℕ} {G H : Garden w}

/-- Transport the literal witnesses of the pinned molecular vine realization. -/
noncomputable def mapVineRealization (F : MolIso G.molecule H.molecule) {X : VineType}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : VineRealization G.molecule X S a b) :
    VineRealization H.molecule X (F.img S) (F.e a) (F.e b) where
  k := R.k
  length_eq := R.length_eq
  f := R.f ∘ F.e.symm
  injOn := by
    intro u hu v hv he
    obtain ⟨u, rfl⟩ := F.e.surjective u
    obtain ⟨v, rfl⟩ := F.e.surjective v
    have he' : R.f u = R.f v := by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using he
    exact congrArg F.e (R.injOn ((F.mem_img S u).mp hu) ((F.mem_img S v).mp hv) he')
  image_eq := by
    change (S.image F.e).image (R.f ∘ F.e.symm) = _
    rw [Finset.image_image]
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using R.image_eq
  joints_eq := by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using R.joints_eq
  bonds_eq := by
    rw [F.groupBonds_img, Multiset.map_map]
    have he : (Sym2.map (R.f ∘ F.e.symm)) ∘ Sym2.map F.e = Sym2.map R.f := by
      funext p
      refine Sym2.inductionOn p ?_
      intro u v
      simp only [Function.comp_apply, Sym2.map_mk, Equiv.symm_apply_apply]
    rw [he]
    exact R.bonds_eq

/-- Transported actual groups have the same monochromatic/nonmonochromatic status. -/
theorem mapVineRealization_index (F : MolIso G.molecule H.molecule) {X : VineType}
    {S : Finset (GBranch G.tree)} {a b : GBranch G.tree} (R : VineRealization G.molecule X S a b)
    (layer : GBranch H.tree → ℕ) :
    realizedIncoherencyIndex (mapVineRealization F R) layer = realizedIncoherencyIndex R (layer ∘ F.e) := by
  classical
  unfold realizedIncoherencyIndex realizedGroups
  change incoherencyIndex layer ((X.expand R.k).groups.map (fun g =>
      (F.img S).toList.filter (fun v => R.f (F.e.symm v) ∈ g))) =
    incoherencyIndex (layer ∘ F.e) ((X.expand R.k).groups.map (fun g => S.toList.filter (fun v => R.f v ∈ g)))
  unfold incoherencyIndex
  rw [List.filter_map, List.filter_map, List.length_map, List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  intro g _
  have hm (u : GBranch G.tree) :
      F.e u ∈ (F.img S).toList.filter (fun v => R.f (F.e.symm v) ∈ g) ↔
        u ∈ S.toList.filter (fun v => R.f v ∈ g) := by
    simp only [List.mem_filter, Finset.mem_toList, decide_eq_true_eq, Equiv.symm_apply_apply, F.mem_img]
  have hc : GroupCoherent layer ((F.img S).toList.filter (fun v => R.f (F.e.symm v) ∈ g)) ↔
      GroupCoherent (layer ∘ F.e) (S.toList.filter (fun v => R.f v ∈ g)) := by
    constructor
    · intro h u hu v hv
      exact h (F.e u) ((hm u).mpr hu) (F.e v) ((hm v).mpr hv)
    · intro h u hu v hv
      obtain ⟨u, rfl⟩ := F.e.surjective u
      obtain ⟨v, rfl⟩ := F.e.surjective v
      exact h u ((hm u).mp hu) v ((hm v).mp hv)
  apply Bool.eq_iff_iff.mpr
  simpa only [Function.comp_apply, decide_eq_true_eq] using not_congr hc

end WaveTurbulence.VineA
