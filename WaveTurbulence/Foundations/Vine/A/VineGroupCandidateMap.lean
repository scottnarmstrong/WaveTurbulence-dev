/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineGroupPickCarrier
/-! Exact candidate bijections under the actual molecular atom and dart maps. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.Stage1 WaveTurbulence.LGSpine.SourceVine
variable {w : ℕ} {G H : Garden w}

/-- A molecular map carries the single-HV case to the single-HV case. -/
theorem SingleHVGroup.map {S : Finset (GBranch G.tree)} (h : SingleHVGroup G S)
    (F : MolIso G.molecule H.molecule) : SingleHVGroup H (F.img S) := by
  refine ⟨F.maximalGroups_img h.1, ?_, ?_⟩
  · obtain ⟨a, b, hv⟩ := h.2.1
    exact ⟨F.e a, F.e b, F.isHV_img hv⟩
  · rintro ⟨a, b, hv⟩
    obtain ⟨a, rfl⟩ := F.e.surjective a
    obtain ⟨b, rfl⟩ := F.e.surjective b
    exact h.2.2 ⟨a, b, F.isHVC_img_iff.mp hv⟩

/-- The raw HV triple bijection keeps both joint order and dart orientation. -/
def hvTripleEquiv (F : MolIso G.molecule H.molecule) :
    (GBranch G.tree × GBranch G.tree × GardenDart G) ≃
      (GBranch H.tree × GBranch H.tree × GardenDart H) := F.e.prodCongr (F.e.prodCongr F.d)

/-- Validity is preserved and reflected for every HV triple. -/
theorem hvCandidate_map_iff (F : MolIso G.molecule H.molecule) (S : Finset (GBranch G.tree))
    (t : GBranch G.tree × GBranch G.tree × GardenDart G) :
    HVCandidate H (F.img S) (hvTripleEquiv F t) ↔ HVCandidate G S t := by
  rcases t with ⟨a, b, e⟩
  constructor
  · intro h
    have he := F.symm.ends_img h.1
    refine ⟨?_, (F.erase e).isSomeVine_img_iff.mp h.2⟩
    change G.molecule.ends (F.d.symm (F.d e)) = s(F.e.symm (F.e a), F.e.symm (F.e b)) at he
    simpa only [Equiv.symm_apply_apply] using he
  · intro h
    exact ⟨F.ends_img h.1, (F.erase e).isSomeVine_img h.2⟩

/-- The complete HV candidate carriers are bijective. -/
def hvCandidateEquiv (F : MolIso G.molecule H.molecule) (S : Finset (GBranch G.tree)) :
    {t // HVCandidate G S t} ≃ {t // HVCandidate H (F.img S) t} :=
  (hvTripleEquiv F).subtypeEquiv (fun t => (hvCandidate_map_iff F S t).symm)

/-- The literal whole-support bijection induced by the atom bijection. -/
def atomSetEquiv (F : MolIso G.molecule H.molecule) : Finset (GBranch G.tree) ≃ Finset (GBranch H.tree) :=
  ⟨F.img, F.symm.img, F.img_img_symm, F.img_symm_img⟩

/-- The raw DV constituent/joint bijection. -/
def dvTripleEquiv (F : MolIso G.molecule H.molecule) :
    (Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) ≃
      (Finset (GBranch H.tree) × GBranch H.tree × GBranch H.tree) :=
  (atomSetEquiv F).prodCongr (F.e.prodCongr F.e)

/-- Every valid DV constituent is carried to a valid whole constituent. -/
theorem dvCandidate_map (F : MolIso G.molecule H.molecule) {S : Finset (GBranch G.tree)}
    {t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree} (h : DVCandidate G S t) :
    DVCandidate H (F.img S) (dvTripleEquiv F t) := by
  obtain ⟨B, hA, hB, hI, hS⟩ := h
  refine ⟨F.img B, F.isVine_img hA, F.isVine_img hB, ?_, ?_⟩
  · change F.img t.1 ∩ F.img B = {F.e t.2.1, F.e t.2.2}
    rw [← F.img_inter, hI]
    simp only [MolIso.img, Finset.image_insert, Finset.image_singleton]
  · change F.img S = F.img t.1 ∪ F.img B
    rw [hS, F.img_union]

/-- Validity is also reflected for every DV triple. -/
theorem dvCandidate_map_iff (F : MolIso G.molecule H.molecule) (S : Finset (GBranch G.tree))
    (t : Finset (GBranch G.tree) × GBranch G.tree × GBranch G.tree) :
    DVCandidate H (F.img S) (dvTripleEquiv F t) ↔ DVCandidate G S t := by
  refine ⟨fun h => ?_, dvCandidate_map F⟩
  have hh := dvCandidate_map F.symm h
  change DVCandidate G (F.symm.img (F.img S))
    (F.symm.img (F.img t.1), F.e.symm (F.e t.2.1), F.e.symm (F.e t.2.2)) at hh
  rw [F.img_img_symm, F.img_img_symm, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hh
  exact hh

/-- The complete DV candidate carriers are bijective. -/
def dvCandidateEquiv (F : MolIso G.molecule H.molecule) (S : Finset (GBranch G.tree)) :
    {t // DVCandidate G S t} ≃ {t // DVCandidate H (F.img S) t} :=
  (dvTripleEquiv F).subtypeEquiv (fun t => (dvCandidate_map_iff F S t).symm)

/-- The pure-DV exclusion conditions are preserved by a molecular map. -/
theorem PureDVGroup.map {S : Finset (GBranch G.tree)} (h : PureDVGroup G S)
    (F : MolIso G.molecule H.molecule) : PureDVGroup H (F.img S) := by
  refine ⟨F.maximalGroups_img h.1, ?_, ?_⟩
  · obtain ⟨a, b, hv⟩ := h.2.1
    exact ⟨F.e a, F.e b, F.isDV_img hv⟩
  · rintro ⟨a, b, hv⟩
    have back : ∃ a b, IsHV G.molecule S a b ∨ IsVC G.molecule S a b ∨ IsHVC G.molecule S a b := by
      rcases hv with hv | hv | hv
      · have hh := F.symm.isHV_img hv
        rw [F.img_img_symm] at hh
        exact ⟨_, _, Or.inl hh⟩
      · have hh := F.symm.isVC_img hv
        rw [F.img_img_symm] at hh
        exact ⟨_, _, Or.inr (Or.inl hh)⟩
      · have hh := F.symm.isHVC_img hv
        rw [F.img_img_symm] at hh
        exact ⟨_, _, Or.inr (Or.inr hh)⟩
    exact h.2.2 back

end WaveTurbulence.VineA
