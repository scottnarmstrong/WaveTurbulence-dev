/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceType1Root

/-! # Restricting the special-node condition to recursive source link blocks -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree

/-- Local special-node admissibility passes to a source sub-block because
the original chosen-node list has no repetitions. The ambient marked
set may contain nodes in other blocks. -/
theorem special_on_sublinks {w : ℕ}
    (L S : List ((Fin w × Path) × (Fin w × Path)))
    (hsub : ∀ l ∈ S, l ∈ L) (hnd : (L.map Prod.fst).Nodup)
    (Z : Finset (Fin w × Path))
    (hZ : ∀ z ∈ L.map Prod.fst, z ∈ Z → ∃ i : Fin 3, (z,addrExt z [i]) ∈ L) :
    ∀ z ∈ S.map Prod.fst, z ∈ Z → ∃ i : Fin 3, (z,addrExt z [i]) ∈ S := by
  intro z hz hzZ
  obtain ⟨l,hl,he⟩ := List.mem_map.mp hz
  obtain ⟨i,hi⟩ := hZ z (List.mem_map.mpr ⟨l,hsub l hl,he⟩) hzZ
  refine ⟨i,?_⟩
  have hpair : l = (z,addrExt z [i]) :=
    List.inj_on_of_nodup_map hnd (hsub l hl) hi he
  rw [← hpair]
  exact hl

/-- The local form of special admissibility already excludes a type1
root, even when the marked set includes nodes outside this sub-code. -/
theorem type1_root_not_mem_locally_special {w : ℕ} (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl)
    (a b : Fin w × Path) (hab : Indep a b) (Z : Finset (Fin w × Path))
    (hZ : ∀ z ∈ ((RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b).map Prod.fst,
      z ∈ Z → ∃ i : Fin 3, (z,addrExt z [i]) ∈ (RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b) :
    a ∉ Z := by
  classical
  let Z' := Z ∩ (((RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b).map Prod.fst).toFinset
  have hs : IsSpecialSet ((RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b) Z' := by
    intro z hz
    obtain ⟨hzZ,hzL⟩ := Finset.mem_inter.mp hz
    exact hZ z (List.mem_toFinset.mp hzL) hzZ
  intro ha
  apply type1_root_not_mem_special c Q₁ Q₂ Q₃ a b hab Z' hs
  apply Finset.mem_inter.mpr
  refine ⟨ha,List.mem_toFinset.mpr ?_⟩
  simp only [RegCpl.linksAt,List.map_cons,List.mem_cons,true_or]

end WaveTurbulence.RA1Leafwise
