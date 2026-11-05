/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineInsertionPaths
public import WaveTurbulence.Foundations.Molecule.VineExpansionInvariant
public import WaveTurbulence.Foundations.Molecule.VineTemplatePaths
import Mathlib.Tactic

/-! # Connectivity of every expanded vine template (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- Every template atom is connected to its first joint. -/
@[expose] def TemplateConnected (T : VineTemplate) : Prop :=
  ∀ v < T.n, Relation.EqvGen (EdgeAdj T.bonds) 0 v

/-- The complete degree profile excludes bonds to names outside the atom range. -/
theorem degreeProfile_endpoints {T : VineTemplate} (hT : DegreeProfile T)
    {e : ℕ×ℕ} (he : e ∈ T.bonds) : e.1 < T.n ∧ e.2 < T.n := by
  have hp1 : 0 < (T.bonds.map Prod.fst).count e.1 :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)
  have hp2 : 0 < (T.bonds.map Prod.snd).count e.2 :=
    List.count_pos_iff.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)
  constructor
  · by_contra hn
    have hh := hT.2 e.1
    simp only [hn,ite_false,templateDegree] at hh
    omega
  · by_contra hn
    have hh := hT.2 e.2
    simp only [hn,ite_false,templateDegree] at hh
    omega

/-- Every inserted atom is attached to an old endpoint by an actual rail. -/
theorem insertRungs_connected (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hd : DegreeProfile T) (hc : TemplateConnected T)
    (h1 : s.1 ∈ T.bonds) (h2 : s.2 ∈ T.bonds.erase s.1) :
    TemplateConnected (insertRungs T s k) := by
  intro v hv
  rw [insertRungs_atoms] at hv
  by_cases hold : v < T.n
  · exact insertion_path T s k (hc v hold)
  · have hk : k ≠ 0 := by intro hk; subst k; omega
    have hrange : T.n ≤ v ∧ v < T.n+2*k := ⟨by omega,hv⟩
    have hf := fresh_counts T.n k v
    simp only [hrange,and_self,ite_true] at hf
    have hfirst := (degreeProfile_endpoints hd h1).1
    have hsecond := (degreeProfile_endpoints hd (List.mem_of_mem_erase h2)).1
    by_cases hu : v ∈ (List.range k).map (T.n+·)
    · exact Relation.EqvGen.trans _ _ _ (insertion_path T s k (hc _ hfirst))
        (path_mono (fun _ h => first_rail_mem T s hk h) (rail_mem_path _ _ _ hu))
    · have hz := List.count_eq_zero_of_not_mem hu
      have hpos : 0 < ((List.range k).map (T.n+k+·)).count v := by omega
      have hv' : v ∈ (List.range k).map (T.n+k+·) := List.count_pos_iff.mp hpos
      exact Relation.EqvGen.trans _ _ _ (insertion_path T s k (hc _ hsecond))
        (path_mono (fun _ h => second_rail_mem T s hk h) (rail_mem_path _ _ _ hv'))

/-- TARGET defvine: every full expansion is connected, for arbitrary rung counts. -/
theorem expand_connected (X : VineType) (k : List ℕ)
    (hk : k.length=X.template.slots.length) : TemplateConnected (X.expand k) := by
  have hslots : slotMembers (X.template.slots.zip k) =
      X.template.slots.flatMap (fun s => [s.1,s.2]) := by
    conv_rhs => rw [← List.map_fst_zip (l₂ := k) hk.symm.le]
    rw [List.flatMap_map]
    rfl
  have hr := template_slots_ready X
  have hh := fold_insertRungs_invariant
    (fun T => DegreeProfile T ∧ TemplateConnected T) (fun _ => True)
    (fun T s k _ hT h1 h2 => ⟨insertRungs_degreeProfile T s k hT.1 h1 h2,
      insertRungs_connected T s k hT.1 hT.2 h1 h2⟩)
    (X.template.slots.zip k) X.template ⟨template_degreeProfile X,template_paths X⟩
    (fun _ _ => trivial) (hslots ▸ hr.1) (hslots ▸ hr.2)
  exact hh.2

end WaveTurbulence.Vine
