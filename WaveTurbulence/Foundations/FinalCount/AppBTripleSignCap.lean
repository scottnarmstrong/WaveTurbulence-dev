/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBIncidenceGap
import Mathlib.Tactic

/-! # Source degree caps exclude three equal local orientations -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

/-- The source out-degree bound excludes three positive local signs. -/
theorem not_all_positive_signs (hM : M.IsMolecule) (hlen : 3 ≤ P.edges.length)
    {v : V} (hv : v ∈ M.atoms) :
    ¬∀ i,appbIncidenceSign M v (r.edge i).val = 1 := by
  intro hall
  have ha (i : Fin P.edges.length) : M.atom (r.edge i).val = v := by
    by_contra hn
    have hh := hall i
    simp [appbIncidenceSign,hn] at hh
  let f (i : Fin P.edges.length) : {x // x ∈ (M.dartsAt v).filter (fun x => M.out x = true)} :=
    ⟨(r.edge i).val,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ha i⟩,
      (mem_filter.mp (mem_filter.mp (r.edge i).property).1).2⟩⟩
  have hinj : Function.Injective f := by
    intro i j he
    have hh : (f i).val = (f j).val := congrArg (fun z => z.val) he
    exact r.edge.injective (Subtype.ext hh)
  have hc : P.edges.length ≤ M.outdeg v := by
    have hh := Fintype.card_le_of_injective f hinj
    simpa only [Fintype.card_fin,Fintype.card_coe,Molecule.outdeg] using hh
  have hd := (hM.1 v hv).1
  omega

/-- The source in-degree bound excludes three negative local signs. -/
theorem not_all_negative_signs (hM : M.IsMolecule) (hlen : 3 ≤ P.edges.length)
    {v : V} (hv : v ∈ M.atoms) (hinc : ∀ i,appbIncidence M v (r.edge i).val = 1) :
    ¬∀ i,appbIncidenceSign M v (r.edge i).val = -1 := by
  intro hall
  have ha (i : Fin P.edges.length) : M.atom (M.mate (r.edge i).val) = v := by
    have hn : M.atom (r.edge i).val ≠ v := by
      intro he
      have hh := hall i
      simp [appbIncidenceSign,he] at hh
    simpa only [appbIncidenceDart,hn,ite_false] using appbIncidenceDart_atom M v (r.edge i).val (hinc i)
  have ho (i : Fin P.edges.length) : M.out (M.mate (r.edge i).val) = false := by
    rw [M.out_mate,(mem_filter.mp (mem_filter.mp (r.edge i).property).1).2]
    rfl
  let f (i : Fin P.edges.length) : {x // x ∈ (M.dartsAt v).filter (fun x => M.out x = false)} :=
    ⟨M.mate (r.edge i).val,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ha i⟩,ho i⟩⟩
  have hinj : Function.Injective f := by
    intro i j he
    exact r.edge.injective (Subtype.ext (mate_injective M (congrArg Subtype.val he)))
  have hc : P.edges.length ≤ M.indeg v := by
    have hh := Fintype.card_le_of_injective f hinj
    simpa only [Fintype.card_fin,Fintype.card_coe,Molecule.indeg] using hh
  have hd := (hM.1 v hv).2
  omega

end AppbRealization
end WaveTurbulence.Mole
