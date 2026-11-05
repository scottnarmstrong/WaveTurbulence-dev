/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineEraseBondDegrees
public import WaveTurbulence.Foundations.Molecule.VineLikeConnected
import Mathlib.Tactic

/-! # A nonloop bond deletion preserves the molecule axioms -/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Deleting a nonloop bond preserves the source molecule axioms. New
components touching a deleted endpoint contain its now deficient degree;
all other paths to an old deficient atom lift through surviving bonds. -/
theorem eraseBond_isMolecule (M : Molecule V D) (hM : M.IsMolecule) (e : D)
    (hne : M.atom e ≠ M.atom (M.mate e)) : (Mole.eraseBond M e).IsMolecule := by
  let N := Mole.eraseBond M e
  have hle (v : V) := eraseBond_degree_le M e v
  have hend (v : V) (hv : v=M.atom e ∨ v=M.atom (M.mate e)) : N.deg v ≠ 4 := by
    have hd1 := eraseBond_degree_endpoint M e hne
    have hd2 := eraseBond_degree_endpoint M (M.mate e) (by rw [M.mate_mate]; exact hne.symm)
    rw [eraseBond_mate_degree] at hd2
    have hb1 := Mole.deg_le_four M hM (M.atom_mem e)
    have hb2 := Mole.deg_le_four M hM (M.atom_mem (M.mate e))
    rcases hv with hv | hv <;> subst v <;> change (Mole.eraseBond M e).deg _ ≠ 4 <;> omega
  let Good : V → Prop := fun v => ∃ u ∈ M.atoms,N.SameComponent v u ∧ N.deg u ≠ 4
  have good_end (v : V) (hv : v=M.atom e ∨ v=M.atom (M.mate e)) : Good v := by
    have hvm : v ∈ M.atoms := hv.elim (fun h => h.symm ▸ M.atom_mem e)
      (fun h => h.symm ▸ M.atom_mem (M.mate e))
    exact ⟨v,hvm,Relation.EqvGen.refl _,hend v hv⟩
  have follow (u v : V) (huv : M.Adj u v) (hg : Good v) : Good u := by
    by_cases hue : u=M.atom e ∨ u=M.atom (M.mate e)
    · exact good_end u hue
    · obtain ⟨d,hdu,hdv⟩ := huv
      have hdne : d ≠ e := by intro he; subst d; exact hue (Or.inl hdu.symm)
      have hdm : d ≠ M.mate e := by intro he; subst d; exact hue (Or.inr hdu.symm)
      obtain ⟨w,hw,hvw,hdw⟩ := hg
      exact ⟨w,hw,Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨⟨d,hdne,hdm⟩,hdu,hdv⟩) hvw,hdw⟩
  have inv {u v : V} (hp : M.SameComponent u v) : (Good u ↔ Good v) := by
    induction hp with
    | rel u v huv => exact ⟨follow v u (Mole.adj_symmetric M huv),follow u v huv⟩
    | refl u => exact Iff.rfl
    | symm u v _ ih => exact ih.symm
    | trans u v w _ _ ih1 ih2 => exact ih1.trans ih2
  constructor
  · intro v hv
    exact ⟨(hle v).1.trans (hM.1 v hv).1,(hle v).2.1.trans (hM.1 v hv).2⟩
  · intro v hv
    obtain ⟨u,hu,hvu,hdu⟩ := hM.2 v hv
    have huN : N.deg u ≠ 4 := by
      have hb := Mole.deg_le_four M hM hu
      have hl := (hle u).2.2
      change (Mole.eraseBond M e).deg u ≠ 4
      omega
    exact (inv hvu).mpr ⟨u,hu,Relation.EqvGen.refl _,huN⟩

end WaveTurbulence.Vine
