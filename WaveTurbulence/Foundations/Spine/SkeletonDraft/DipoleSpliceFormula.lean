/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Dipoles
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.InternalSplice

/-! # A three-bond contraction reconnects exactly its two free attachment ports -/

public section
namespace WaveTurbulence.Reg.Skeleton
namespace Dipole

/-- On every surviving port, contracting a dipole is the single splice of its free ports. -/
theorem contract_outside_free {V : Type*} [DecidableEq V] {mate : V × Fin 4 → V × Fin 4}
    (D : Dipole mate) (hm : Function.Involutive mate) (x : V × Fin 4)
    (hu : x.1 ≠ D.u) (hv : x.1 ≠ D.v) :
    D.contract x = splice mate (D.u,D.free) (D.v,D.perm D.free) x := by
  let p := ((D.u,D.free),(D.v,D.perm D.free))
  let P := D.pairs.erase p
  have hp : p ∈ D.pairs := List.mem_ofFn.mpr ⟨D.free,rfl⟩
  have he : D.pairs.Perm (p::P) := List.perm_cons_erase hp
  have hn := (pairPorts_perm he).nodup_iff.mp D.pairPorts_nodup
  have ht := (pairPorts_nodup_cons p P).mp hn
  have hmx : x ∉ pairPorts D.pairs := by
    intro hx
    rcases (D.pairPorts_mem x).mp hx with h | h
    · exact hu h
    · exact hv h
  have hx : x ∉ pairPorts P := by
    intro hx
    exact hmx ((pairPorts_perm he).mem_iff.mpr (by rw [pairPorts_cons]; simp only [List.mem_cons]; exact Or.inr (Or.inr hx)))
  change foldSplice mate D.pairs x = _
  rw [foldSplice_perm he mate hm D.pairPorts_nodup D.targets_active]
  change foldSplice (splice mate p.1 p.2) P x = _
  apply foldSplice_matched P _ (splice_involutive mate hm p.1 p.2 ht.1
    (D.active_u D.free) (D.active_v (D.perm D.free))) ht.2.2.2 ?_ x hx
  intro q hq
  have hq' : q ∈ D.pairs := List.mem_of_mem_erase hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq'
  have hi : i ≠ D.free := by
    intro hi
    apply ht.2.1
    change (D.u,D.free) ∈ pairPorts P
    rw [← hi]
    exact List.mem_flatMap.mpr ⟨_,hq,by simp⟩
  have hmi := D.internal i hi
  apply (splice_unaffected mate p.1 p.2 (D.u,i) ?_ ?_ ?_ ?_).trans hmi
  · intro heq; exact hi (congrArg Prod.snd heq)
  · intro heq; exact D.ne (congrArg Prod.fst heq)
  · rw [hmi]
    intro heq; exact D.ne (congrArg Prod.fst heq).symm
  · rw [hmi]
    intro heq; exact hi (D.perm.injective (congrArg Prod.snd heq))

end Dipole
end WaveTurbulence.Reg.Skeleton
