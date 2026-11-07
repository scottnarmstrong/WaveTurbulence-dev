/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBTripleOrdering
public import WaveTurbulence.Foundations.FinalCount.AppBTripleSignCap
import Mathlib.Tactic

/-! # Ordered three-bond coordinates at an actual degree-three atom -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

structure AppbLocalTriple {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (v : V) where
  first : Fin P.edges.length
  middle : Fin P.edges.length
  last : Fin P.edges.length
  first_ne_middle : first ≠ middle
  first_ne_last : first ≠ last
  middle_ne_last : middle ≠ last
  cover : ∀ i,i = first ∨ i = middle ∨ i = last
  incidence : ∀ i,appbIncidence M v (r.edge i).val = 1
  same_sign : appbIncidenceSign M v (r.edge first).val = appbIncidenceSign M v (r.edge last).val
  opposite_sign : appbIncidenceSign M v (r.edge first).val ≠ appbIncidenceSign M v (r.edge middle).val

/-- Three distinct indices exhaust Fin 3. -/
theorem appb_fin_three_cover (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∀ t : Fin 3,t = i ∨ t = j ∨ t = k := by
  intro t
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases t <;> simp_all

/-- The ordered profile follows from source degree caps and the input
incidence table; no extra sign assumption is imposed on the operation. -/
theorem appb_localTriple_exists {M : Molecule V D} {P : AppbPattern}
    (r : AppbRealization M P) (hM : M.IsMolecule) (hlen : P.edges.length = 3)
    {v : V} (hv : v ∈ M.atoms) (hinc : ∀ i,appbIncidence M v (r.edge i).val = 1) :
    Nonempty (AppbLocalTriple r v) := by
  let σ : Fin 3 → ℤˣ := fun i => appbIncidenceSign M v (r.edge (Fin.cast hlen.symm i)).val
  have hp : ¬∀ i,σ i = 1 := by
    intro hall
    apply r.not_all_positive_signs hM (by omega) hv
    intro i
    have hc : Fin.cast hlen.symm (Fin.cast hlen i) = i := Fin.ext rfl
    simpa only [σ,hc] using hall (Fin.cast hlen i)
  have hn : ¬∀ i,σ i = -1 := by
    intro hall
    apply r.not_all_negative_signs hM (by omega) hv hinc
    intro i
    have hc : Fin.cast hlen.symm (Fin.cast hlen i) = i := Fin.ext rfl
    simpa only [σ,hc] using hall (Fin.cast hlen i)
  obtain ⟨i,j,k,hij,hik,hjk,hs,ho⟩ := appb_three_sign_order σ hp hn
  refine ⟨⟨Fin.cast hlen.symm i,Fin.cast hlen.symm j,Fin.cast hlen.symm k,
    fun he => hij (Fin.cast_injective hlen.symm he),
    fun he => hik (Fin.cast_injective hlen.symm he),
    fun he => hjk (Fin.cast_injective hlen.symm he),?_,hinc,hs,ho⟩⟩
  intro t
  rcases appb_fin_three_cover i j k hij hik hjk (Fin.cast hlen t) with ht | ht | ht
  · exact Or.inl ((Fin.cast_injective hlen) (by simpa using ht))
  · exact Or.inr (Or.inl ((Fin.cast_injective hlen) (by simpa using ht)))
  · exact Or.inr (Or.inr ((Fin.cast_injective hlen) (by simpa using ht)))

namespace AppbLocalTriple
variable {M : Molecule V D} {P : AppbPattern} {r : AppbRealization M P} {v : V}
    (t : AppbLocalTriple r v)

def project {K : Type*} (q : Fin P.edges.length → K) : K × K × K :=
  (q t.first,q t.middle,q t.last)

theorem project_injective {K : Type*} : Function.Injective (t.project (K := K)) := by
  intro q q' he
  funext i
  rcases t.cover i with hi | hi | hi
  · exact hi ▸ congrArg Prod.fst he
  · exact hi ▸ congrArg (fun q => q.2.1) he
  · exact hi ▸ congrArg (fun q => q.2.2) he

theorem sum_three {E : Type*} [AddCommMonoid E] (f : Fin P.edges.length → E) :
    (∑ i,f i) = f t.first+f t.middle+f t.last := by
  have hu : (univ : Finset (Fin P.edges.length)) = {t.first,t.middle,t.last} := by
    ext i
    simp only [mem_univ,mem_insert,mem_singleton,true_iff]
    exact t.cover i
  rw [hu]
  simp [t.first_ne_middle,t.first_ne_last,t.middle_ne_last,add_assoc]

end AppbLocalTriple
end WaveTurbulence.Mole
