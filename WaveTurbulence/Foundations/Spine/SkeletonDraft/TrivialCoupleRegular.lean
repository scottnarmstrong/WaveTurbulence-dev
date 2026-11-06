/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Spine.SkeletonDraft.RegularCoupleClosure
public import WaveTurbulence.Foundations.Spine.SkeletonDraft.TrivialGardens

/-! # Every actual trivial (+,-) couple is source-regular -/

public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

theorem distinct_root_pair_mem (j k : Fin 2) (hne : k ≠ j) :
    (((j,[]) : Address 2),(k,[])) ∈ symmPairs [(((0,[]) : Address 2),(1,[]))] := by
  fin_cases j <;> fin_cases k <;> simp_all [symmPairs]

theorem trivial_couple_regular (G : Garden 2) (hc : IsCouple G) (ht : IsTrivialGarden G) : IsRegularCouple G := by
  refine ⟨((.leaf,.leaf),[(((0,[]) : Address 2),(1,[]))]),RawRegular.triv,?_⟩
  refine ⟨hc,ht.2 0,ht.2 1,?_⟩
  intro ℓ
  have hl : ℓ.1.2 = [] := by
    have hm := ℓ.2
    rw [ht.2] at hm
    exact Finset.mem_singleton.mp hm
  have hq : (G.pair ℓ).1.2 = [] := by
    have hm := (G.pair ℓ).2
    rw [ht.2] at hm
    exact Finset.mem_singleton.mp hm
  have hn : (G.pair ℓ).1.1 ≠ ℓ.1.1 := by
    intro he
    exact Comb.pair_ne_of_plain hc.1 ℓ (Subtype.ext (Prod.ext he (hq.trans hl.symm)))
  have hℓ : ℓ.1 = (ℓ.1.1,[]) := Prod.ext rfl hl
  have hp : (G.pair ℓ).1 = ((G.pair ℓ).1.1,[]) := Prod.ext rfl hq
  rw [hℓ,hp]
  exact distinct_root_pair_mem _ _ hn

end WaveTurbulence.Reg.Skeleton
