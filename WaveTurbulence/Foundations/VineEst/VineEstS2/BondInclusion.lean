/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS2.InternalBondDarts

/-! # Actual internal-bond inclusions and restriction of label assignments -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS2
open VineParamContract
variable {V D : Type*} [DecidableEq V] [Fintype D] {M : Molecule V D} {S T U : Finset V}

theorem internalBondSet_mono (hST : S ⊆ T) : internalBondSet M S ⊆ internalBondSet M T := by
  intro e he
  obtain ⟨hb,hs⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hb,⟨hST hs.1,hST hs.2⟩⟩

noncomputable def includeBond (hST : S ⊆ T) (e : Bond M S) : Bond M T :=
  ⟨e.1,internalBondSet_mono hST e.2⟩

theorem includeBond_injective (hST : S ⊆ T) : Function.Injective (includeBond (M := M) hST) := by
  intro e f he
  exact Subtype.ext (congrArg (fun q : Bond M T => q.1) he)

noncomputable def restrictBondLabels {E : Type*} (hST : S ⊆ T) (k : Bond M T → E) : Bond M S → E :=
  fun e => k (includeBond hST e)

/-- There is no incidence at a vertex outside the actual atom group. -/
theorem flow_eq_zero_of_not_mem {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V)
    (k : Bond M S → E) {v : V} (hv : v ∉ S) : flow M S k v = 0 := by
  classical
  unfold flow
  apply Finset.sum_eq_zero
  intro e _
  have he := internalBond_inGroup M S e
  have h1 : M.atom e.1 ≠ v := fun h => hv (h ▸ he.1)
  have h2 : M.atom (M.mate e.1) ≠ v := fun h => hv (h ▸ he.2)
  simp only [incidence,h1,h2,ite_false,sub_self,zero_smul]

end WaveTurbulence.VineEstS2
