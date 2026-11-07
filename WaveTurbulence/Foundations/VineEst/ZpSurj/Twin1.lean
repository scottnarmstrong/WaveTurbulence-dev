/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Dat1

/-! # ZP-SURJ: conjugation preserves the layer-`p` count and the sizes -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree Reg Reg.Skeleton Twist Links RegRed WaveTurbulence.LGSpine WaveTurbulence.ConjCoh

variable {w : ℕ}

theorem topBranchCount_conj {LG LH : LayeredGarden w} {e : Fin w ≃ Fin w} (h : IsConjugateBy LG LH e) (p : ℕ) :
    topBranchCount LH p = topBranchCount LG p := by
  classical
  unfold topBranchCount
  refine Finset.card_equiv (PL234.Conj.branchEquiv h).symm (fun b => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 := PL234.Conj.layer_node h ((PL234.Conj.branchEquiv h).symm b).toNode
  have h2 : (PL234.Conj.branchEquiv h ((PL234.Conj.branchEquiv h).symm b)).toNode = b.toNode := by
    rw [Equiv.apply_symm_apply]
  rw [← PL234.Conj.branch_toNode, h2] at h1
  rw [h1]

mutual
theorem regCpl_size_even : ∀ Q : RegCpl, Even Q.size
  | .triv => ⟨0, rfl⟩
  | .type1 _ Q₁ Q₂ Q₃ => by
    obtain ⟨a, ha⟩ := regCpl_size_even Q₁
    obtain ⟨b, hb⟩ := regCpl_size_even Q₂
    obtain ⟨c, hc⟩ := regCpl_size_even Q₃
    exact ⟨a + b + c + 1, by simp only [RegCpl.size]; omega⟩
  | .type2 Xp Xm Qlp => by
    obtain ⟨a, ha⟩ := regChain_size_even Xp
    obtain ⟨b, hb⟩ := regChain_size_even Xm
    obtain ⟨c, hc⟩ := regCpl_size_even Qlp
    exact ⟨a + b + c, by simp only [RegCpl.size]; omega⟩
termination_by structural Q => Q

theorem regChain_size_even : ∀ X : RegChain, Even X.size
  | .nil => ⟨0, rfl⟩
  | .pair _ Qr Qg inner rest => by
    obtain ⟨a, ha⟩ := regCpl_size_even Qr
    obtain ⟨b, hb⟩ := regCpl_size_even Qg
    obtain ⟨c, hc⟩ := regChain_size_even inner
    obtain ⟨d, hd⟩ := regChain_size_even rest
    exact ⟨a + b + c + d + 1, by simp only [RegChain.size]; omega⟩
termination_by structural X => X
end

end WaveTurbulence.ZpSurj
