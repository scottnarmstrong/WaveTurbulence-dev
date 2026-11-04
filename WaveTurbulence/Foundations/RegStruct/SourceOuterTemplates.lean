/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.DoubleChainB
public import WaveTurbulence.Foundations.RegStruct.SourceDecorationGrafts

/-! # Actual source construction of the two outer template families -/

public section
namespace WaveTurbulence.Reg
open TTree

/-- Every bare double chain is an actual source-regular couple, built by B from the trivial couple. -/
theorem bareDoubleChain_isRegular (p n : RegChain) (hp : BareChain p) (hn : BareChain n) :
    IsRegularCouple (decodedCouple (joinChains p n .triv)) := by
  generalize hsize : p.size+n.size = N
  induction N using Nat.strong_induction_on generalizing p n with
  | h N ih =>
    by_cases hp0 : p = .nil
    · subst p
      by_cases hn0 : n = .nil
      · subst n
        exact decodedTriv_isRegular
      · obtain ⟨Y,m,target,hY,hSY,ht,he⟩ := bareChain_prune n hn hn0 (-1) (1,[])
        have hsmall := ih (RegChain.nil.size+Y.size) (by change 0+Y.size < N; change 0+n.size=N at hsize; omega) .nil Y trivial hY rfl
        have hreg := isRegularCouple_operationB (joinChains .nil Y .triv) hsmall target m
          (doubleChain_negative_position .nil Y target ht)
        have hcarrier := operationB_doubleChain_negative .nil Y target m ht
        rw [he] at hcarrier
        rw [← hcarrier]
        exact hreg
    · obtain ⟨Y,m,target,hY,hSY,ht,he⟩ := bareChain_prune p hp hp0 1 (0,[])
      have hsmall := ih (Y.size+n.size) (by omega) Y n hY hn rfl
      have hreg := isRegularCouple_operationB (joinChains Y n .triv) hsmall target m
        (doubleChain_positive_position Y n target ht)
      have hcarrier := operationB_doubleChain_positive Y n target m ht
      rw [he] at hcarrier
      rw [← hcarrier]
      exact hreg

/-- Source A on the initial pair gives the exact chosen mini-couple template. -/
theorem operationA_triv_eq_mini (c : MiniCplCode) :
    operationA .triv (0,[]) (1,[]) c = miniCoupleCode c := by
  simp [operationA,substituteCouplePair,miniCoupleCode,normalizeCouple]

/-- Each of the two mini-couple templates is an actual source-regular couple. -/
theorem miniCouple_isRegular (c : MiniCplCode) : IsRegularCouple (decodedCouple (miniCoupleCode c)) := by
  have hpair : (((0 : Fin 2),[]),(1,[])) ∈ RegCpl.triv.raw.2 := by
    exact List.mem_singleton_self _
  have h := isRegularCouple_operationA .triv decodedTriv_isRegular (0,[]) (1,[]) c hpair
  rw [operationA_triv_eq_mini] at h
  exact h

end WaveTurbulence.Reg
