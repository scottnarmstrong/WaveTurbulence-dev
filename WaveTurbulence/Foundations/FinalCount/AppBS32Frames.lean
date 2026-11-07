/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBLocalPairCut
public import WaveTurbulence.Foundations.FinalCount.AppBTripleFrame
public import WaveTurbulence.Foundations.FinalCount.AppBLocalLabelDetermination
public import WaveTurbulence.Foundations.FinalCount.AppBDeletionCounting
import Mathlib.Tactic

/-! # The exact degree-three and degree-two supports in Figure 3S2 -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

def appbS32Kinds : List AppbPatternKind := [.s32one,.s32two,.s32three,.s32four]
theorem appb_s32_kind_length (k : AppbPatternKind) (hk : k ∈ appbS32Kinds) : k.pattern.edges.length = 4 := by
  cases k <;> simp_all [appbS32Kinds,AppbPatternKind.pattern]

def appbFourEmbedding {P : AppbPattern} (h : P.edges.length = 4) : Fin 4 ↪ Fin P.edges.length :=
  (finCongr h.symm).toEmbedding

theorem appb_s32_incidence_table (k : AppbPatternKind) (hk : k ∈ appbS32Kinds)
    {M : Molecule V D} (r : AppbRealization M k.pattern) (j : Fin 4) :
    appbIncidence M (r.vertex 1) (r.edge (appbFourEmbedding (appb_s32_kind_length k hk) j)).val =
      (if j = 1 then 0 else 1) ∧
    appbIncidence M (r.vertex 2) (r.edge (appbFourEmbedding (appb_s32_kind_length k hk) j)).val =
      (if j < 2 then 1 else 0) := by
  have ht : ∀ k ∈ appbS32Kinds,1 ∈ k.pattern.vertices ∧ 2 ∈ k.pattern.vertices := by decide
  rw [r.edge_incidence _ 1 (ht k hk).1,r.edge_incidence _ 2 (ht k hk).2]
  simp only [appbS32Kinds,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  all_goals fin_cases j <;> norm_num [appbFourEmbedding,AppbPatternKind.pattern,finCongr,Fin.lt_def]

def appbS32Frame {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbS32Kinds)
    (r : AppbRealization M k.pattern) : AppbTripleFrame r (r.vertex 1) where
  index := (⟨![2,3,0],by decide⟩ : Fin 3 ↪ Fin 4).trans (appbFourEmbedding (appb_s32_kind_length k hk))
  incidence := by
    intro j
    change appbIncidence M (r.vertex 1) (r.edge (appbFourEmbedding (appb_s32_kind_length k hk) (![2,3,0] j))).val = 1
    rw [(appb_s32_incidence_table k hk r _).1]
    fin_cases j <;> decide
  other := by
    intro i hn
    obtain ⟨j,rfl⟩ := (finCongr (appb_s32_kind_length k hk).symm).surjective i
    change appbIncidence M (r.vertex 1) (r.edge (appbFourEmbedding (appb_s32_kind_length k hk) j)).val = 0
    rw [(appb_s32_incidence_table k hk r j).1]
    fin_cases j
    · exact False.elim (hn 2 rfl)
    · decide
    · exact False.elim (hn 0 rfl)
    · exact False.elim (hn 1 rfl)

def appbS32Pair {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbS32Kinds)
    (r : AppbRealization M k.pattern) : AppbLocalPair r (r.vertex 2) where
  first := appbFourEmbedding (appb_s32_kind_length k hk) 0
  second := appbFourEmbedding (appb_s32_kind_length k hk) 1
  distinct := fun he => (by decide : (0 : Fin 4) ≠ 1) ((appbFourEmbedding _).injective he)
  incidence_first := (appb_s32_incidence_table k hk r 0).2
  incidence_second := (appb_s32_incidence_table k hk r 1).2
  incidence_other := by
    intro i h0 h1
    obtain ⟨j,rfl⟩ := (finCongr (appb_s32_kind_length k hk).symm).surjective i
    change appbIncidence M (r.vertex 2) (r.edge (appbFourEmbedding (appb_s32_kind_length k hk) j)).val = 0
    rw [(appb_s32_incidence_table k hk r j).2]
    fin_cases j
    · exact False.elim (h0 rfl)
    · exact False.elim (h1 rfl)
    · decide
    · decide

theorem appb_s32_projection_injective {M : Molecule V D} (k : AppbPatternKind) (hk : k ∈ appbS32Kinds)
    (r : AppbRealization M k.pattern) {d : ℕ} (p : AppbCountParameters M d) {L : ℝ} (hL : 0 < L)
    (γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) :
    Set.InjOn ((appbS32Frame k hk r).project (K := Fin d → ℤ)) (r.localChoices p hL γ δ w Adm : Set _) := by
  intro q hq q' hq' he
  obtain ⟨κ,hκ,rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q).mp hq
  obtain ⟨κ',hκ',rfl⟩ := (r.mem_localChoices p hL γ δ w Adm q').mp hq'
  have ht : ∀ k ∈ appbS32Kinds,2 ∈ k.pattern.removed := by decide
  have hv := mem_image_of_mem r.vertex (ht k hk)
  have hz := congrFun he (2 : Fin 3)
  have hrest := ((appbS32Pair k hk r).singletonCut hv).second_label_eq hL.ne' w p.momentum κ κ' hκ.1 hκ'.1 hz
  funext i
  obtain ⟨j,rfl⟩ := (finCongr (appb_s32_kind_length k hk).symm).surjective i
  fin_cases j
  · exact hz
  · exact hrest
  · exact congrFun he (0 : Fin 3)
  · exact congrFun he (1 : Fin 3)

end WaveTurbulence.Mole
