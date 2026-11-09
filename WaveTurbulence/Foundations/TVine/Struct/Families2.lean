/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Struct.Families
import Mathlib.Tactic

/-!
# N2 Theorem 1.15 (F5) for families: the induction (packet L3)

**`families`**: in a T-vine, removing (sources' semantics) any list of pairwise atom-disjoint sub-objects leaves it
connected. Induction on `|G| + |Us|` (N2 L404–L419); see `Struct/Families.lean`.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace WaveTurbulence.TVine.Struct

open Finset TVine Core

universe u

variable {V : Type u} [DecidableEq V]

theorem card_rungDel {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V}
    (hR : IsRungAt G a b xm xp ym yp Km Kp) (μ : Bool) :
    (rungDel G a b xm xp ym yp μ).verts.card + 2 = G.verts.card := by
  rw [hR.verts_rungDel μ]
  have h1 := Finset.card_erase_add_one hR.a_mem
  have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨Ne.symm hR.ne, hR.b_mem⟩)
  omega

theorem phiU_atoms_sub (U : SubObj V) (a b : V) : (phiU U a b).atoms ⊆ U.atoms :=
  (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)

theorem disjoint_of_pairwise {Us : List (SubObj V)} (hdisj : Us.Pairwise (fun U W => Disjoint U.atoms W.atoms))
    {U W : SubObj V} (hU : U ∈ Us) (hW : W ∈ Us) (hne : U ≠ W) : Disjoint U.atoms W.atoms := by
  induction Us with
  | nil => simp at hU
  | cons X Xs ih =>
    obtain ⟨hX, hXs⟩ := List.pairwise_cons.mp hdisj
    rcases List.mem_cons.mp hU with rfl | hU' <;> rcases List.mem_cons.mp hW with rfl | hW'
    · exact absurd rfl hne
    · exact hX W hW'
    · exact (hX U hU').symm
    · exact ih hXs hU' hW'

/-- **N2 Theorem 1.15 (F5) for families, U level.** -/
theorem families (I : Thm115Inputs.{u}) : ∀ (N : ℕ) (G : UMultigraph V) (j₁ j₂ : V) (Us : List (SubObj V)),
    G.verts.card + Us.length = N → IsTVineU G j₁ j₂ → (∀ U ∈ Us, IsSubObjU G U) →
    Us.Pairwise (fun U W => Disjoint U.atoms W.atoms) → Connected (removeAll G Us) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro G j₁ j₂ Us hN hT hsub hdisj
  have hsubA : ∀ U ∈ Us, U.atoms ⊆ G.verts := fun U hU => (hsub U hU).1.subset
  have hl : G.Loopless := loopless_of_isTVineU hT
  by_cases hsmall : G.verts.card ≤ 13
  · exact connected_removeAll_of_removeAllN G Us hsubA hdisj (I.baseFam G j₁ j₂ hT hsmall Us hsub hdisj)
  have hD : 2 ≤ deletableCount G j₁ j₂ := by have := I.size G j₁ j₂ hT; omega
  -- step 1: a member is the double bond of a deletable rung
  have hstep1 : ∀ a b xm xp ym yp : V, ∀ Km Kp : Finset V, IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp →
      ∀ U₀ ∈ Us, U₀.atoms = {a, b} → Connected (removeAll G Us) := by
    intro a b xm xp ym yp Km Kp hDel U₀ hU₀ hA
    obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem hU₀
    have hp : Us.Perm (U₀ :: (l₁ ++ l₂)) := by rw [hsplit]; exact List.perm_middle
    have hdisj0 := hp.pairwise hdisj (fun h => h.symm)
    obtain ⟨hWd, hWp⟩ := List.pairwise_cons.mp hdisj0
    have hWs : ∀ W ∈ (l₁ ++ l₂), IsSubObjU G W := fun W hW => hsub W (hp.mem_iff.mpr (List.mem_cons_of_mem _ hW))
    have hT' := I.del G j₁ j₂ a b xm xp ym yp Km Kp hT hDel false
    have hsubW' : ∀ W ∈ (l₁ ++ l₂), IsSubObjU (rungDel G a b xm xp ym yp false) W := by
      intro W hW
      have haW : a ∉ W.atoms := fun h => Finset.disjoint_left.mp (hWd W hW) (by rw [hA]; simp) h
      have hbW : b ∉ W.atoms := fun h => Finset.disjoint_left.mp (hWd W hW) (by rw [hA]; simp) h
      have hk₁ := k₁_mem (hWs W hW)
      have hk₂ := k₂_mem (hWs W hW)
      have h := I.phiSub G j₁ j₂ a b xm xp ym yp Km Kp W false hT.1 hl hDel.1 (hWs W hW)
        (fun h => haW (h ▸ hk₁)) (fun h => hbW (h ▸ hk₁)) (fun h => haW (h ▸ hk₂)) (fun h => hbW (h ▸ hk₂))
      have h' : W.phi a b = W := phiU_eq_self haW hbW
      rwa [h'] at h
    have hc := card_rungDel hDel.1.1 false
    have hlen : Us.length = (l₁ ++ l₂).length + 1 := by rw [hsplit]; simp; omega
    have hIH := ih ((rungDel G a b xm xp ym yp false).verts.card + (l₁ ++ l₂).length) (by omega) _ j₁ j₂
      (l₁ ++ l₂) rfl hT' hsubW' hWp
    have := step1_transfer hT.1 hDel.1.1 (hsub U₀ hU₀) hA hWs hWd hWp hIH
    rw [removeAll_perm G hp hsubA hdisj]; exact this
  by_cases h3 : ∃ a b xm xp ym yp : V, ∃ Km Kp : Finset V, IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp ∧
      ∀ U ∈ Us, U.k₁ ≠ a ∧ U.k₁ ≠ b ∧ U.k₂ ≠ a ∧ U.k₂ ≠ b
  · -- step 3: a deletable rung with no joint of a member
    obtain ⟨a, b, xm, xp, ym, yp, Km, Kp, hDel, hav⟩ := h3
    have hT' := I.del G j₁ j₂ a b xm xp ym yp Km Kp hT hDel true
    have hsub' : ∀ U' ∈ Us.map (fun U => phiU U a b), IsSubObjU (rungDel G a b xm xp ym yp true) U' := by
      intro U' hU'
      obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hU'
      obtain ⟨h1, h2, h3', h4⟩ := hav U hU
      exact I.phiSub G j₁ j₂ a b xm xp ym yp Km Kp U true hT.1 hl hDel.1 (hsub U hU) h1 h2 h3' h4
    have hdisj' : (Us.map fun U => phiU U a b).Pairwise (fun U W => Disjoint U.atoms W.atoms) := by
      rw [List.pairwise_map]
      exact hdisj.imp fun h =>
        Finset.disjoint_of_subset_left (phiU_atoms_sub _ a b) (Finset.disjoint_of_subset_right (phiU_atoms_sub _ a b) h)
    have hc := card_rungDel hDel.1.1 true
    have hIH := ih ((rungDel G a b xm xp ym yp true).verts.card + (Us.map fun U => phiU U a b).length)
      (by rw [List.length_map]; omega) _ j₁ j₂ _ rfl hT' hsub' hdisj'
    exact I.phiRem G j₁ j₂ a b xm xp ym yp Km Kp Us true hT.1 hl hDel.1 (fun U hU => ⟨hsub U hU, hav U hU⟩) hdisj hIH
  -- otherwise every deletable rung carries a joint of a member
  have hjoint : ∀ a b xm xp ym yp : V, ∀ Km Kp : Finset V, IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp →
      ∃ U ∈ Us, U.k₁ = a ∨ U.k₁ = b ∨ U.k₂ = a ∨ U.k₂ = b := by
    intro a b xm xp ym yp Km Kp hDel
    by_contra hc
    apply h3
    refine ⟨a, b, xm, xp, ym, yp, Km, Kp, hDel, fun U hU => ?_⟩
    by_contra hne
    exact hc ⟨U, hU, by tauto⟩
  -- a side hyper-block member yields a joint-free pendant 2-pole inside it
  have hside : ∀ a b xm xp ym yp : V, ∀ Km Kp : Finset V, IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp →
      ∀ U ∈ Us, (U.k₁ = a ∨ U.k₁ = b ∨ U.k₂ = a ∨ U.k₂ = b) → Connected (removeAll G Us) ∨
        (s(U.k₁, U.k₂) = s(a, b) ∧ ∃ K ⊆ U.atoms, K ⊆ Core.interior G j₁ j₂ ∧ K.Nonempty ∧ cut G K = 2) := by
    intro a b xm xp ym yp Km Kp hDel U hU hin
    have hR := hDel.1.1
    obtain ⟨hs, hcase⟩ := I.joints G j₁ j₂ a b xm xp ym yp Km Kp U hT.1 hl hDel.1 (hsub U hU) hin
    rcases hcase with ⟨-, hA⟩ | ⟨-, hK⟩
    · exact Or.inl (hstep1 a b xm xp ym yp Km Kp hDel U hU hA)
    · right
      refine ⟨hs, ?_⟩
      have hKm : Km ⊆ (G.verts.erase a).erase b := hR.union ▸ Finset.subset_union_left
      have hKp : Kp ⊆ (G.verts.erase a).erase b := hR.union ▸ Finset.subset_union_right
      have hint : ∀ K : Finset V, K ⊆ (G.verts.erase a).erase b → j₁ ∉ K → j₂ ∉ K → K ⊆ Core.interior G j₁ j₂ := by
        intro K hK h1 h2 x hx
        have hxV : x ∈ G.verts := (Finset.mem_erase.mp (Finset.mem_erase.mp (hK hx)).2).2
        exact Finset.mem_erase.mpr ⟨fun h => h2 (h ▸ hx), Finset.mem_erase.mpr ⟨fun h => h1 (h ▸ hx), hxV⟩⟩
      rcases hK with ⟨hA, h1, h2⟩ | ⟨hA, h1, h2⟩
      · exact ⟨Km, by rw [hA]; intro x hx; simp [hx], hint Km hKm h1 h2, ⟨xm, hR.xm_mem⟩,
          RungFacts.cut_Km hR⟩
      · exact ⟨Kp, by rw [hA]; intro x hx; simp [hx], hint Kp hKp h1 h2, ⟨xp, hR.xp_mem⟩,
          RungFacts.cut_Kp hR⟩
  -- two distinct deletable rungs
  classical
  unfold deletableCount at hD
  obtain ⟨z₁, hz₁, z₂, hz₂, hz⟩ := Finset.one_lt_card.mp (Nat.lt_of_lt_of_le (by norm_num : 1 < 2) hD)
  obtain ⟨-, a₁, b₁, rfl, xm₁, xp₁, ym₁, yp₁, Km₁, Kp₁, hDel₁⟩ := Finset.mem_filter.mp hz₁
  obtain ⟨-, a₂, b₂, rfl, xm₂, xp₂, ym₂, yp₂, Km₂, Kp₂, hDel₂⟩ := Finset.mem_filter.mp hz₂
  obtain ⟨U₁, hU₁, hin₁⟩ := hjoint _ _ _ _ _ _ _ _ hDel₁
  obtain ⟨U₂, hU₂, hin₂⟩ := hjoint _ _ _ _ _ _ _ _ hDel₂
  rcases hside _ _ _ _ _ _ _ _ hDel₁ U₁ hU₁ hin₁ with h | ⟨hs₁, K₁, hK₁U, hK₁i, hK₁n, hK₁c⟩
  · exact h
  rcases hside _ _ _ _ _ _ _ _ hDel₂ U₂ hU₂ hin₂ with h | ⟨hs₂, K₂, hK₂U, hK₂i, hK₂n, hK₂c⟩
  · exact h
  exfalso
  have hne : U₁ ≠ U₂ := fun h => hz (by rw [← hs₁, ← hs₂, h])
  have hdU : Disjoint U₁.atoms U₂.atoms := disjoint_of_pairwise hdisj hU₁ hU₂ hne
  exact I.pend G j₁ j₂ K₁ K₂ hT hK₁i hK₂i
    (Finset.disjoint_of_subset_left hK₁U (Finset.disjoint_of_subset_right hK₂U hdU)) hK₁n hK₂n hK₁c hK₂c

end WaveTurbulence.TVine.Struct
