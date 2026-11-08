/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Cov4

/-! # C1b1 MK-PHASE1 (18): the explicit "intact or pending re-cut joint" status of a survivor

LOW's invariant "every collected object is dartless or intact" (LowChain21) does not hold for survivors: after
`E (i-1)` is removed, `E i` has one **pending re-cut joint**. `BookE.surv_status` states the survivor version from the
bookkeeping `BookE`: a survivor `E i` that is not dartless, all of whose predecessors are dartless, is intact, or it is
pending: exactly one atom `v` of `E i` (a joint of `E i`, the atom shared with the removed `E (i-1)`) is represented by
a non-`ε` remnant `r` (`anc r = v`), and every other atom of `E i` is a present `ε`-atom. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

variable {V : Type*} [DecidableEq V] {D₀ : Type} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section status
variable {M₀ : Molecule V D₀} {m : ℕ} {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
  {Fst : Set (Object M₀)} {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- **The survivor status: intact, or one pending re-cut joint.** -/
theorem BookE.surv_status {Rn : ℕ} (hS : SubHypL Rn M₀) {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc)
    {ps qs : List (Object M₀ × Quad D₀)} (B : BookE M₀ C Un Fst E L γ η w κ h ps qs)
    (hsd : ∀ U, CollectedF C (Un κ) L γ η w κ U → ∀ i, Disjoint U.atoms (E i).atoms)
    (hchain : ∀ i j, i ≠ j → ¬ Disjoint (E i).atoms (E j).atoms →
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ ((E i).atoms ∩ (E j).atoms).card = 1)
    {i : Fin m} (hi : ¬ Dartless (E i) h) :
    UIntact (E i) h ∨ ∃ (j : Fin m) (v r : V), j.val + 1 = i.val ∧ v ∈ (E j).atoms ∩ (E i).atoms ∧
      (v = (E i).upper ∨ v = (E i).lower) ∧ r ∈ h.s.M.atoms ∧ h.anc r = v ∧ h.s.cls r ≠ .eps ∧
      ∀ a ∈ (E i).atoms, a ≠ v → a ∈ h.s.M.atoms ∧ h.s.cls a = .eps := by
  have hm := B.surv_match hS hsd hchain hi
  -- an atom whose representative is `ε` is itself a present `ε`-atom
  have heps : ∀ a ∈ (E i).atoms, h.s.cls (ancInv h a) = .eps → a ∈ h.s.M.atoms ∧ h.s.cls a = .eps := by
    intro a ha he
    have he' : ancInv h a = a := (hA.eps _ (hm.mem a ha) he).symm.trans (hm.anc a ha)
    rw [he'] at he
    exact ⟨he' ▸ hm.mem a ha, he⟩
  -- an atom whose representative is not `ε` lies in `E (i-1)`
  have hnon : ∀ a ∈ (E i).atoms, h.s.cls (ancInv h a) ≠ .eps →
      ∃ j : Fin m, j.val + 1 = i.val ∧ a ∈ (E j).atoms ∩ (E i).atoms ∧ ((E j).atoms ∩ (E i).atoms).card = 1 := by
    intro a ha hne
    obtain ⟨p, hp, hpa⟩ := B.geom.neps _ (hm.mem a ha) hne
    rw [hm.anc a ha] at hpa
    obtain ⟨j, hj, -, hmem, hcard⟩ := B.piece_meet hsd hchain hi ha hp hpa
    exact ⟨j, hj, hmem, hcard⟩
  by_cases hall : ∀ a ∈ (E i).atoms, h.s.cls (ancInv h a) = .eps
  · exact Or.inl fun a ha => heps a ha (hall a ha)
  · right
    push Not at hall
    obtain ⟨v, hv, hve⟩ := hall
    obtain ⟨j, hj, hvm, hcard⟩ := hnon v hv hve
    have hvj : v = (E i).upper ∨ v = (E i).lower := by
      by_contra hcon
      push Not at hcon
      have hM₀ : M₀.IsMolecule := hS.isMolecule
      obtain ⟨z, hza, hzg⟩ := exists_group_dart (E j) (Finset.mem_inter.1 hvm).1
      have hcd : (E i).ContainsDart z :=
        containsDart_of_interior (E i) (fun c hc => Mole.deg_le_four M₀ hM₀ hc)
          (object_oh (E i)).basic.2.2.2.2.2.2 (hza ▸ hv) (hza ▸ hcon.1) (hza ▸ hcon.2)
      exact not_two_groups hS hcard hzg (containsDart_inGroup _ hcd)
    refine ⟨j, v, ancInv h v, hj, hvm, hvj, hm.mem v hv, hm.anc v hv, hve, fun a ha hav => ?_⟩
    by_cases hae : h.s.cls (ancInv h a) = .eps
    · exact heps a ha hae
    · exfalso
      obtain ⟨j', hj', ham, -⟩ := hnon a ha hae
      have hjj : j' = j := Fin.ext (by omega)
      subst hjj
      exact hav (Finset.card_le_one.1 (le_of_eq hcard) _ ham _ hvm)

end status

end WaveTurbulence.Flower.FinalMKPhase1
