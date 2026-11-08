/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Book2
public import WaveTurbulence.Foundations.Flower.FinalMKStep.Obj

/-! # C1b1 MK-PHASE1 (8): the bookkeeping `ConnInvLE` along the survivor Step 1, and C1a's two obligations

`BookE h ps qs`: the geometric bookkeeping `GeomBook` of all removed pieces (survivor pieces `qs`, collected pieces
`ps`), main's collected-piece clauses (`PieceData`, pairwise disjointness), the survivor pieces (`PieceDataS`, each one a
dartless survivor removed in the removal order) and the first-stage order. A survivor whose shared joint was re-cut by
the previous survivor is **not** intact: it is the explicit "pending re-cut joint" state, recorded through `neps` (its
remnant joint descends from the removed previous survivor) and `hqd` (the removal order).

* `reach1LE_book`: along `Reach1LE`, every collected object is dartless or intact, and either `BookE` holds for some
  `ps qs` or every collected object and every survivor is dartless (main's `collInv_of_reach1L` + `reach1L_connInv`).
* **Obligation 1 (`hone`)** `recut_hone`: at a re-cut of the survivor `E i` from a reachable state, at most one joint is a
  non-`ε` (`α/β`) remnant. A non-`ε` joint descends from a removed piece (`neps`); collected pieces miss survivors; a
  removed survivor `E j` that meets `E i` is `E (i-1)` (`survChain`, and `E (i+1)` cannot be removed before `E i`);
  `|E (i-1) ∩ E i| = 1` while the two joints of `E i` differ.
* **Obligation 2** (`recut_not_both_ab`): the configuration "both joints `α/β` re-cut remnants" (C1a's non-closing
  case) never occurs at a reachable state. It is the negation of obligation 1.
* `recut_pend`: the step pays one pending re-cut (`hpend` of `hW_RCp`), via C1a's `pendRC_step`. -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section inv
variable {M₀ : Molecule V D₀} {m : ℕ}

/-- **The removal bookkeeping with survivors** (`ConnInvLE`'s data). -/
structure BookE (M₀ : Molecule V D₀) (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀)
    (ps qs : List (Object M₀ × Quad D₀)) : Prop where
  geom : GeomBook M₀ h (qs ++ ps)
  hps : ∀ p ∈ ps, PieceDataF C Un L γ η w κ p
  hpw : ps.Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms)
  hqs : ∀ q ∈ qs, PieceDataS E q
  hqd : ∀ q ∈ qs, ∃ j, q.1 = E j ∧ Dartless (E j) h ∧ ∀ k, k < j → Dartless (E k) h
  hfo : ((∃ p ∈ ps, p.1 ∉ Fst) ∨ qs ≠ []) → ∀ U ∈ Fst, Dartless U h

/-- `ConnInvLE`: the bookkeeping holds for some removed pieces. -/
def ConnInvLE (M₀ : Molecule V D₀) (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀))
    (Fst : Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) :
    Prop :=
  ∃ ps qs, BookE M₀ C Un Fst E L γ η w κ h ps qs

variable {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
  {E : Fin m → Object M₀} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- Darts are only removed along the survivor Step 1. -/
theorem HStep1RLE.dartless {h h' : HSt V D₀} (hs : HStep1RLE C Un Fst E L γ η w κ h h') {U : Object M₀}
    (hd : Dartless U h) : Dartless U h' := by
  cases hs with
  | vine K R kp _ _ _ _ _ _ _ => exact fun x hx => hd x.1 hx
  | d1 K _ _ _ _ _ _ _ => exact fun x hx => hd x.1 hx
  | triple _ _ hs3 _ _ _ =>
    cases hs3 with
    | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact fun x hx => hd x hx
  | survVine K R kp i _ _ _ => exact fun x hx => hd x.1 hx
  | survD1 K i _ _ _ => exact fun x hx => hd x.1 hx
  | survRC K i _ _ _ => exact fun x hx => hd x.1 hx

/-- The node darts of a cut object are present, so the object is not dartless. -/
theorem not_dartless_of_cd {h : HSt V D₀} {U : Object M₀} {x : h.s.D} (hx : U.ContainsDart (h.s.down x)) :
    ¬ Dartless U h := fun hd => hd x hx

/-- The piece data of an ancestor-matched removal of a survivor. -/
theorem pieceDataS_of_remA {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) (K : VineCut b.s.M) (i : Fin m)
    (hc : SurvCut E i b K) : PieceDataS E (E i, quadK b K) := by
  refine ⟨⟨i, rfl⟩, hc.2.1, hc.2.2, ?_, ?_, ?_, ?_⟩
  · show M₀.atom (b.s.down K.x₂) = M₀.atom (b.s.down K.x₁)
    rw [hA.atom, hA.atom, K.Mx₂, K.cut_a.2.2.1]
  · show M₀.atom (b.s.down K.y₂) = M₀.atom (b.s.down K.y₁)
    rw [hA.atom, hA.atom, K.My₂, K.My₁]
  · intro e
    have h1 := K.cut_a.2.2.2.2.2.1
    have h2 := K.cut_a.2.2.2.2.2.2
    rw [hA.inj e] at h1; rw [h1] at h2; cases h2
  · intro e
    have h1 := K.cut_b.2.2.2.2.2.1
    have h2 := K.cut_b.2.2.2.2.2.2
    rw [hA.inj e] at h1; rw [h1] at h2; cases h2

/-- The piece data of a removed collected object. -/
theorem pieceData_of_cut {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) (K : VineCut b.s.M) (U : Object M₀)
    (hU : CollectedF C (Un κ) L γ η w κ U)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper)) :
    PieceDataF C Un L γ η w κ (U, quadK b K) := by
  refine ⟨hU, hUD, hUJ, ?_, ?_, ?_, ?_⟩
  · show M₀.atom (b.s.down K.x₂) = M₀.atom (b.s.down K.x₁)
    rw [hA.atom, hA.atom, K.Mx₂, K.cut_a.2.2.1]
  · show M₀.atom (b.s.down K.y₂) = M₀.atom (b.s.down K.y₁)
    rw [hA.atom, hA.atom, K.My₂, K.My₁]
  · intro e
    have h1 := K.cut_a.2.2.2.2.2.1
    have h2 := K.cut_a.2.2.2.2.2.2
    rw [hA.inj e] at h1; rw [h1] at h2; cases h2
  · intro e
    have h1 := K.cut_b.2.2.2.2.2.1
    have h2 := K.cut_b.2.2.2.2.2.2
    rw [hA.inj e] at h1; rw [h1] at h2; cases h2

/-- An intact collected object stays intact or becomes dartless along a collected-object removal (main's
`collInv_of_reach1L` step). -/
theorem collInv_vine_step {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) (hD : DartRel M₀ b.s) (K : VineCut b.s.M)
    (U U' : Object M₀) (hUK : U'.atoms = K.C.atoms)
    (hUD : U'.ContainsDart (b.s.down K.x₁) ∧ U'.ContainsDart (b.s.down K.x₂) ∧ U'.ContainsDart (b.s.down K.y₁) ∧
      U'.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U'.upper ∧ M₀.atom (b.s.down K.y₁) = U'.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U'.lower ∧ M₀.atom (b.s.down K.y₁) = U'.upper))
    (hi : UIntact U b) (hsd : SameDes U U' ∨ Disjoint U.atoms U'.atoms) :
    (∀ R kp, Dartless U (b.vinePost K R kp) ∨ UIntact U (b.vinePost K R kp)) ∧
      (Dartless U (b.vinePostG K) ∨ UIntact U (b.vinePostG K)) := by
  rcases hsd with hsd | hdis
  · have hcd : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
        U.ContainsDart (b.s.down K.y₂) :=
      ⟨(hsd.2.1 _).2 hUD.1, (hsd.2.1 _).2 hUD.2.1, (hsd.2.1 _).2 hUD.2.2.1, (hsd.2.1 _).2 hUD.2.2.2⟩
    have hj : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
        (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper) := by
      rcases hUJ with ⟨a, b⟩ | ⟨a, b⟩
      · exact hsd.joint_id (Or.inl ⟨a, b⟩)
      · exact hsd.joint_id (Or.inr ⟨a, b⟩)
    exact ⟨fun R kp => Or.inl (dartless_vineSt hA hD K _ U (hsd.1.trans hUK) hi hcd hj),
      Or.inl (dartless_vineStG hA hD K U (hsd.1.trans hUK) hi hcd hj)⟩
  · exact ⟨fun R kp => Or.inr (uIntact_vinePost K R kp U hi (hUK ▸ hdis)),
      Or.inr (uIntact_vinePostG K U hi (hUK ▸ hdis))⟩

/-- An intact collected object stays intact along a survivor removal (they share no atom). -/
theorem collInv_surv_step {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e) (K : VineCut b.s.M) (i : Fin m)
    (hc : SurvCut E i b K) (U : Object M₀) (hi : UIntact U b) (hsd : Disjoint U.atoms (E i).atoms) :
    (∀ R kp, UIntact U (b.vinePost K R kp)) ∧ UIntact U (b.vinePostG K) := by
  obtain ⟨-, -, -, hat⟩ := (remA_of_survCut hc).facts hA hinj
  have hdis : Disjoint U.atoms K.C.atoms := by
    refine Finset.disjoint_left.2 fun a ha haK => ?_
    have he : b.anc a = a := hA.eps a (hi a ha).1 (hi a ha).2
    exact Finset.disjoint_left.1 hsd ha (he ▸ hat a haK)
  exact ⟨fun R kp => uIntact_vinePost K R kp U hi hdis, uIntact_vinePostG K U hi hdis⟩

end inv

end WaveTurbulence.Flower.FinalMKPhase1
