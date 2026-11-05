/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.EnhancedDraft.Encoded

/-!
# Dominant couples ↔ encoded trees (DH21 Prop 4.23, L892–L895)

* `encCode_spec`: `cplEnc (encCode T) = T`, and `encCode T` is a well-formed dominant code
  (`encCode_good`); hence **the map `𝒬 ↦ 𝒯(𝒬)` is onto** (`cplEnc_surjective`);
* `DomCpl`: well-formed dominant couple codes, with DH21's equivalence for `Z = ∅`
  (`DomCpl.equiv_iff_enh`: it is the equivalence of the enhanced couples `(𝒬, ∅)`);
* **`𝒬 ~ 𝒬'` iff `𝒯(𝒬) ~ 𝒯(𝒬')`** (`domCpl_equiv_iff_enc`), and the induced map of classes is a
  bijection (`domClassEquiv`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg EncTree

/-- Well-formed and dominant. -/
def Good (Q : RegCpl) : Prop := Q.wf = true ∧ Q.dominant = true

theorem chainOfList_good : (L : List (MiniTreeCode × RegCpl × RegCpl)) →
    (∀ x ∈ L, Good x.2.1 ∧ Good x.2.2) →
    (chainOfList L).wf = true ∧ (chainOfList L).dominant = true
  | [], _ => ⟨rfl, rfl⟩
  | (m, qr, qg) :: L, h => by
    have hL := chainOfList_good L fun x hx => h x (List.mem_cons_of_mem _ hx)
    have hx := h (m, qr, qg) List.mem_cons_self
    simp only [chainOfList, RegChain.wf, RegChain.dominant, RegChain.isNil, Bool.and_eq_true]
    simp [hx.1.1, hx.2.1, hx.1.2, hx.2.2, hL.1, hL.2]

theorem assemble_cons (x : MiniTreeCode × RegCpl × RegCpl) (L : List (MiniTreeCode × RegCpl × RegCpl))
    (q : RegCpl) : assemble (x :: L, q) = .type2 (chainOfList (x :: L)) .nil q := rfl

theorem assemble_good (L : List (MiniTreeCode × RegCpl × RegCpl)) (q : RegCpl)
    (hL : ∀ x ∈ L, Good x.2.1 ∧ Good x.2.2) (hq : Good q) (ht : q.isType2 = false) :
    Good (assemble (L, q)) := by
  cases L with
  | nil => exact hq
  | cons x L =>
    rw [assemble_cons]
    have hc := chainOfList_good (x :: L) hL
    obtain ⟨m, qr, qg⟩ := x
    simp only [Good, RegCpl.wf, RegCpl.dominant, RegChain.wf, RegChain.dominant, chainOfList,
      RegChain.isNil, ht, hq.1, hq.2, Bool.and_eq_true, Bool.and_true, Bool.not_false,
      true_and] at hc ⊢
    exact ⟨hc.1, hc.2⟩

/-- `encCode T` is well formed and dominant; its chain data are good and its tail is not of
type 2. -/
theorem encCode_good : (T : EncTree) →
    Good (encCode T) ∧ (∀ x ∈ (encCodeAux T).1, Good x.2.1 ∧ Good x.2.2) ∧
      Good (encCodeAux T).2 ∧ (encCodeAux T).2.isType2 = false
  | .leaf => ⟨⟨rfl, rfl⟩, by simp [encCodeAux], ⟨rfl, rfl⟩, rfl⟩
  | .node .c0 a b c => by
    have ha := (encCode_good a).1
    have hb := (encCode_good b).1
    have hc := (encCode_good c).1
    have h1 : Good (.type1 0 (encCode a) (encCode b) (encCode c)) := by
      simp only [Good, RegCpl.wf, RegCpl.dominant, Bool.and_eq_true] at ha hb hc ⊢
      exact ⟨⟨⟨ha.1, hb.1⟩, hc.1⟩, ⟨⟨ha.2, hb.2⟩, hc.2⟩⟩
    exact ⟨h1, by simp [encCodeAux], h1, rfl⟩
  | .node .c1 t a b => by
    obtain ⟨-, hl, hq, ht⟩ := encCode_good t
    have hx : ∀ x ∈ (encCodeAux (.node .c1 t a b)).1, Good x.2.1 ∧ Good x.2.2 := by
      intro x hx
      simp only [encCodeAux, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨(encCode_good a).1, (encCode_good b).1⟩
      · exact hl x hx
    exact ⟨assemble_good _ _ hx hq ht, hx, hq, ht⟩
  | .node .c2 a t b => by
    obtain ⟨-, hl, hq, ht⟩ := encCode_good t
    have hx : ∀ x ∈ (encCodeAux (.node .c2 a t b)).1, Good x.2.1 ∧ Good x.2.2 := by
      intro x hx
      simp only [encCodeAux, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨(encCode_good a).1, (encCode_good b).1⟩
      · exact hl x hx
    exact ⟨assemble_good _ _ hx hq ht, hx, hq, ht⟩
  | .node .c3 a b t => by
    obtain ⟨-, hl, hq, ht⟩ := encCode_good t
    have hx : ∀ x ∈ (encCodeAux (.node .c3 a b t)).1, Good x.2.1 ∧ Good x.2.2 := by
      intro x hx
      simp only [encCodeAux, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨(encCode_good a).1, (encCode_good b).1⟩
      · exact hl x hx
    exact ⟨assemble_good _ _ hx hq ht, hx, hq, ht⟩

theorem chainEnc_cons (m : MiniTreeCode) (qr qg : RegCpl) (L : List (MiniTreeCode × RegCpl × RegCpl))
    (t : EncTree) : chainEnc (chainOfList ((m, qr, qg) :: L)) t =
      encNode m.c (cplEnc qr) (cplEnc qg) (chainEnc (chainOfList L) t) := rfl

theorem cplEnc_assemble (L : List (MiniTreeCode × RegCpl × RegCpl)) (q : RegCpl) :
    cplEnc (assemble (L, q)) = chainEnc (chainOfList L) (cplEnc q) := by
  cases L with
  | nil => rfl
  | cons x L => rw [assemble_cons]; rfl

/-- **`𝒯(encCode T) = T`.** -/
theorem encCode_spec : (T : EncTree) →
    chainEnc (chainOfList (encCodeAux T).1) (cplEnc (encCodeAux T).2) = T ∧ cplEnc (encCode T) = T
  | .leaf => ⟨rfl, rfl⟩
  | .node .c0 a b c => by
    have e : chainEnc (chainOfList (encCodeAux (.node .c0 a b c)).1)
        (cplEnc (encCodeAux (.node .c0 a b c)).2) = .node .c0 a b c := by
      show EncTree.node .c0 (cplEnc (encCode a)) (cplEnc (encCode b)) (cplEnc (encCode c)) = _
      rw [(encCode_spec a).2, (encCode_spec b).2, (encCode_spec c).2]
    exact ⟨e, by rw [encCode, cplEnc_assemble]; exact e⟩
  | .node .c1 t a b => by
    have e : chainEnc (chainOfList (encCodeAux (.node .c1 t a b)).1)
        (cplEnc (encCodeAux (.node .c1 t a b)).2) = .node .c1 t a b := by
      show chainEnc (chainOfList ((⟨0, 0⟩, encCode a, encCode b) :: (encCodeAux t).1))
        (cplEnc (encCodeAux t).2) = _
      rw [chainEnc_cons, (encCode_spec t).1, (encCode_spec a).2, (encCode_spec b).2]
      rfl
    exact ⟨e, by rw [encCode, cplEnc_assemble]; exact e⟩
  | .node .c2 a t b => by
    have e : chainEnc (chainOfList (encCodeAux (.node .c2 a t b)).1)
        (cplEnc (encCodeAux (.node .c2 a t b)).2) = .node .c2 a t b := by
      show chainEnc (chainOfList ((⟨1, 0⟩, encCode a, encCode b) :: (encCodeAux t).1))
        (cplEnc (encCodeAux t).2) = _
      rw [chainEnc_cons, (encCode_spec t).1, (encCode_spec a).2, (encCode_spec b).2]
      rfl
    exact ⟨e, by rw [encCode, cplEnc_assemble]; exact e⟩
  | .node .c3 a b t => by
    have e : chainEnc (chainOfList (encCodeAux (.node .c3 a b t)).1)
        (cplEnc (encCodeAux (.node .c3 a b t)).2) = .node .c3 a b t := by
      show chainEnc (chainOfList ((⟨2, 0⟩, encCode a, encCode b) :: (encCodeAux t).1))
        (cplEnc (encCodeAux t).2) = _
      rw [chainEnc_cons, (encCode_spec t).1, (encCode_spec a).2, (encCode_spec b).2]
      rfl
    exact ⟨e, by rw [encCode, cplEnc_assemble]; exact e⟩

/-! ### The equivalence classes -/

/-- Well-formed dominant couple codes. -/
abbrev DomCpl : Type := {Q : RegCpl // Good Q}

/-- **DH21's equivalence of dominant couples** (Def 4.18 with `Z = ∅`). -/
instance DomCpl.setoid : Setoid DomCpl where
  r q q' := Shape.Equiv (cplShape0 q.1) (cplShape0 q'.1)
  iseqv := ⟨fun _ => Shape.equiv_refl _, Shape.Equiv.symm, Shape.Equiv.trans⟩

/-- A dominant couple as the enhanced couple `(𝒬, ∅)`. -/
def DomCpl.toEnh (q : DomCpl) : EnhCpl :=
  ⟨q.1, q.2.1, q.2.2, ∅, (mem_specialSets_iff _ _).2 (by simp)⟩

/-- `𝒬 ~ 𝒬'` means `(𝒬, ∅) ~ (𝒬', ∅)` (DH21 L873). -/
theorem DomCpl.equiv_iff_enh (q q' : DomCpl) : q ≈ q' ↔ q.toEnh ≈ q'.toEnh := by
  show _ ↔ Shape.Equiv (cplShape ∅ q.1 (0, []) (1, [])) (cplShape ∅ q'.1 (0, []) (1, []))
  rw [cplShape_empty, cplShape_empty]
  rfl

/-- **DH21 Prop 4.23 (1): the map from dominant couples to encoded trees is onto.** -/
theorem cplEnc_surjective (T : EncTree) : ∃ q : DomCpl, cplEnc q.1 = T :=
  ⟨⟨encCode T, (encCode_good T).1⟩, (encCode_spec T).2⟩

/-- **DH21 Prop 4.23 (2): `𝒬 ~ 𝒬'` iff `𝒯(𝒬) ~ 𝒯(𝒬')`.** -/
theorem domCpl_equiv_iff_enc (q q' : DomCpl) : q ≈ q' ↔ cplEnc q.1 ≈ cplEnc q'.1 := by
  show _ ↔ Shape.Equiv (cplEnc q.1).shape (cplEnc q'.1).shape
  rw [shape_cplEnc q.1 q.2.1, shape_cplEnc q'.1 q'.2.1]
  rfl

/-- **DH21 Prop 4.23 (3): the classes of dominant couples correspond bijectively to the classes of
encoded trees.** -/
noncomputable def domClassEquiv : Quotient DomCpl.setoid ≃ Quotient EncTree.setoid :=
  Equiv.ofBijective
    (Quotient.map (fun q : DomCpl => cplEnc q.1) fun q q' h => (domCpl_equiv_iff_enc q q').1 h)
    ⟨by
      intro x y hxy
      induction x using Quotient.inductionOn with | h q => ?_
      induction y using Quotient.inductionOn with | h q' => ?_
      simp only [Quotient.map_mk] at hxy
      exact Quotient.sound ((domCpl_equiv_iff_enc q q').2 (Quotient.exact hxy)),
    by
      intro y
      induction y using Quotient.inductionOn with | h T => ?_
      obtain ⟨q, hq⟩ := cplEnc_surjective T
      exact ⟨⟦q⟧, by simp only [Quotient.map_mk, hq]⟩⟩

theorem domClassEquiv_mk (q : DomCpl) : domClassEquiv ⟦q⟧ = ⟦cplEnc q.1⟧ := rfl

end WaveTurbulence.Links
