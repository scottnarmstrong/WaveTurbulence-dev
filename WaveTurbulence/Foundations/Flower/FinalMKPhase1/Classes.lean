/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.NodeFacts

/-! # C1b1 MK-PHASE1 (3): the node classes of the survivor Step 1

The phase-1 node families of the LOW cover (vine nodes `nodes1`, triple nodes `nodesT`, D1 nodes `nodes1D`, on
`C.toCollData`) keep main's state-level node data; only the class restriction changes:

* **collected nodes** `AvineF`: main's `Avine` (LowChain/AsmPhase1) with the forbidden-pool collection `CollectedF`;
* **survivor nodes** `AvineS`: every vine cut with the node data removes the survivor `E i` (ancestor-matched,
  `SurvCut`), in the removal order (`SurvOrder`). This does not depend on the decoration. The vine and D1 classes use
  `AvineE = AvineF ∪ AvineS`;
* **triple nodes** `AtripE`: every `CollectedF` object and every survivor dartless (the `triple` constructor);
* **re-cut nodes** (`Node1RC`, NodeFacts): class `cls1D` on `AvineS`.

For each family a decoration of the class makes a step of `HStep1RLE` (`hstep1RLE_vine/_D1/_trip/_RC`). -/

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

section classes
variable {M₀ : Molecule V D₀} {m : ℕ}

/-- Main's `Avine` with the forbidden-pool collection: the decorations of `A` for which some `CollectedF` object `U` has
exactly the atoms of every vine cut with these data, in the first-stage order. -/
def AvineF [Infinite V] (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (x₁ x₂ y₁ y₂ : h.s.D) :
    Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧ ∃ U : Object M₀, CollectedF C (Un k) L γ η w k U ∧
    (∀ K : VineCut h.s.M, K.x₁ = x₁ → K.x₂ = x₂ → K.y₁ = y₁ → K.y₂ = y₂ → K.fa = fresh3 h 0 → K.fb = fresh3 h 1 →
      U.atoms = K.C.atoms) ∧
    (U.ContainsDart (h.s.down x₁) ∧ U.ContainsDart (h.s.down x₂) ∧ U.ContainsDart (h.s.down y₁) ∧
      U.ContainsDart (h.s.down y₂)) ∧
    ((M₀.atom (h.s.down x₁) = U.upper ∧ M₀.atom (h.s.down y₁) = U.lower) ∨
      (M₀.atom (h.s.down x₁) = U.lower ∧ M₀.atom (h.s.down y₁) = U.upper)) ∧
    (U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' h)}

/-- The decorations of `A` (all or none) for which the node data cut a survivor in the removal order. -/
def AvineS [Infinite V] (E : Fin m → Object M₀) (Fst : Set (Object M₀)) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ)))
    (x₁ x₂ y₁ y₂ : h.s.D) : Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧ ∃ i, (∀ K : VineCut h.s.M, K.x₁ = x₁ → K.x₂ = x₂ → K.y₁ = y₁ → K.y₂ = y₂ → K.fa = fresh3 h 0 →
    K.fb = fresh3 h 1 → SurvCut E i h K) ∧ SurvOrder Fst E i h}

/-- The vine/D1 class restriction with survivors: a collected object (`AvineF`) or a survivor. -/
def AvineE [Infinite V] (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (E : Fin m → Object M₀) (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ)))
    (x₁ x₂ y₁ y₂ : h.s.D) : Set (D₀ → (Fin d → ℤ)) :=
  AvineF C Un Fst L γ η w h A x₁ x₂ y₁ y₂ ∪ AvineS E Fst h A x₁ x₂ y₁ y₂

/-- The triple-cut class restriction with survivors: every `CollectedF` object and every survivor dartless. -/
def AtripE (C : CollDataMK M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (E : Fin m → Object M₀) (L γ η : ℝ)
    (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) : Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧ (∀ U, CollectedF C (Un k) L γ η w k U → Dartless U h) ∧ ∀ i, Dartless (E i) h}

variable {C : CollDataMK M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)}
  {E : Fin m → Object M₀} {crit : V → Prop} {L γ η : ℝ} {w : Mom d}

theorem AvineS_sub [Infinite V] {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {x₁ x₂ y₁ y₂ : h.s.D} :
    AvineS E Fst h A x₁ x₂ y₁ y₂ ⊆ A := fun _ hk => hk.1

theorem AvineE_sub [Infinite V] {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {x₁ x₂ y₁ y₂ : h.s.D} :
    AvineE C Un Fst E L γ η w h A x₁ x₂ y₁ y₂ ⊆ A := by
  rintro k (hk | hk)
  · exact hk.1
  · exact hk.1

theorem AtripE_sub {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} : AtripE C Un E L γ η w h A ⊆ A := fun _ hk => hk.1

/-- **A vine node on `AvineE` is a survivor Step-1 step**: `HStep1RLE.vine` (collected object) or `survVine`. -/
theorem hstep1RLE_vine [Infinite V] {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {t : T1 h}
    (hn : Node1 C.toCollData crit L γ η h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1 L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2.1)
      t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2.1 t.2.2.2.2.2.2.2) :
    HStep1RLE C Un Fst E L γ η w κ h (post1 C.toCollData crit L γ η h t) := by
  obtain ⟨hkA, hrest⟩ := hk
  have hC := hstep1C_node (A := A) hn ⟨AvineE_sub hkA, hrest⟩
  obtain ⟨x₁, x₂, y₁, y₂, z, b, a, sg⟩ := t
  have hspec := Classical.choose_spec hn
  generalize hKd : Classical.choose hn = K at hspec
  obtain ⟨e1, e2, e3, e4, e5, e6, -⟩ := hspec
  simp only at e1 e2 e3 e4 hkA
  have hpost : post1 C.toCollData crit L γ η h (x₁, x₂, y₁, y₂, z, b, a, sg) =
      h.vinePost K ((2 : ℝ) ^ z) (if b then 50 else 0) := by
    unfold post1
    rw [dite_eq_left hn, hKd]
  rw [hpost] at hC ⊢
  rcases hkA with hv | hs
  · obtain ⟨-, U, hU, hUK, hUD, hUJ, hord⟩ := hv
    subst e1 e2 e3 e4
    exact HStep1RLE.vine h K _ _ hC U hU (hUK K rfl rfl rfl rfl e5 e6) hUD hUJ hord
  · obtain ⟨-, i, hcut, hord⟩ := hs
    exact HStep1RLE.survVine h K _ _ i hC (hcut K e1 e2 e3 e4 e5 e6) hord

/-- **A D1 node on `AvineE` is a survivor Step-1 step**: `HStep1RLE.d1` (collected object) or `survD1`. -/
theorem hstep1RLE_D1 [Infinite V] {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h}
    (hn : Node1D C.toCollData crit h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1D L γ η w h (AvineE C Un Fst E L γ η w h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) :
    HStep1RLE C Un Fst E L γ η w κ h (post1D C.toCollData crit h t) := by
  obtain ⟨hkA, hrest⟩ := hk
  have hC := hstepD1_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn ⟨AvineE_sub hkA, hrest⟩
  obtain ⟨K, -, hK, e1, e2, e3, e4, e5, e6⟩ := node1D_spec hn
  rw [hK] at hC ⊢
  rcases hkA with hv | hs
  · obtain ⟨-, U, hU, hUK, hUD, hUJ, hord⟩ := hv
    obtain ⟨x₁, x₂, y₁, y₂⟩ := t
    simp only at e1 e2 e3 e4 hUK hUD hUJ hord
    have hUK' := hUK K e1 e2 e3 e4 e5 e6
    subst e1 e2 e3 e4
    exact HStep1RLE.d1 h K hC U hU hUK' hUD hUJ hord
  · obtain ⟨-, i, hcut, hord⟩ := hs
    exact HStep1RLE.survD1 h K i hC (hcut K e1 e2 e3 e4 e5 e6) hord

/-- **A triple node on `AtripE` is a survivor Step-1 step** (the `triple` constructor). -/
theorem hstep1RLE_trip [Infinite V] {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {t : T3 h}
    (hn : NodeT C.toCollData L γ η h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls3 L γ η w h (AtripE C Un E L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) :
    HStep1RLE C Un Fst E L γ η w κ h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) := by
  have hb := hstep1C_triple_both hn.1 hn.2 hk
  exact HStep1RLE.triple h _ hb.1 hb.2 hk.1.2.1 hk.1.2.2 (post3_F_le hn.1 hn.2)

/-- **A re-cut node on `AvineS` is a survivor Step-1 step** (`survRC`). -/
theorem hstep1RLE_RC [Infinite V] {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {t : T1D h}
    (hn : Node1RC C.toCollData crit E L γ η h t) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls1D L γ η w h (AvineS E Fst h A t.1 t.2.1 t.2.2.1 t.2.2.2) t.1 t.2.1 t.2.2.1 t.2.2.2) :
    HStep1RLE C Un Fst E L γ η w κ h (post1RC C.toCollData crit E L γ η h t) := by
  have hC := hstepRC_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn ⟨hk.1.1, hk.2⟩
  obtain ⟨⟨-, i, hcut, hord⟩, -⟩ := hk
  obtain ⟨K, -, hK, e1, e2, e3, e4, e5, e6⟩ := nodeRC_spec hn
  rw [hK] at hC ⊢
  exact HStep1RLE.survRC h K i hC (hcut K e1 e2 e3 e4 e5 e6) hord

end classes

end WaveTurbulence.Flower.FinalMKPhase1
