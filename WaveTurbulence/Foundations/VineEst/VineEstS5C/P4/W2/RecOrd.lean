/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecVanish
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecDisp

/-! # P4-W2 (session 14, step 1c): the order atoms of a summand and the engine pairs

`ordRels caseA c`: the list of order atoms `(i, j, strict)` (`value_i ≤/< value_j` among the three slot values `(t₀, s₁, t₁) = (0, 1, 2)`) of `ExcOrd caseA t₀ s₁ t₁ c`
(`excOrd_iff`).  For three slots, each a time variable (`inl`) or the exterior clock (`inr 0`): `ordPairs` is the set of time-variable pairs the atoms need,
`ordBad` says some atom is impossible on the engine domain (first slot exterior with second a time variable, or a strict atom between two exterior slots).
On the engine time domain (`τ s < tt 0` for all `s`, the pairs of `cons`): `ordPairs ⊆ cons ∧ ¬ordBad → ExcOrd` and `ordBad → ¬ExcOrd`
(`excOrd_of_dom`, `not_excOrd_of_dom`).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS5C.P4.W13
open scoped ComplexConjugate

open Classical in
/-- The order atoms of a summand. -/
noncomputable def ordRels (caseA : Prop) {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β} :
    Ch S bs₁ bs₂ rA rB → List (Fin 3 × Fin 3 × Bool) :=
  Sum.elim (Sum.elim (fun _ => if caseA then [(1, 0, false), (0, 2, true)] else [(2, 0, false), (0, 1, true)])
    (Sum.elim (fun _ => [(0, 2, true), (0, 1, true)]) (Sum.elim (fun _ => [(0, 2, true), (0, 1, true)])
    (Sum.elim (fun _ => if caseA then [(2, 0, false), (0, 1, true)] else [(1, 0, false), (0, 2, true)])
    (Sum.elim (fun _ => [(0, 2, true), (0, 1, true)]) (fun _ => [(0, 2, true), (0, 1, true)]))))))
    (Sum.elim (fun _ => [(0, 2, true)]) (fun _ => [(0, 1, true)]))

/-- An order atom between the values of three slots. -/
def relHolds (v : Fin 3 → ℝ) (r : Fin 3 × Fin 3 × Bool) : Prop :=
  if r.2.2 then v r.1 < v r.2.1 else v r.1 ≤ v r.2.1

open Classical in
theorem excOrd_iff (caseA : Prop) {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β} (t0 s1 t1 : ℝ)
    (c : Ch S bs₁ bs₂ rA rB) :
    ExcOrd caseA t0 s1 t1 c ↔ ∀ r ∈ ordRels caseA c, relHolds ![t0, s1, t1] r := by
  rcases c with (c | c | c | c | c | c) | (c | c)
  all_goals
    by_cases hc : caseA
    all_goals
      simp [ExcOrd, ordRels, relHolds, hc]
      try tauto

section Slots
variable {T : Type*}

/-- The pairs of time variables an atom needs. -/
noncomputable def pairOfRel (σ ρ : T ⊕ Fin 3) : Finset (T × T) := by
  classical
  exact match σ, ρ with
    | Sum.inl a, Sum.inl b => {(a, b)}
    | _, _ => ∅

/-- An atom impossible on the engine domain. -/
def relBad (σ ρ : T ⊕ Fin 3) (strict : Bool) : Prop :=
  match σ, ρ with
  | Sum.inr _, Sum.inl _ => True
  | Sum.inr _, Sum.inr _ => strict = true
  | _, _ => False

/-- Exterior slots are the top clock. -/
def SlotWf (σ : T ⊕ Fin 3) : Prop := ∀ j, σ = Sum.inr j → j = 0

open Classical in
/-- The pairs needed by a list of atoms at the slots `σ`. -/
noncomputable def ordPairs (rels : List (Fin 3 × Fin 3 × Bool)) (σ : Fin 3 → T ⊕ Fin 3) : Finset (T × T) :=
  rels.toFinset.biUnion fun r => pairOfRel (σ r.1) (σ r.2.1)

/-- Some atom is impossible. -/
def ordBad (rels : List (Fin 3 × Fin 3 × Bool)) (σ : Fin 3 → T ⊕ Fin 3) : Prop :=
  ∃ r ∈ rels, relBad (σ r.1) (σ r.2.1) r.2.2

theorem relHolds_of_dom (τ : T → ℝ) (tt : Fin 3 → ℝ) (cons : Finset (T × T)) (htop : ∀ s, τ s < tt 0)
    (hcons : ∀ c ∈ cons, τ c.1 < τ c.2) (σ ρ : T ⊕ Fin 3) (hσ : SlotWf σ) (hρ : SlotWf ρ) (strict : Bool)
    (hp : pairOfRel σ ρ ⊆ cons) (hb : ¬ relBad σ ρ strict) :
    (if strict then Sum.elim τ tt σ < Sum.elim τ tt ρ else Sum.elim τ tt σ ≤ Sum.elim τ tt ρ) := by
  classical
  rcases σ with a | i <;> rcases ρ with b | j
  · have h := hcons (a, b) (hp (by simp [pairOfRel]))
    cases strict
    · simpa using h.le
    · simpa using h
  · have hj := hρ j rfl
    subst hj
    have h := htop a
    cases strict
    · simpa using h.le
    · simpa using h
  · exact absurd trivial hb
  · have hi := hσ i rfl
    have hj := hρ j rfl
    subst hi; subst hj
    cases strict
    · simp
    · exact absurd rfl hb

theorem not_relHolds_of_bad (τ : T → ℝ) (tt : Fin 3 → ℝ) (htop : ∀ s, τ s < tt 0) (σ ρ : T ⊕ Fin 3) (hσ : SlotWf σ)
    (hρ : SlotWf ρ) (strict : Bool) (hb : relBad σ ρ strict) :
    ¬ (if strict then Sum.elim τ tt σ < Sum.elim τ tt ρ else Sum.elim τ tt σ ≤ Sum.elim τ tt ρ) := by
  rcases σ with a | i <;> rcases ρ with b | j
  · exact absurd hb (by simp [relBad])
  · exact absurd hb (by simp [relBad])
  · have hi := hσ i rfl
    subst hi
    have h := htop b
    cases strict
    · simpa using h
    · simpa using h.le
  · have hi := hσ i rfl
    have hj := hρ j rfl
    subst hi; subst hj
    have : strict = true := hb
    subst this
    simp

theorem excOrd_of_dom (caseA : Prop) {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β}
    (c : Ch S bs₁ bs₂ rA rB) (σ : Fin 3 → T ⊕ Fin 3) (hwf : ∀ i, SlotWf (σ i)) (τ : T → ℝ) (tt : Fin 3 → ℝ)
    (cons : Finset (T × T)) (htop : ∀ s, τ s < tt 0) (hcons : ∀ c ∈ cons, τ c.1 < τ c.2)
    (hp : ordPairs (ordRels caseA c) σ ⊆ cons) (hb : ¬ ordBad (ordRels caseA c) σ) :
    ExcOrd caseA (Sum.elim τ tt (σ 0)) (Sum.elim τ tt (σ 1)) (Sum.elim τ tt (σ 2)) c := by
  classical
  rw [excOrd_iff]
  intro r hr
  have hv : (![Sum.elim τ tt (σ 0), Sum.elim τ tt (σ 1), Sum.elim τ tt (σ 2)] : Fin 3 → ℝ) = fun i => Sum.elim τ tt (σ i) := by
    funext i; fin_cases i <;> rfl
  unfold relHolds
  rw [hv]
  exact relHolds_of_dom τ tt cons htop hcons (σ r.1) (σ r.2.1) (hwf _) (hwf _) r.2.2
    (fun x hx => hp (Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hr, hx⟩))
    (fun hbad => hb ⟨r, hr, hbad⟩)

theorem not_excOrd_of_dom (caseA : Prop) {β : Type*} {d : ℕ} {S : SepTerms β d} {bs₁ bs₂ rA rB : Finset β}
    (c : Ch S bs₁ bs₂ rA rB) (σ : Fin 3 → T ⊕ Fin 3) (hwf : ∀ i, SlotWf (σ i)) (τ : T → ℝ) (tt : Fin 3 → ℝ)
    (htop : ∀ s, τ s < tt 0) (hb : ordBad (ordRels caseA c) σ) :
    ¬ ExcOrd caseA (Sum.elim τ tt (σ 0)) (Sum.elim τ tt (σ 1)) (Sum.elim τ tt (σ 2)) c := by
  rw [excOrd_iff]
  intro h
  obtain ⟨r, hr, hbad⟩ := hb
  have h1 := h r hr
  have hv : (![Sum.elim τ tt (σ 0), Sum.elim τ tt (σ 1), Sum.elim τ tt (σ 2)] : Fin 3 → ℝ) = fun i => Sum.elim τ tt (σ i) := by
    funext i; fin_cases i <;> rfl
  unfold relHolds at h1
  rw [hv] at h1
  exact not_relHolds_of_bad τ tt htop (σ r.1) (σ r.2.1) (hwf _) (hwf _) r.2.2 hbad h1

end Slots

end WaveTurbulence.VineEstS5C.P4.W2
