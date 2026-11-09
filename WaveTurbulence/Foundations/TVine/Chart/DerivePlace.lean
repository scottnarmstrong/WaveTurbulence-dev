/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveCell

/-!
# Derivation of the cell decomposition, VI: placing a piece

`place_cell`: a placement of a piece shape whose stubs are port bonds is injective by a signature argument (an
internal bond crosses no port region, a stub crosses the region of its own role and no other, two stubs of one role
sit at different atoms), so `build_cell` applies.
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V}

/-- The bond `φB l` of a stub has exactly one end among the placed atoms, at `φA u`. -/
def StubAt {nA : ℕ} (φA : Fin nA → V) (e : Bond M S) (u : Fin nA) : Prop :=
  (tl e = φA u ∧ ∀ u', hd e ≠ φA u') ∨ (hd e = φA u ∧ ∀ u', tl e ≠ φA u')

theorem stubAt_unique {nA : ℕ} {φA : Fin nA → V} (hA : Function.Injective φA) {e : Bond M S} {u u' : Fin nA}
    (h : StubAt φA e u) (h' : StubAt φA e u') : u = u' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases h' with ⟨h3, h4⟩ | ⟨h3, h4⟩
  · exact hA (h1.symm.trans h3)
  · exact absurd h1 (h4 u)
  · exact absurd h3 (h2 u')
  · exact hA (h1.symm.trans h3)

/-- **Placing a piece.** -/
theorem place_cell {nA nC nB : ℕ} (P : PShape nA nB) (tab : List (LocalChart nA nC nB))
    (hcov : ∀ b : Fin nB → Bool, P.OK b → ∃ c ∈ tab, c.src = P.src b ∧ c.dst = P.dst b)
    (hM : M.IsMolecule) (φA : Fin nA → V) (φB : Fin nB → Bond M S) (R : SRole → Finset V)
    (hAinj : Function.Injective φA) (hmem : ∀ u, φA u ∈ M.atoms) (hdeg : ∀ u, M.degIn S (φA u) = 4)
    (hlocdeg : ∀ u : Fin nA, 4 ≤ (univ.filter fun l => (P.ends l).1 = u ∨ (P.ends l).2 = some u).card)
    (hnoloop : ∀ l u w, P.ends l = (u, some w) → u ≠ w)
    (hsameRole : ∀ l l' u u', l ≠ l' → P.ends l = (u, none) → P.ends l' = (u', none) → P.role l = P.role l' → u ≠ u')
    (hroleStub : ∀ l u, P.ends l = (u, none) → P.role l ≠ .int)
    (hint : ∀ l u w, P.ends l = (u, some w) →
      (tl (φB l) = φA u ∧ hd (φB l) = φA w) ∨ (tl (φB l) = φA w ∧ hd (φB l) = φA u))
    (hpar : ∀ l l' u w u' w', l ≠ l' → P.ends l = (u, some w) → P.ends l' = (u', some w') →
      s(u, w) = s(u', w') → φB l ≠ φB l')
    (hintNo : ∀ l u w ρ, P.ends l = (u, some w) → ρ ≠ .int → ¬ Crosses (R ρ) (φB l))
    (hstub : ∀ l u, P.ends l = (u, none) → StubAt φA (φB l) u)
    (hcross : ∀ l u, P.ends l = (u, none) → Crosses (R (P.role l)) (φB l))
    (hnocross : ∀ l l' u u', P.ends l = (u, none) → P.ends l' = (u', none) → P.role l ≠ P.role l' →
      ¬ Crosses (R (P.role l')) (φB l))
    (hpairs : ∀ ρ ∈ [SRole.inp, SRole.exM, SRole.exB],
      (univ.filter fun l => P.role l = ρ ∧ placeBits P φA φB l = true).card =
        (univ.filter fun l => P.role l = ρ ∧ placeBits P φA φB l = false).card) :
    ∃ c ∈ tab, c.src = P.src (placeBits P φA φB) ∧ c.dst = P.dst (placeBits P φA φB) ∧
      ∃ φ : LocEmb c.graph M S, φ.atom = φA ∧ φ.bond = φB := by
  have hBinj : Function.Injective φB := by
    intro l l' heq
    by_contra hne
    rcases hl : P.ends l with ⟨u, w⟩
    rcases hl' : P.ends l' with ⟨u', w'⟩
    rcases w with _ | w <;> rcases w' with _ | w'
    · -- two stubs
      by_cases hr : P.role l = P.role l'
      · exact hsameRole l l' u u' hne hl hl' hr
          (stubAt_unique hAinj (hstub l u hl) (heq ▸ hstub l' u' hl'))
      · exact hnocross l l' u u' hl hl' hr (heq ▸ hcross l' u' hl')
    · -- stub, internal
      exact hintNo l' u' w' (P.role l) hl' (hroleStub l u hl) (heq ▸ hcross l u hl)
    · -- internal, stub
      exact hintNo l u w (P.role l') hl (hroleStub l' u' hl') (heq ▸ hcross l' u' hl')
    · -- two internal
      apply hpar l l' u w u' w' hne hl hl' _ heq
      have h1 := hint l u w hl
      have h2 := hint l' u' w' hl'
      rw [heq] at h1
      rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · rw [hAinj (a1.symm.trans b1), hAinj (a2.symm.trans b2)]
      · rw [hAinj (a1.symm.trans b1), hAinj (a2.symm.trans b2), Sym2.eq_swap]
      · rw [hAinj (a1.symm.trans b1), hAinj (a2.symm.trans b2), Sym2.eq_swap]
      · rw [hAinj (a1.symm.trans b1), hAinj (a2.symm.trans b2)]
  exact build_cell P tab hcov hM φA φB hAinj hBinj hmem hdeg hlocdeg hnoloop hint
    (fun l u h => hstub l u h) hpairs

end WaveTurbulence.TVine.Chart
