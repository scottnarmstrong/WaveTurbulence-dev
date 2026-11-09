/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.ChainOrient
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.BetaCut
public import WaveTurbulence.Foundations.FinalCount.Prop96Statement
import Mathlib.Tactic

/-! # The configurations of operation (d)+(e) (packet L6-COUNT, item D; M2 Lemma 4.3, REF-M2 R3)

M2 Lemma 4.3 "Which configurations occur": the removed set `S = C ∪ {p, q}` has at most one external bond at `p` and
at most one at `q`, so at most two exits. The configurations are:
* none (`crossDarts = ∅`, `opE_none`), one (`OneExit`, `opE_one`), two at distinct atoms (`TwoExit`, `opE_two`);
* two at **one** atom `w` (`Pinch`): excluded by `noBetaCut` (REF-M2 R3).

* `exit_cases`: the classification. With two exits, `S` balanced (in = out at every atom of `S`, e.g. `p, q` of degree
  four in a molecule with in/out caps two and chain atoms in = out = 1) gives exits of opposite directions (main's
  `chain_cross_opposite`), hence `TwoExit` or `Pinch`.
* `pinch_gap_eq_starSum`: the gap of the cut of `w` along the two exits is the signed star sum over `S`
  (`∑_{v∈S} ∑_{z∈v} ζ_z k_z`, the total charge of the `S`-side: REF-M2 R3, "its gap is the total charge of all α/β
  atoms on the S-side").
* `pinch_gap_eq_zero`: under a `noBetaCut` hypothesis (the form of `FinalDec.noBetaCut` / L6's
  `FinalDecLow.noBetaCut`) and `deg w ≥ 3`, that gap is zero (main's `Pinch.cut_not_alpha`: the cut is a β-cut).
  `pinch_gap_eq_zero_of_finalDec`: the same from main's `FinalDec`.
So a pinch with nonzero total charge on the `S`-side (in case (6d): `±r₁`, `±r₂` or `±r_β`, nonzero by `alphaGap`,
`betaGap`) cannot occur. -/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.GammaLow.FinalCount.Count
open WaveTurbulence.MoleProp4 WaveTurbulence.FinalCountG8

section
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The external configurations** of a removed set with at most two exits (M2 Lemma 4.3): none, one exit, two exits
at distinct atoms, or two exits at one atom. With two exits `S` is balanced. -/
theorem exit_cases (N : Molecule V D) (S : Finset V) (hS : S ⊆ N.atoms) (h2 : (crossDarts N S).card ≤ 2)
    (hbal : (crossDarts N S).card = 2 → ∀ v ∈ S, N.outdeg v = N.indeg v) :
    crossDarts N S = ∅ ∨ (∃ T : OneExit N, T.Y = S) ∨ (∃ T : TwoExit N, T.Y = S) ∨ (∃ T : Pinch N, T.Y = S) := by
  classical
  rcases Nat.lt_or_ge (crossDarts N S).card 2 with hlt | hge
  · rcases Nat.lt_or_ge (crossDarts N S).card 1 with h0 | h1
    · left; exact card_eq_zero.mp (by omega)
    · right; left
      obtain ⟨x, hx⟩ := card_eq_one.mp (by omega : (crossDarts N S).card = 1)
      exact ⟨⟨S, hS, x, hx⟩, rfl⟩
  · have hc : (crossDarts N S).card = 2 := le_antisymm h2 hge
    obtain ⟨y₁, y₂, hne, hy⟩ := card_eq_two.mp hc
    have hop := chain_cross_opposite N S (hbal hc) hne hy
    right; right
    -- `x` the outgoing exit, `y` the incoming one
    have key : ∃ x y : D, crossDarts N S = {x, y} ∧ x ≠ y ∧ N.out x = true ∧ N.out y = false := by
      cases h1 : N.out y₁
      · have h2' : N.out y₂ = true := by
          cases h2'' : N.out y₂
          · exact absurd (h1.trans h2''.symm) hop
          · rfl
        exact ⟨y₂, y₁, by rw [hy, pair_comm], hne.symm, h2', h1⟩
      · have h2' : N.out y₂ = false := by
          cases h2'' : N.out y₂
          · rfl
          · exact absurd (h1.trans h2''.symm) hop
        exact ⟨y₁, y₂, hy, hne, h1, h2'⟩
    obtain ⟨x, y, hxy, hne', hox, hoy⟩ := key
    by_cases hw : N.atom (N.mate x) = N.atom (N.mate y)
    · right; exact ⟨⟨S, hS, x, y, hxy, hne', hw, hox, hoy⟩, rfl⟩
    · left; exact ⟨⟨S, hS, x, y, hxy, hne', hw, hox, hoy⟩, rfl⟩


/-- **The gap of the pinch cut is the total charge of the `S`-side** (REF-M2 R3): for labels constant on bonds,
`k_{mate x} − k_{mate y} = ∑_{v ∈ S} ∑_{z ∈ v} ζ_z k_z`. -/
theorem pinch_gap_eq_starSum {M : Molecule V D} (T : Pinch M) {d : ℕ} (L : ℝ) {κ : D → (Fin d → ℤ)} (hκ : ∀ x, κ (M.mate x) = κ x) :
    Molecule.gapAt L 0 κ (M.mate T.x) (M.mate T.y) =
      ∑ v ∈ T.Y, ∑ z ∈ M.dartsAt v, M.dartSign z • Molecule.kvec L 0 κ z := by
  rw [sum_stars_eq_cross M T.Y (fun z => M.dartSign z • Molecule.kvec L 0 κ z) (fun x => by
    simp only [dartSign_mate, Molecule.kvec, hκ x, neg_smul]), T.cross, sum_pair T.ne]
  unfold Molecule.gapAt Molecule.dartSign
  rw [T.out_x, T.out_y]
  simp only [Molecule.kvec, hκ, ite_true, Bool.false_eq_true, ite_false, one_smul, neg_one_smul]
  abel

/-- **A pinch has zero gap under `noBetaCut`** (REF-M2 R3): if every cut with nonzero gap at an atom of degree `≥ 3`
is an α-cut, the cut of `w` along the two exits (a β-cut, main's `Pinch.cut_not_alpha`) has gap zero. -/
theorem pinch_gap_eq_zero {M : Molecule V D} (T : Pinch M) {d : ℕ} {L : ℝ} {κ : D → (Fin d → ℤ)} (hfresh : ∃ v₂ : V, v₂ ∉ M.atoms)
    (hdeg : 3 ≤ M.deg T.w)
    (hNB : ∀ v ∈ M.atoms, 3 ≤ M.deg v → ∀ v₂ x₁ x₂, M.IsCutData v v₂ x₁ x₂ →
      Molecule.gapAt L (0 : Mom d) κ x₁ x₂ ≠ 0 → M.IsAlphaCut v v₂ x₁ x₂) :
    Molecule.gapAt L (0 : Mom d) κ (M.mate T.x) (M.mate T.y) = 0 := by
  obtain ⟨v₂, hv₂⟩ := hfresh
  by_contra hne
  exact T.cut_not_alpha hv₂ (hNB T.w (M.atom_mem _) hdeg v₂ _ _ (T.cutData hv₂) hne)

/-- **Exclusion of the pinch from main's `FinalDec`** (its `noBetaCut` field). L6's `FinalDecLow.noBetaCut` has the
same form and is used as `pinch_gap_eq_zero T hfresh hdeg (hF.noBetaCut κ hκ)`. -/
theorem pinch_gap_eq_zero_of_finalDec {M : Molecule V D} (T : Pinch M) {cls : V → Cls} {d : ℕ} {L γ η : ℝ} {Adm : (D → (Fin d → ℤ)) → Prop}
    (hF : FinalDec M cls L γ η Adm) {κ : D → (Fin d → ℤ)} (hκ : Adm κ) (hfresh : ∃ v₂ : V, v₂ ∉ M.atoms)
    (hdeg : 3 ≤ M.deg T.w) : Molecule.gapAt L (0 : Mom d) κ (M.mate T.x) (M.mate T.y) = 0 :=
  pinch_gap_eq_zero T hfresh hdeg (hF.noBetaCut κ hκ)

end

end WaveTurbulence.GammaLow.FinalCount.Count
