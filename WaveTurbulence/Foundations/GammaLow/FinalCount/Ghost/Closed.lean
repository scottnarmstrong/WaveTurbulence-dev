/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex2G
/-! **L6E GHOST, part 10: Lemma 2.1 in its closed-set form** (M1-R2 NOTES §2, Lemma 2.1; REF-M1R2 §4.1 and repair R1).

*Statement (REF-M1R2 R1).* Let `S` be a set of atoms of a molecule, all with charge `c_v = 0`, whose only boundary darts
(darts at `S` whose mate is outside `S`) are `p ≠ q`, with opposite orientations. Then in every `(c_v)`-decoration the
two bonds of `p` and `q` carry the same momentum. At the outside atom `z` holding `mate p` and `mate q` (the third atom
of a triangle whose two other atoms are the ghosts `x`, `y`), the gap along `(mate p, mate q)` is `0`: the triangle is
not eligible (R29: SG at `v₁`, `v₂`, nonzero gap at `v₃`).

* `sum_darts_boundary`: `∑_{a ∈ S} ∑_{x at a} g x = ∑_{boundary darts} g x` for `g` odd under `mate`;
* `closedSet_kappa_eq` / `closedSet_zero_gap`: the conclusion on the molecule (applied to `M_sb = M₀`, where
  `c_v = 0` at every degree-4 atom, TARGET Def `defdecmol` L1308);
* `closedSet_zero_gap_down`: the same for the inherited decoration `κ₀ ∘ down` of a run state;
* `TriData.not_eligible_of_closedSet`: the contradiction with main's `hnz` (nonzero triangle gaps). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- **Flux through the boundary.** For `g` odd under `mate`, the sum over the darts of `S` is the sum over its
boundary darts (internal bonds cancel). -/
theorem sum_darts_boundary {E : Type*} [AddCommGroup E] (M : Molecule V D) (S : Finset V) (g : D → E)
    (hg : ∀ x, g (M.mate x) = -g x) :
    ∑ a ∈ S, ∑ x ∈ M.dartsAt a, g x =
      ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S), g x := by
  have h1 : ∑ a ∈ S, ∑ x ∈ M.dartsAt a, g x = ∑ x ∈ Finset.univ.filter (fun x => M.atom x ∈ S), g x := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun x => M.atom x ∈ S))
      (t := S) (g := M.atom) (fun x hx => (Finset.mem_filter.mp hx).2)]
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr ?_ fun _ _ => rfl
    ext x
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact ⟨h ▸ ha, h⟩
    · intro h; exact h.2
  rw [h1, ← Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (fun x => M.atom x ∈ S))
    (fun x => M.atom (M.mate x) ∈ S)]
  have hint : ∑ x ∈ (Finset.univ.filter (fun x => M.atom x ∈ S)).filter (fun x => M.atom (M.mate x) ∈ S), g x = 0 := by
    refine Finset.sum_involution (fun x _ => M.mate x) ?_ ?_ ?_ ?_
    · intro x _; rw [hg x]; simp
    · intro x _ _ h; exact M.mate_ne x h
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact ⟨hx.2, by rw [M.mate_mate]; exact hx.1⟩
    · intro x _; exact M.mate_mate x
  rw [hint, zero_add]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Lemma 2.1 (closed-set form), the momenta.** Charge-`0` atoms `S` with exactly two boundary darts `p ≠ q` of
opposite orientations: the two boundary bonds carry the same label. -/
theorem closedSet_kappa_eq (M : Molecule V D) {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hdec : M.IsDecoration L w c κ) (S : Finset V) (hSat : S ⊆ M.atoms) (hc : ∀ v ∈ S, c v = 0) (p q : D)
    (hpq : p ≠ q) (hp : M.atom p ∈ S ∧ M.atom (M.mate p) ∉ S) (hq : M.atom q ∈ S ∧ M.atom (M.mate q) ∉ S)
    (hbd : ∀ x, M.atom x ∈ S → M.atom (M.mate x) ∉ S → x = p ∨ x = q) (hdir : M.out p ≠ M.out q) :
    Molecule.kvec L w κ p = Molecule.kvec L w κ q := by
  have hflux := sum_darts_boundary M S (fun x => M.dartSign x • Molecule.kvec L w κ x) (by
    intro x
    have h1 : Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
      unfold Molecule.kvec; rw [hdec.1 x]
    simp only [Molecule.dartSign, M.out_mate, h1]
    cases M.out x <;> simp)
  have hzero : ∑ a ∈ S, ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L w κ x = 0 := by
    rw [Finset.sum_congr rfl fun a ha => hdec.2 a (hSat ha)]
    exact Finset.sum_eq_zero fun a ha => hc a ha
  have hbset : Finset.univ.filter (fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S) = {p, q} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact hbd x h1 h2
    · rintro (rfl | rfl)
      · exact hp
      · exact hq
  rw [hzero, hbset, Finset.sum_pair hpq] at hflux
  -- `ζ_p k_p + ζ_q k_q = 0` with `ζ_q = -ζ_p`
  have hsq : M.dartSign q = -M.dartSign p := by
    unfold Molecule.dartSign
    rcases hP : M.out p <;> rcases hQ : M.out q <;> simp_all
  rw [hsq, neg_smul] at hflux
  have hs0 : M.dartSign p ≠ 0 := by unfold Molecule.dartSign; split_ifs <;> norm_num
  have h2 : M.dartSign p • (Molecule.kvec L w κ p - Molecule.kvec L w κ q) = 0 := by
    rw [smul_sub, sub_eq_add_neg]; exact hflux.symm
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd h hs0
  · exact sub_eq_zero.1 h

/-- **Lemma 2.1 (closed-set form), the gap at the outside atom** `z` (holding `mate p` and `mate q`): zero. -/
theorem closedSet_zero_gap (M : Molecule V D) {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → (Fin d → ℤ)}
    (hdec : M.IsDecoration L w c κ) (S : Finset V) (hSat : S ⊆ M.atoms) (hc : ∀ v ∈ S, c v = 0) (p q : D)
    (hpq : p ≠ q) (hp : M.atom p ∈ S ∧ M.atom (M.mate p) ∉ S) (hq : M.atom q ∈ S ∧ M.atom (M.mate q) ∉ S)
    (hbd : ∀ x, M.atom x ∈ S → M.atom (M.mate x) ∉ S → x = p ∨ x = q) (hdir : M.out p ≠ M.out q) :
    Molecule.gapAt L w κ (M.mate p) (M.mate q) = 0 := by
  have h := closedSet_kappa_eq M hdec S hSat hc p q hpq hp hq hbd hdir
  unfold Molecule.gapAt
  have e1 : Molecule.kvec L w κ (M.mate p) = Molecule.kvec L w κ p := by unfold Molecule.kvec; rw [hdec.1 p]
  have e2 : Molecule.kvec L w κ (M.mate q) = Molecule.kvec L w κ q := by unfold Molecule.kvec; rw [hdec.1 q]
  rw [e1, e2, h, sub_self]

/-- **Lemma 2.1 for a run state**: the decoration of a state is inherited from an `M₀`-decoration `κ₀` through
`down`; if the triangle darts `a`, `b` at `z` go down to `mate p`, `mate q` (or `mate q`, `mate p`), the gap is `0`. -/
theorem closedSet_zero_gap_down {D' : Type*} (M₀ : Molecule V D) {L : ℝ} {w : Mom d} {c : V → Mom d}
    {κ₀ : D → (Fin d → ℤ)} (hdec : M₀.IsDecoration L w c κ₀) (S : Finset V) (hSat : S ⊆ M₀.atoms)
    (hc : ∀ v ∈ S, c v = 0) (p q : D) (hpq : p ≠ q) (hp : M₀.atom p ∈ S ∧ M₀.atom (M₀.mate p) ∉ S)
    (hq : M₀.atom q ∈ S ∧ M₀.atom (M₀.mate q) ∉ S)
    (hbd : ∀ x, M₀.atom x ∈ S → M₀.atom (M₀.mate x) ∉ S → x = p ∨ x = q) (hdir : M₀.out p ≠ M₀.out q)
    (down : D' → D) (a b : D')
    (hab : (down a = M₀.mate p ∧ down b = M₀.mate q) ∨ (down a = M₀.mate q ∧ down b = M₀.mate p)) :
    Molecule.gapAt L w (κ₀ ∘ down) a b = 0 := by
  have h := closedSet_zero_gap M₀ hdec S hSat hc p q hpq hp hq hbd hdir
  have e : Molecule.gapAt L w (κ₀ ∘ down) a b = Molecule.gapAt L w κ₀ (down a) (down b) := rfl
  rw [e]
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb, h]
  · rw [ha, hb]
    unfold Molecule.gapAt at h ⊢
    rw [← neg_sub, h, neg_zero]

/-- **The triangle is not eligible** (Lemma 2.1 ⇒ Cor 2.2): main's triangle hypothesis `hnz` (nonzero gaps at the three
triangle atoms) fails at `z = T.t j` when its darts go down to the two boundary darts' mates of a charge-`0` set. -/
theorem TriData.not_eligible_of_closedSet {M : Molecule V D} {D₀ : Type*} [Fintype D₀] [DecidableEq D₀] (T : TriData M) (M₀ : Molecule V D₀)
    {L : ℝ} {w : Mom d} {c : V → Mom d} {κ₀ : D₀ → (Fin d → ℤ)} (hdec : M₀.IsDecoration L w c κ₀)
    (S : Finset V) (hSat : S ⊆ M₀.atoms) (hc : ∀ v ∈ S, c v = 0) (p q : D₀) (hpq : p ≠ q)
    (hp : M₀.atom p ∈ S ∧ M₀.atom (M₀.mate p) ∉ S) (hq : M₀.atom q ∈ S ∧ M₀.atom (M₀.mate q) ∉ S)
    (hbd : ∀ x, M₀.atom x ∈ S → M₀.atom (M₀.mate x) ∉ S → x = p ∨ x = q) (hdir : M₀.out p ≠ M₀.out q)
    (down : D → D₀) (j : Fin 3)
    (hab : (down (T.a j) = M₀.mate p ∧ down (T.b j) = M₀.mate q) ∨
      (down (T.a j) = M₀.mate q ∧ down (T.b j) = M₀.mate p)) :
    ¬ (Molecule.gapAt L w (κ₀ ∘ down) (T.a j) (T.b j) ≠ 0) := by
  intro hne
  exact hne (closedSet_zero_gap_down M₀ hdec S hSat hc p q hpq hp hq hbd hdir down (T.a j) (T.b j) hab)

end WaveTurbulence.GammaLow.FinalCount.Ghost
