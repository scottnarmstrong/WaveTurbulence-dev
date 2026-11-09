/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Match
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone8
public import WaveTurbulence.Foundations.FinalCount.G3Hist
/-! **Ghost assembly, part 2: the NC graph of a run state and its bank** (design: `CHAIN-DESIGN.md`).

For a state `h` of the run and a class `A` of `M_sb`-decorations (state decorations `k0 ∘ h.s.down`):
* `IsCritA`: the present κ = 0 α-atoms of degree `2` with a critical label (M1-R2 §6, "critical");
* `gvec`: the gap of an atom's cut record (`pgap k0 p` for `crec x = some (p, _)`): an `M_sb`-level vector, equal to
  `±` the dart gap of the atom by the run invariant `HGap.dg` (main `G3Dart`);
* `TRon`: transversality (T-TR) of two parameters on the whole class (`θ₀ = L^{-6η}`, Gram form of `TRpair`);
* `Locked`: every two darts at a common atom pointing to `x` and `y` have gap `0` on the class (the M1-R2 Lemma 2.1
  configuration; such a pair is never two ghosts of an eligible triangle);
* `NCEdge`, `bank`: the NC graph and its matching number.

A **survivor map** `SurvMap h h' X` (darts of `h'` injected into darts of `h`, commuting with `down` and `mate`;
atoms of `X` keep their membership, degree, class and cut record) transports all of these from `s'` back to `s` (`SurvMap.edge`): edges among
survivors can only disappear along the run. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} {d : ℕ}

/-- The gap vector of an atom: the gap of its cut record (`0` without a record). -/
noncomputable def gvec (h : HSt V D₀) (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) (x : V) : Mom d :=
  match h.crec x with
  | some pv => pgap L w k0 pv.1
  | none => 0

/-- A present κ = 0 `α`-atom of degree `2` with a critical label. -/
def IsCritA (L γ η : ℝ) (h : HSt V D₀) (x : V) : Prop :=
  x ∈ h.s.M.atoms ∧ h.s.M.deg x = 2 ∧ ∃ R, h.s.cls x = .alpha R 0 ∧ Crit L γ η R

/-- (T-TR) of the gap vectors of `x` and `y` on the class `A`. -/
def TRon (L η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (x y : V) : Prop :=
  ∀ k0 ∈ A, L ^ (-12 * η) * (‖gvec h L w k0 x‖ ^ 2 * ‖gvec h L w k0 y‖ ^ 2) ≤
    ‖gvec h L w k0 x‖ ^ 2 * ‖gvec h L w k0 y‖ ^ 2 - inner ℝ (gvec h L w k0 x) (gvec h L w k0 y) ^ 2

/-- `x, y` are locked on `A`: two darts of opposite directions at a common atom pointing to `x` and to `y` have gap
`0` on `A`. -/
def Locked (L : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (x y : V) : Prop :=
  ∀ a b : h.s.D, h.s.M.atom a = h.s.M.atom b → h.s.M.out a ≠ h.s.M.out b → h.s.M.atom (h.s.M.mate a) = x →
    h.s.M.atom (h.s.M.mate b) = y → ∀ k0 ∈ A, Molecule.gapAt L w (k0 ∘ h.s.down) a b = 0

/-- **The NC graph**: adjacent critical atoms, not transverse and not locked on `A`. -/
def NCEdge (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (x y : V) : Prop :=
  x ≠ y ∧ IsCritA L γ η h x ∧ IsCritA L γ η h y ∧ h.s.M.Adj x y ∧ ¬ TRon L η w h A x y ∧
    ¬ Locked L w h A x y ∧ ¬ Locked L w h A y x

/-- The critical atoms of a state. -/
noncomputable def critSet (L γ η : ℝ) (h : HSt V D₀) : Finset V := h.s.M.atoms.filter (IsCritA L γ η h)

/-- **The bank**: the matching number of the NC graph. -/
noncomputable def bank (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) : ℕ :=
  matchNum (NCEdge L γ η w h A) (critSet L γ η h)

theorem mem_critSet {L γ η : ℝ} {h : HSt V D₀} {x : V} : x ∈ critSet L γ η h ↔ IsCritA L γ η h x := by
  unfold critSet; rw [mem_filter]
  exact ⟨fun hx => hx.2, fun hx => ⟨hx.1, hx⟩⟩

/-! ### Monotonicity in the class -/

theorem TRon.mono {L η : ℝ} {w : Mom d} {h : HSt V D₀} {A B : Set (D₀ → (Fin d → ℤ))} {x y : V}
    (hT : TRon L η w h A x y) (hBA : B ⊆ A) : TRon L η w h B x y := fun k0 hk => hT k0 (hBA hk)

theorem Locked.mono {L : ℝ} {w : Mom d} {h : HSt V D₀} {A B : Set (D₀ → (Fin d → ℤ))} {x y : V}
    (hL : Locked L w h A x y) (hBA : B ⊆ A) : Locked L w h B x y :=
  fun a b hab ho ha hb k0 hk => hL a b hab ho ha hb k0 (hBA hk)

theorem NCEdge.mono {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A B : Set (D₀ → (Fin d → ℤ))} {x y : V}
    (hE : NCEdge L γ η w h B x y) (hBA : B ⊆ A) : NCEdge L γ η w h A x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hE
  exact ⟨h1, h2, h3, h4, fun hT => h5 (hT.mono hBA), fun hL => h6 (hL.mono hBA), fun hL => h7 (hL.mono hBA)⟩

theorem bank_mono {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A B : Set (D₀ → (Fin d → ℤ))} (hBA : B ⊆ A) :
    bank L γ η w h B ≤ bank L γ η w h A :=
  matchNum_mono (fun _ _ _ _ hE => hE.mono hBA) subset_rfl

/-! ### Survivor maps -/

/-- **A survivor map** from `h'` back to `h`: the darts of `h'` map into those of `h` (with `down` and `mate`); two darts
at one atom of `h'` were at one atom of `h`; an atom of `X` keeps its membership, degree, class and cut record. -/
structure SurvMap (h h' : HSt V D₀) (X : Set V) where
  ι : h'.s.D → h.s.D
  down_eq : ∀ a, h'.s.down a = h.s.down (ι a)
  out_eq : ∀ a, h'.s.M.out a = h.s.M.out (ι a)
  mate_eq : ∀ a, ι (h'.s.M.mate a) = h.s.M.mate (ι a)
  atom_eq : ∀ a, h'.s.M.atom a ∈ X → h.s.M.atom (ι a) = h'.s.M.atom a
  common : ∀ a b, h'.s.M.atom a = h'.s.M.atom b → h.s.M.atom (ι a) = h.s.M.atom (ι b)
  mem : ∀ x ∈ X, x ∈ h'.s.M.atoms → x ∈ h.s.M.atoms
  deg_eq : ∀ x ∈ X, h'.s.M.deg x = h.s.M.deg x
  cls_eq : ∀ x ∈ X, h'.s.cls x = h.s.cls x
  crec_eq : ∀ x ∈ X, h'.crec x = h.crec x

namespace SurvMap
variable {h h' : HSt V D₀} {X : Set V} (F : SurvMap h h' X)
include F

theorem kvec_eq (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) (a : h'.s.D) :
    Molecule.kvec L w (k0 ∘ h'.s.down) a = Molecule.kvec L w (k0 ∘ h.s.down) (F.ι a) := by
  unfold Molecule.kvec; simp only [Function.comp, F.down_eq]

theorem gapAt_eq (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) (a b : h'.s.D) :
    Molecule.gapAt L w (k0 ∘ h'.s.down) a b = Molecule.gapAt L w (k0 ∘ h.s.down) (F.ι a) (F.ι b) := by
  unfold Molecule.gapAt; rw [F.kvec_eq, F.kvec_eq]

theorem gvec_eq (L : ℝ) (w : Mom d) (k0 : D₀ → (Fin d → ℤ)) {x : V} (hx : x ∈ X) :
    gvec h' L w k0 x = gvec h L w k0 x := by
  unfold gvec; rw [F.crec_eq x hx]

theorem critA {L γ η : ℝ} {x : V} (hx : x ∈ X) (hc : IsCritA L γ η h' x) : IsCritA L γ η h x := by
  obtain ⟨h1, h2, R, h3, h4⟩ := hc
  exact ⟨F.mem x hx h1, (F.deg_eq x hx).symm.trans h2, R, (F.cls_eq x hx).symm.trans h3, h4⟩

theorem adj {x y : V} (hx : x ∈ X) (hy : y ∈ X) (hA : h'.s.M.Adj x y) : h.s.M.Adj x y := by
  obtain ⟨a, ha, hb⟩ := hA
  refine ⟨F.ι a, ?_, ?_⟩
  · rw [F.atom_eq a (ha ▸ hx), ha]
  · rw [← F.mate_eq, F.atom_eq _ (hb ▸ hy), hb]

theorem tron {L η : ℝ} {w : Mom d} {A : Set (D₀ → (Fin d → ℤ))} {x y : V} (hx : x ∈ X) (hy : y ∈ X)
    (hT : TRon L η w h A x y) : TRon L η w h' A x y := by
  intro k0 hk
  rw [F.gvec_eq L w k0 hx, F.gvec_eq L w k0 hy]
  exact hT k0 hk

theorem locked {L : ℝ} {w : Mom d} {A : Set (D₀ → (Fin d → ℤ))} {x y : V} (hx : x ∈ X) (hy : y ∈ X)
    (hL : Locked L w h A x y) : Locked L w h' A x y := by
  intro a b hab ho ha hb k0 hk
  rw [F.gapAt_eq]
  refine hL (F.ι a) (F.ι b) (F.common a b hab) (by rw [← F.out_eq, ← F.out_eq]; exact ho) ?_ ?_ k0 hk
  · rw [← F.mate_eq, F.atom_eq _ (ha ▸ hx), ha]
  · rw [← F.mate_eq, F.atom_eq _ (hb ▸ hy), hb]

/-- **Edges among survivors come from edges of the earlier state** (on a larger class). -/
theorem edge {L γ η : ℝ} {w : Mom d} {A B : Set (D₀ → (Fin d → ℤ))} (hBA : B ⊆ A) {x y : V} (hx : x ∈ X)
    (hy : y ∈ X) (hE : NCEdge L γ η w h' B x y) : NCEdge L γ η w h A x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hE
  refine ⟨h1, F.critA hx h2, F.critA hy h3, F.adj hx hy h4, fun hT => h5 ((F.tron hx hy hT).mono hBA),
    fun hL => h6 ((F.locked hx hy hL).mono hBA), fun hL => h7 ((F.locked hy hx hL).mono hBA)⟩

end SurvMap

/-! ### The bank across a step -/

/-- **The bank across a step.** Edges of `h'` (on `B ⊆ A`) between survivors are edges of `h` (on `A`); if every edge
of `h'` between survivors has both ends in `Sold` or an end in `C`, and every edge with a non-survivor end has an end in
`C`, then the bank of `h'` is at most the matching number of `h`'s graph on `Sold`, plus `|C|`. -/
theorem bank_step {L γ η : ℝ} {w : Mom d} {h h' : HSt V D₀} {X : Set V} (F : SurvMap h h' X)
    {A B : Set (D₀ → (Fin d → ℤ))} (hBA : B ⊆ A) (Sold : Finset V) (C : Finset V)
    (hC : ∀ x y, NCEdge L γ η w h' B x y → x ∈ X → y ∈ X → x ∈ Sold ∧ y ∈ Sold ∨ x ∈ C ∨ y ∈ C)
    (hnew : ∀ x y, NCEdge L γ η w h' B x y → (x ∉ X ∨ y ∉ X) → x ∈ C ∨ y ∈ C) :
    bank L γ η w h' B ≤ matchNum (NCEdge L γ η w h A) Sold + C.card := by
  unfold bank
  refine matchNum_le_add_cover C fun x y _ _ _ hE => ?_
  by_cases hX : x ∈ X ∧ y ∈ X
  · rcases hC x y hE hX.1 hX.2 with hh | hh | hh
    · exact Or.inl ⟨hh.1, hh.2, F.edge hBA hX.1 hX.2 hE⟩
    · exact Or.inr (Or.inl hh)
    · exact Or.inr (Or.inr hh)
  · rw [not_and_or] at hX
    exact Or.inr (hnew x y hE hX)

end WaveTurbulence.GammaLow.FinalCount.Ghost
