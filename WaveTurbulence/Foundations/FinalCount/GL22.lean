/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL21
public import WaveTurbulence.Foundations.FinalCount.GL18
/-! **G3-LOWDEG (R48), part 22: transport of vine-like objects between `M` and `M.unloop`** (for objects whose atoms carry no
self-loop of `M`).  `Object.unloop`, `Object.lift`, with `ContainsDart` and `HasGapKind` (for the decoration `κ ∘ val`) preserved. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.LGSpine.SourceVine
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}

/-- No loop dart of `M` has its atom in `S`. -/
def LoopFreeSet (M : Molecule V D) (S : Finset V) : Prop := ∀ y : D, M.atom y ∈ S → M.atom y ≠ M.atom (M.mate y)

theorem LoopFreeSet.mono {M : Molecule V D} {S T : Finset V} (h : LoopFreeSet M S) (hT : T ⊆ S) : LoopFreeSet M T :=
  fun y hy => h y (hT hy)

theorem unloopEmb (M : Molecule V D) {S : Finset V} (h : LoopFreeSet M S) : GEmb M.unloop M Subtype.val S where
  inj := Subtype.val_injective
  atom := fun _ => rfl
  mate := fun _ => rfl
  out := fun _ => rfl
  cover := fun z hz => ⟨⟨z, h z hz.1⟩, rfl⟩

/-- The dart embedding `eraseBond M.unloop e' ↪ eraseBond M e'.1`. -/
def eraseUnloopMap (M : Molecule V D) (e : NonLoop M) :
    {x : NonLoop M // x ≠ e ∧ x ≠ M.unloop.mate e} → {x : D // x ≠ e.1 ∧ x ≠ M.mate e.1} :=
  fun z => ⟨z.1.1, fun h => z.2.1 (Subtype.ext h), fun h => z.2.2 (Subtype.ext h)⟩

theorem eraseUnloopEmb (M : Molecule V D) (e : NonLoop M) {S : Finset V} (h : LoopFreeSet M S) :
    GEmb (M.unloop.eraseBond e) (M.eraseBond e.1) (eraseUnloopMap M e) S where
  inj := fun a b hab => Subtype.ext (Subtype.ext (by simpa [eraseUnloopMap] using congrArg Subtype.val hab))
  atom := fun _ => rfl
  mate := fun _ => rfl
  out := fun _ => rfl
  cover := fun z hz => by
    have hn := h z.1 hz.1
    refine ⟨⟨⟨z.1, hn⟩, fun hh => z.2.1 (congrArg Subtype.val hh), fun hh => z.2.2 (congrArg Subtype.val hh)⟩, rfl⟩

theorem GEmb.isBlockGap_iff {V D1 D2 : Type*} [DecidableEq V] [Fintype D1] [DecidableEq D1] [Fintype D2] [DecidableEq D2]
    {M1 : Molecule V D1} {M2 : Molecule V D2} {ι : D1 → D2} {S : Finset V} (G : GEmb M1 M2 ι S) {d : ℕ} (L : ℝ) (w : Mom d)
    (κ : D2 → Fin d → ℤ) (j : V) (r : Mom d) :
    M2.IsBlockGap L w κ S j r ↔ M1.IsBlockGap L w (fun x => κ (ι x)) S j r := by
  unfold Molecule.IsBlockGap
  constructor
  · rintro ⟨z₁, z₂, h1, h2, g1, g2, o1, o2, hr⟩
    obtain ⟨x₁, rfl⟩ := G.cover z₁ g1
    obtain ⟨x₂, rfl⟩ := G.cover z₂ g2
    exact ⟨x₁, x₂, by rw [← G.atom]; exact h1, by rw [← G.atom]; exact h2, (G.inGroup_iff S x₁).1 g1,
      (G.inGroup_iff S x₂).1 g2, by rw [← G.out]; exact o1, by rw [← G.out]; exact o2, hr⟩
  · rintro ⟨x₁, x₂, h1, h2, g1, g2, o1, o2, hr⟩
    exact ⟨ι x₁, ι x₂, by rw [G.atom]; exact h1, by rw [G.atom]; exact h2, (G.inGroup_iff S x₁).2 g1,
      (G.inGroup_iff S x₂).2 g2, by rw [G.out]; exact o1, by rw [G.out]; exact o2, hr⟩

theorem nonloop_of_block {M : Molecule V D} {S : Finset V} {a b : V} (hb : M.IsBlock S a b) {e : D} (he : M.ends e = s(a, b)) :
    M.atom e ≠ M.atom (M.mate e) := ends_ne_of hb.2.2.2.1 he

end WaveTurbulence.FinalCountG3
