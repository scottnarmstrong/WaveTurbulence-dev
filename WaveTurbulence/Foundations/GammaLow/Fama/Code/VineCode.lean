/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Fama.Code.TBand
public import WaveTurbulence.Foundations.GammaLow.Fama.Code.IngCode
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitDecode4
import Mathlib.Tactic
/-! # Every member of `𝒱_γ` (γ ≤ 1/2) has an ingredient code (packet L5a, items H, I)

The `𝒱_γ` version of main's `ClassCount.vine_chain_code`: a vine ingredient with joints `a` (first along the chain)
and `b`, placed at position `p`, has a well-formed code `c : IngCodeG` and a labelling onto `[p, p + c.size)` with
`a ↦ p`, `b ↦ p + c.size − 1`, whose arc multiset is the code's. Bad vines (I), (II): main's drawn codes (`toG`).
T-vines: a band code, from the band labelling (`Code/TBand.lean`), using L3's published statements of N3 Theorem 6
(`TVine.Struct.LayervineStatement`) and N2 Prop 1.17(b) (`TVine.Struct.PieceShapeStatement`). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Fama.ClassCount
open Finset WaveTurbulence.GammaLow.FinalCount

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- L3's published structure statements, carried as an instance. -/
abbrev TVineStructInputs : Prop :=
  TVine.Struct.LayervineStatement.{0, 0} ∧ TVine.Struct.PieceShapeStatement.{0, 0}

theorem groupArcs_comp (M : Molecule V D) (S : Finset V) (g : V → ℕ) (pos : ℕ → ℕ) :
    WaveTurbulence.ClassCount.groupArcs M S (pos ∘ g) =
      (WaveTurbulence.ClassCount.groupArcs M S g).map fun q => (pos q.1, pos q.2) := by
  unfold WaveTurbulence.ClassCount.groupArcs
  rw [Multiset.map_map]
  rfl

/-- The pieces of a T-vine have at most three atoms (N2 Prop 1.17(b)). -/
theorem tvine_piece_card_le (hP : TVine.Struct.PieceShapeStatement.{0, 0}) {M : Molecule V D} {S : Finset V}
    {a b : V} (h : M.IsTVine S a b) : ∀ P ∈ M.pieces S a b, P.card ≤ 3 := by
  obtain ⟨core, -, hcore, hrest, -⟩ := hP M S a b h
  intro P hP'
  by_cases hc : P = core
  · subst hc
    obtain ⟨x, y, z, -, -, -, rfl, -⟩ := hcore
    exact (card_insert_le _ _).trans (by have := card_insert_le y {z}; simp at this ⊢; omega)
  · obtain ⟨u, v, -, rfl, -⟩ := hrest P hP' hc
    exact (card_insert_le _ _).trans (by simp)

/-- **Band labelling of a T-vine** (joints `a ↦ 0`, `b ↦ 1`). -/
theorem tvine_band_labelling (hS : TVineStructInputs) {M : Molecule V D} (hM : M.IsMolecule) {S : Finset V}
    {a b : V} (h : M.IsTVine S a b) :
    ∃ f : V → ℕ, Set.InjOn f S ∧ S.image f = range S.card ∧ f a = 0 ∧ f b = 1 ∧
      BandAdmissible S.card (WaveTurbulence.ClassCount.groupArcs M S f) :=
  exists_band_labelling (spineData_of (hS.1 M S a b h).1) h.1 hM (tvine_piece_card_le hS.2 h)

/-- **The `𝒱_γ` ingredient code** (main's `ClassCount.vine_chain_code`). -/
theorem vine_chain_codeG (hS : TVineStructInputs) {γ : ℝ} (hγ : γ ≤ 1 / 2) (M : Molecule V D)
    (hM : M.IsMolecule) {S : Finset V} {a b : V} (hv : Src.IsSomeVine γ M S a b) (p : ℕ) :
    ∃ c : IngCodeG, c.Wf ∧ 2 ≤ c.size ∧ ∃ lab : V → ℕ, Set.InjOn lab S ∧
      S.image lab = Finset.Ico p (p + c.size) ∧ lab a = p ∧ lab b = p + c.size - 1 ∧
      WaveTurbulence.ClassCount.groupArcs M S lab =
        ((ingArcsG c (WaveTurbulence.ClassCount.ingPosOf p c.size c.swap) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
  classical
  have hB := Src.isBlock_of_isSomeVine hv
  have hab : a ≠ b := hB.2.2.2.1
  -- drawn (bad) vines: main's codes
  have drawn : ∀ X : VineType, M.IsVine X S a b → ∃ c : IngCodeG, c.Wf ∧ 2 ≤ c.size ∧ ∃ lab : V → ℕ,
      Set.InjOn lab S ∧ S.image lab = Finset.Ico p (p + c.size) ∧ lab a = p ∧ lab b = p + c.size - 1 ∧
      WaveTurbulence.ClassCount.groupArcs M S lab =
        ((ingArcsG c (WaveTurbulence.ClassCount.ingPosOf p c.size c.swap) : List (ℕ × ℕ)) : Multiset (ℕ × ℕ)) := by
    intro X hX
    obtain ⟨-, ⟨R⟩⟩ := Vine.isVine_iff_realization.mp hX
    obtain ⟨c, hwf, hsz, hinj, himg, hpa, hpb, harcs⟩ :=
      WaveTurbulence.ClassCount.vine_chain_code M R hab hB.2.1 hB.2.2.1 p
    refine ⟨c.toG, toG_wf hwf, hsz, _, hinj, himg, hpa, hpb, ?_⟩
    rw [harcs, ingArcs_toG]
    rfl
  rcases hv with ⟨-, h | h | h⟩ | ⟨hγ', X, h⟩
  · exact drawn _ h
  · exact drawn _ h
  · -- a T-vine: a band code
    obtain ⟨g, hginj, hgimg, hga, hgb, hadm⟩ := tvine_band_labelling hS hM h
    obtain ⟨l, hl, hlm⟩ := exists_band_code S.card _ hadm
    have hn : 2 ≤ S.card := by
      have := card_le_card (show ({a, b} : Finset V) ⊆ S by
        intro v hv; rcases mem_insert.mp hv with rfl | hv
        · exact hB.2.1
        · rw [mem_singleton.mp hv]; exact hB.2.2.1)
      rwa [card_pair hab] at this
    let c : IngCodeG := ⟨S.card, l, false⟩
    have hgS : ∀ v ∈ S, g v < S.card := fun v hv => by
      have : g v ∈ S.image g := mem_image_of_mem g hv
      rw [hgimg, mem_range] at this; exact this
    refine ⟨c, band_wf hn hl false, hn, fun v => WaveTurbulence.ClassCount.ingPosOf p S.card false (g v),
      ?_, ?_, ?_, ?_, ?_⟩
    · intro v1 hv1 v2 hv2 h12
      have := WaveTurbulence.ClassCount.ingPosOf_inj (sz := S.card) (sw := false) (hgS v1 hv1) (hgS v2 hv2)
        (by simpa [WaveTurbulence.ClassCount.ingPosOf_add p (by omega : 1 ≤ S.card)] using h12)
      exact hginj hv1 hv2 this
    · ext y
      simp only [mem_image, mem_Ico]
      constructor
      · rintro ⟨v, hv, rfl⟩
        have := WaveTurbulence.ClassCount.ingPosOf_lt hn (sw := false) (hgS v hv)
        rw [WaveTurbulence.ClassCount.ingPosOf_add p (by omega : 1 ≤ S.card)]
        change p ≤ _ ∧ _ < p + S.card
        omega
      · rintro ⟨h1, h2⟩
        have hcs : c.size = S.card := rfl
        rw [hcs] at h2
        obtain ⟨t, ht, ht'⟩ := WaveTurbulence.ClassCount.ingPosOf_surj hn false (y := y - p) (by omega)
        have : t ∈ S.image g := by rw [hgimg, mem_range]; exact ht
        obtain ⟨v, hv, hvt⟩ := mem_image.mp this
        refine ⟨v, hv, ?_⟩
        rw [hvt, WaveTurbulence.ClassCount.ingPosOf_add p (by omega : 1 ≤ S.card), ht']
        omega
    · simp [hga, WaveTurbulence.ClassCount.ingPosOf]
    · simp [hgb, WaveTurbulence.ClassCount.ingPosOf, c, IngCodeG.size]
    · rw [show (fun v => WaveTurbulence.ClassCount.ingPosOf p S.card false (g v)) =
        WaveTurbulence.ClassCount.ingPosOf p S.card false ∘ g from rfl, groupArcs_comp, ← hlm]
      simp [ingArcsG, c, IngCodeG.size]
  · exact absurd hγ (by linarith)

end WaveTurbulence.GammaLow.Fama.ClassCount
