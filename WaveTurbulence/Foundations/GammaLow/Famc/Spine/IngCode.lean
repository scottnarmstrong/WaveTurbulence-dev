/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.Band
public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitFamily
import Mathlib.Tactic
/-! # Ingredient codes over `𝒱_γ` (packet L5a, items H, I)

Main's class count encodes every vine ingredient by an `IngCode` (template, slot rung counts, swap, orientation) and
uses only: its size, a well-formedness predicate, its arc list `ingArcs c pos`, the finite sets `ingCodesAt w` of codes
with `w + 1` atoms, the bound `card_ingCodesAt_le'`, and (per ingredient) `vine_chain_code`. `IngCodeG` is the same
API with a code given directly by its arc list: main's drawn codes embed (`ingCodeToG`), and T-vines get band codes
(`Code/Band.lean`). Well-formedness *is* membership in the counted set, so the count is immediate. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open Finset

/-- An ingredient code: the number of atoms, the directed arcs on labels `0 … n − 1` (joints `0`, `1`), and the swap
bit ordering the joints along the chain (main's `ClassCount.IngCode` with the arcs made explicit). -/
structure IngCodeG where
  n : ℕ
  arcs : List (ℕ × ℕ)
  swap : Bool
deriving DecidableEq

/-- The number of atoms. -/
def IngCodeG.size (c : IngCodeG) : ℕ := c.n

/-- Main's drawn code as an explicit arc list. -/
def ingCodeToG (c : WaveTurbulence.ClassCount.IngCode) : IngCodeG :=
  ⟨c.size, WaveTurbulence.ClassCount.ingArcs c id, c.swap⟩

/-- The codes with `w + 1` atoms: main's drawn codes, and the band codes. -/
noncomputable def ingCodesAtG (w : ℕ) : Finset IngCodeG :=
  (WaveTurbulence.ClassCount.ingCodesAt w).image ingCodeToG ∪
    ((bandArcLists (w + 1)) ×ˢ (univ : Finset Bool)).image fun p => ⟨w + 1, p.1, p.2⟩

/-- Well-formedness: the code is counted, with at least two atoms. -/
def IngCodeG.Wf (c : IngCodeG) : Prop := 2 ≤ c.n ∧ c ∈ ingCodesAtG (c.n - 1)

/-- The oriented arcs of a code, relabelled by `pos` (main's `ingArcs`). -/
def ingArcsG (c : IngCodeG) (pos : ℕ → ℕ) : List (ℕ × ℕ) :=
  c.arcs.map fun q => (pos q.1, pos q.2)

theorem ingArcs_toG (c : WaveTurbulence.ClassCount.IngCode) (pos : ℕ → ℕ) :
    ingArcsG (ingCodeToG c) pos = WaveTurbulence.ClassCount.ingArcs c pos := by
  unfold ingArcsG ingCodeToG WaveTurbulence.ClassCount.ingArcs
  rw [List.map_map]
  congr 1
  funext q
  simp only [Function.comp]
  split_ifs <;> rfl

theorem mem_ingCodesAtG {w : ℕ} {c : IngCodeG} (hc : c.Wf) (hs : c.size = w + 1) : c ∈ ingCodesAtG w := by
  have : c.n - 1 = w := by unfold IngCodeG.size at hs; omega
  exact this ▸ hc.2

theorem toG_wf {c : WaveTurbulence.ClassCount.IngCode} (hc : c.Wf) : (ingCodeToG c).Wf := by
  have h2 := WaveTurbulence.ClassCount.expand_n_ge c.X c.k hc.1
  refine ⟨h2, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c, ?_, rfl⟩)⟩
  exact WaveTurbulence.ClassCount.mem_ingCodesAt hc (by
    change c.size = c.size - 1 + 1
    have : 2 ≤ c.size := h2
    omega)

theorem band_wf {n : ℕ} (hn : 2 ≤ n) {l : List (ℕ × ℕ)} (hl : l ∈ bandArcLists n) (sw : Bool) :
    (⟨n, l, sw⟩ : IngCodeG).Wf := by
  refine ⟨hn, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(l, sw), ?_, ?_⟩)⟩
  · rw [show n - 1 + 1 = n by omega]; exact Finset.mem_product.mpr ⟨hl, Finset.mem_univ _⟩
  · simp only [IngCodeG.mk.injEq, and_true]; omega

theorem card_ingCodesAtG_le' (w : ℕ) (hw : 1 ≤ w) : (ingCodesAtG w).card ≤ (2 ^ 102) ^ w := by
  unfold ingCodesAtG
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := (Finset.card_image_le (s := WaveTurbulence.ClassCount.ingCodesAt w)
    (f := ingCodeToG)).trans (WaveTurbulence.ClassCount.card_ingCodesAt_le' w hw)
  have h2 : (((bandArcLists (w + 1)) ×ˢ (univ : Finset Bool)).image
      fun p => (⟨w + 1, p.1, p.2⟩ : IngCodeG)).card ≤ (2 ^ 100) ^ w * 2 := by
    refine Finset.card_image_le.trans ?_
    rw [card_product, card_univ, Fintype.card_bool]
    exact Nat.mul_le_mul_right _ (by simpa using card_bandArcLists_le' (w + 1) (by omega))
  calc _ ≤ (2 ^ 41) ^ w + (2 ^ 100) ^ w * 2 := Nat.add_le_add h1 h2
    _ ≤ (2 ^ 100) ^ w * 2 + (2 ^ 100) ^ w * 2 := by
        have : (2 ^ 41) ^ w ≤ (2 ^ 100) ^ w := Nat.pow_le_pow_left (by norm_num) w
        omega
    _ = (2 ^ 100) ^ w * 4 := by ring
    _ ≤ (2 ^ 100) ^ w * (2 ^ 2) ^ w := Nat.mul_le_mul_left _ (by
        calc (4 : ℕ) = (2 ^ 2) ^ 1 := by norm_num
          _ ≤ (2 ^ 2) ^ w := Nat.pow_le_pow_right (by norm_num) hw)
    _ = (2 ^ 102) ^ w := by rw [← mul_pow]; norm_num

end WaveTurbulence.GammaLow.Famc.ClassCount
