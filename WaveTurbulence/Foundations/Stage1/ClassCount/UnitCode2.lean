/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.UnitCode1
import Mathlib.Tactic

/-!
# CLASSCOUNT: codes of ingredient vines and of vine chains

An ingredient code is a vine type `X`, a rung vector `k`, a swap bit (which joint is the template atom `0`) and one
orientation bit per bond of the expanded template.  The number of ingredient codes with `n(X, k) = w + 1` atoms is at
most `2^41 · 64^w` (`card_ingCodesAt_le`).  A unit code is a list of ingredient codes; the number of unit codes with
total weight `Σ (n_i - 1) = W` is at most `B^W` (`card_unitCodes_le`), by the recurrence over the first ingredient.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open WaveTurbulence Finset LayerCnt

/-- An ingredient code. -/
structure IngCode where
  X : VineType
  k : List ℕ
  swap : Bool
  o : List Bool
deriving DecidableEq

/-- The number of atoms of the expanded template of an ingredient code. -/
def IngCode.size (c : IngCode) : ℕ := (c.X.expand c.k).n

/-- Well-formedness: lengths match the template. -/
def IngCode.Wf (c : IngCode) : Prop :=
  c.k.length = c.X.template.slots.length ∧ c.o.length = (c.X.expand c.k).bonds.length

/-- All vine types. -/
def vineTypes : Finset VineType := {.I, .II, .III, .IV, .V, .VI, .VII, .VIII}

theorem mem_vineTypes (X : VineType) : X ∈ vineTypes := by cases X <;> simp [vineTypes]

theorem card_vineTypes : vineTypes.card ≤ 8 := by
  unfold vineTypes; decide

/-- Lists of booleans of length `L`. -/
def boolLists (L : ℕ) : Finset (List Bool) :=
  (univ : Finset (Fin L → Bool)).image List.ofFn

theorem mem_boolLists {L : ℕ} {o : List Bool} (h : o.length = L) : o ∈ boolLists L := by
  subst h
  exact Finset.mem_image.mpr ⟨o.get, Finset.mem_univ _, List.ofFn_get o⟩

theorem card_boolLists (L : ℕ) : (boolLists L).card ≤ 2 ^ L := by
  refine Finset.card_image_le.trans ?_
  simp

theorem card_bseqs_le (h : ℕ) : ∀ k, (bseqs h k).card ≤ (h + 1) ^ k
  | 0 => by simp [bseqs]
  | k + 1 => by
    unfold bseqs
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Finset.card_range, pow_succ, mul_comm]
    exact Nat.mul_le_mul_right _ (card_bseqs_le h k)

/-- The ingredient codes with `w + 1` atoms. -/
noncomputable def ingCodesAt (w : ℕ) : Finset IngCode :=
  vineTypes.biUnion (fun X => (bseqs w X.template.slots.length).biUnion (fun k =>
    if (X.expand k).n = w + 1 then
      ((boolLists (X.expand k).bonds.length) ×ˢ (univ : Finset Bool)).image
        (fun p => (⟨X, k, p.2, p.1⟩ : IngCode))
    else ∅))

theorem mem_ingCodesAt {w : ℕ} {c : IngCode} (hc : c.Wf) (hs : c.size = w + 1) : c ∈ ingCodesAt w := by
  obtain ⟨h1, h2⟩ := hc
  unfold ingCodesAt
  refine Finset.mem_biUnion.mpr ⟨c.X, mem_vineTypes _, Finset.mem_biUnion.mpr ⟨c.k, ?_, ?_⟩⟩
  · refine mem_bseqs.mpr ⟨h1, fun x hx => ?_⟩
    have := expand_entry_le c.X c.k h1 hx
    have hs' : (c.X.expand c.k).n = w + 1 := hs
    omega
  · have hs' : (c.X.expand c.k).n = w + 1 := hs
    rw [if_pos hs']
    exact Finset.mem_image.mpr ⟨(c.o, c.swap), Finset.mem_product.mpr ⟨mem_boolLists h2, Finset.mem_univ _⟩, rfl⟩

theorem card_ingCodesAt_le (w : ℕ) : (ingCodesAt w).card ≤ 8 * ((w + 1) ^ 3 * (2 ^ (28 + 3 * (w + 1)) * 2)) := by
  unfold ingCodesAt
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ X ∈ vineTypes, (( bseqs w X.template.slots.length).biUnion _).card
      ≤ ∑ _X ∈ vineTypes, ((w + 1) ^ 3 * (2 ^ (28 + 3 * (w + 1)) * 2)) := by
        apply Finset.sum_le_sum
        intro X _
        refine Finset.card_biUnion_le.trans ?_
        calc ∑ k ∈ bseqs w X.template.slots.length,
              (if (X.expand k).n = w + 1 then
                ((boolLists (X.expand k).bonds.length) ×ˢ (univ : Finset Bool)).image
                  (fun p => (⟨X, k, p.2, p.1⟩ : IngCode)) else ∅).card
            ≤ ∑ _k ∈ bseqs w X.template.slots.length, (2 ^ (28 + 3 * (w + 1)) * 2) := by
              apply Finset.sum_le_sum
              intro k hk
              split_ifs with hn
              · refine Finset.card_image_le.trans ?_
                rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
                refine Nat.mul_le_mul ((card_boolLists _).trans ?_) le_rfl
                refine Nat.pow_le_pow_right (by norm_num) ?_
                have := expand_bonds_le X k
                omega
              · simp
          _ = (bseqs w X.template.slots.length).card * (2 ^ (28 + 3 * (w + 1)) * 2) := by simp
          _ ≤ (w + 1) ^ 3 * (2 ^ (28 + 3 * (w + 1)) * 2) := by
              refine Nat.mul_le_mul_right _ ((card_bseqs_le w _).trans ?_)
              exact Nat.pow_le_pow_right (by omega) (template_slots_le X)
    _ = vineTypes.card * ((w + 1) ^ 3 * (2 ^ (28 + 3 * (w + 1)) * 2)) := by simp
    _ ≤ 8 * ((w + 1) ^ 3 * (2 ^ (28 + 3 * (w + 1)) * 2)) := Nat.mul_le_mul_right _ card_vineTypes


theorem card_ingCodesAt_le' (w : ℕ) (hw : 1 ≤ w) : (ingCodesAt w).card ≤ (2 ^ 41) ^ w := by
  refine (card_ingCodesAt_le w).trans ?_
  have h1 : (w + 1) ^ 3 ≤ 8 ^ w := by
    have : w + 1 ≤ 2 ^ w := Nat.lt_two_pow_self
    calc (w + 1) ^ 3 ≤ (2 ^ w) ^ 3 := Nat.pow_le_pow_left this 3
      _ = 8 ^ w := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  calc 8 * ((w + 1) ^ 3 * (2 ^ (28 + 3 * (w + 1)) * 2))
      ≤ 8 * (8 ^ w * (2 ^ (28 + 3 * (w + 1)) * 2)) := by gcongr
    _ = 2 ^ 35 * 8 ^ w * 8 ^ w := by
        have : (2 : ℕ) ^ (28 + 3 * (w + 1)) = 2 ^ 31 * 8 ^ w := by
          rw [show 28 + 3 * (w + 1) = 31 + 3 * w by ring, pow_add, pow_mul]; norm_num
        rw [this]; ring
    _ = 2 ^ 35 * 64 ^ w := by
        rw [mul_assoc, ← mul_pow]; norm_num
    _ ≤ (2 ^ 41) ^ w := by
        have e1 : (64 : ℕ) ^ w = 2 ^ (6 * w) := by rw [pow_mul]; norm_num
        rw [e1, ← pow_add, ← pow_mul]
        exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)


/-- The unit codes of total weight `W = Σ (n_i - 1)`. -/
noncomputable def unitCodes : ℕ → Finset (List IngCode)
  | 0 => {[]}
  | W + 1 => (Finset.range (W + 1)).attach.biUnion (fun i =>
      ((ingCodesAt (i.1 + 1)) ×ˢ unitCodes (W - i.1)).image (fun p => p.1 :: p.2))
termination_by W => W
decreasing_by omega

/-- Total weight of a unit code. -/
def unitWeight (cs : List IngCode) : ℕ := (cs.map (fun c => c.size - 1)).sum

theorem mem_unitCodes : ∀ (cs : List IngCode), (∀ c ∈ cs, c.Wf) → cs ∈ unitCodes (unitWeight cs)
  | [], _ => by simp [unitWeight, unitCodes]
  | c :: cs, h => by
    have hc : c.Wf := h c (by simp)
    have hs : 2 ≤ c.size := expand_n_ge c.X c.k hc.1
    have ih := mem_unitCodes cs (fun x hx => h x (by simp [hx]))
    have hw : unitWeight (c :: cs) = ((c.size - 2) + unitWeight cs) + 1 := by
      simp only [unitWeight, List.map_cons, List.sum_cons]; omega
    rw [hw, unitCodes]
    refine Finset.mem_biUnion.mpr ⟨⟨c.size - 2, Finset.mem_range.mpr (by omega)⟩, Finset.mem_attach _ _, ?_⟩
    refine Finset.mem_image.mpr ⟨(c, cs), Finset.mem_product.mpr ⟨?_, ?_⟩, rfl⟩
    · exact mem_ingCodesAt hc (by simp only; omega)
    · have : (c.size - 2 + unitWeight cs) - (c.size - 2) = unitWeight cs := by omega
      simp only
      rw [this]; exact ih

theorem sum_two_pow (n : ℕ) : ∑ j ∈ Finset.range n, 2 ^ j + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem geom_sum_bound (c W : ℕ) :
    ∑ i ∈ Finset.range (W + 1), c ^ (i + 1) * (2 * c) ^ (W - i) ≤ (2 * c) ^ (W + 1) := by
  have h1 : ∀ i ∈ Finset.range (W + 1), c ^ (i + 1) * (2 * c) ^ (W - i) = c ^ (W + 1) * 2 ^ (W - i) := by
    intro i hi
    have hi' : i ≤ W := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_pow, show c ^ (i + 1) * (2 ^ (W - i) * c ^ (W - i)) = c ^ (i + 1) * c ^ (W - i) * 2 ^ (W - i) by ring,
      ← pow_add, show i + 1 + (W - i) = W + 1 by omega]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, mul_pow, mul_comm (2 ^ (W + 1))]
  refine Nat.mul_le_mul_left _ ?_
  have hr := Finset.sum_range_reflect (fun j => 2 ^ j) (W + 1)
  simp only [Nat.add_sub_cancel] at hr
  rw [hr]
  have := sum_two_pow (W + 1)
  omega

theorem card_unitCodes_le : ∀ W : ℕ, (unitCodes W).card ≤ (2 ^ 42) ^ W
  | 0 => by simp [unitCodes]
  | W + 1 => by
    rw [unitCodes]
    refine Finset.card_biUnion_le.trans ?_
    have hterm : ∀ i : {x // x ∈ Finset.range (W + 1)},
        (((ingCodesAt (i.1 + 1)) ×ˢ unitCodes (W - i.1)).image (fun p => p.1 :: p.2)).card ≤
          (2 ^ 41) ^ (i.1 + 1) * (2 ^ 42) ^ (W - i.1) := by
      intro i
      refine Finset.card_image_le.trans ?_
      rw [Finset.card_product]
      have h1 := card_ingCodesAt_le' (i.1 + 1) (by omega)
      have h2 := card_unitCodes_le (W - i.1)
      exact Nat.mul_le_mul h1 h2
    refine (Finset.sum_le_sum (fun i _ => hterm i)).trans ?_
    rw [Finset.sum_attach (Finset.range (W + 1)) (fun i => (2 ^ 41) ^ (i + 1) * (2 ^ 42) ^ (W - i))]
    have := geom_sum_bound (2 ^ 41) W
    simpa using this

end WaveTurbulence.ClassCount
