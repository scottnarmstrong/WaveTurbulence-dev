/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngVNS
public import WaveTurbulence.Foundations.Stage1.RepAnalytic.CentreSum

/-! # B3s-HELPER7 (general assembly): the centre-indexed outer mode form and the engine statement `CentreEngine`

Ruling of B3s on HELPER8's S2 (MkSlotsO/PROGRESS.md 15:40, MkSlots/HANDOFF.md "S1/S2 decision"): on every chain slot
of a NON-root branch of `G_sb` the slot superposition may depend on a NODE CENTRE `x : Fin d → ℤ` and is only valid for
the slot momenta in the node ball of `x` (`MkSlotsI.GenSlotObligationAt`, revision 3), because the D3/D6 gates bound
protected objects per output lattice ball. The general assembly (helper 7) therefore inserts at those chain slots
main's partition of unity in the slot momentum and produces the class value in the CENTRE-INDEXED OUTER MODE FORM:
`val = Σ_i sgn i · Σ'_X Σ'_ξ (∏_t w) · outerValMμD … (Zw · chiX X) …` over centre assignments `X` of the centred slots,
where the slot family at `X` is `famX (fam₀ i) (famC i) X` (`fam₀ i` on leaf-pair slots and root chain slots, the
centre-`X c` chain piece `famC i c (X c)` on the chain slot of the non-root branch `c`). Helper 9 (area MkSlotsE)
proves the engine **`CentreEngine`** from it.

* `CentredSlot G` (non-root branches of `G`, i.e. the centred chain slots `.inr c`), `IsCentred`;
* `ChainPiece d`: an UNLOCALIZED chain-slot superposition (main's `SlotFam` fields at one chain slot: no `a_supp`);
  `ChainPiece.empty`;
* `pieceAtX famC X s`: the centre-`X` piece at a centred slot, empty elsewhere;
* **`famX fam₀ famC X`**: the slot family at the centre assignment `X` (α's `MkSlots.combineFam` pattern: the modes of
  `fam₀` at weight `0` on centred slots plus the piece modes);
* **`chiX L base X z`** `= ∏_{c centred} chiC d (X c) (base + latticePoint L (z c))`, with main's
  `RepAnalytic.chiC d x k = chi d x k` (`Stage1/RepAnalytic/Partition.lean`, `CentreSum.lean`): the partition of
  unity `RepAnalytic.hasSum_chi : HasSum (fun x => chi d x k) 1`, `chi_nonneg`, support in the unit ball
  (`norm_sub_le_one_of_chi_ne_zero : chi d x k ≠ 0 → ‖k - latPt d x‖ ≤ 1`); hence (product over the finitely many
  centred slots, main's `RepAnalytic.hasSum_node_chi` pattern) `Σ_X chiX L base X z = 1` for every decoration `z`
  (`hasSum_chiX`);
* **`CentreEngine`**: δ's S1 engine `MkSlotsS.representsIntMKSel_of_vineModesFixD` (W:MkSlotsS/EngVNS.lean) with the
  slot family `fam i` replaced by `famX (fam₀ i) (famC i) X`, the moment hypothesis `hμ` and the hinge hypothesis
  `hhinge` required for EVERY centre assignment `X` (uniformly: the bounds `μs`, `lf`, `M0`, … do not depend on `X`;
  they are NOT summed over `X`), and `hval` in the centre-indexed form. The engine may restrict `Σ'_X` to the node-centre
  assignments compatible with the leaf-pair centres of `ξ` (main's `RepAnalytic.nodeCentreSet`,
  `nodeCentreAdm_of_prod_ne_zero`): the other terms vanish since the leaf-pair amplitudes are localized and
  `chiX X z = 0`; at most `nodeBallCard d ^ m` assignments remain per `ξ` (`nodeCentreSet_finite_card`).

**Reduction to δ's engine.** If `famC i c x` does not depend on the centre `x`, then (`Σ_X chiX X z = 1`, all sums
absolutely convergent) the centre-indexed `hval` is δ's `hval` for the family `famX (fam₀ i) (famC i) 0`, so
`CentreEngine`'s conclusion is that of `MkSlotsS.representsIntMKSel_of_vineModesFixD` (the centre-free engine is the
special case). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.Induct WaveTurbulence.LGSpine WaveTurbulence.Represents
  WaveTurbulence.RepAnalytic WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton TTree
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.MkSlots
  WaveTurbulence.Flower.MkSlotsS
open scoped ENNReal

namespace WaveTurbulence.Flower.MkSlotsI

variable {w d : ℕ}

/-! ## Centred slots and chain pieces -/

/-- The centred slots of `G`: the non-root branches (their chain slots `.inr c` carry centre-indexed families). -/
abbrev CentredSlot (G : Garden w) : Type := {c : GBranch G.tree // c.1.2 ≠ []}

/-- A slot is centred: the chain slot of a non-root branch. -/
def IsCentred {G : Garden w} : ReplacementSlot G → Prop
  | .inl _ => False
  | .inr c => c.1.2 ≠ []

/-- **An unlocalized chain-slot superposition** (main's `SlotFam` fields at one chain slot, no localization). -/
structure ChainPiece (d : ℕ) where
  Λ : Type
  cnt : Countable Λ
  w : Λ → ℝ
  m : Λ → Fin 2 → ℤ
  a : Λ → Mom d → ℂ
  w_nn : ∀ l, 0 ≤ w l
  w_sum : Summable w
  a_one : ∀ l k, ‖a l k‖ ≤ 1
  a_snorm : ∀ l, SNorm (30 * d) 0 (a l) ≤ 1

/-- The empty chain piece. -/
def ChainPiece.empty (d : ℕ) : ChainPiece d where
  Λ := Empty
  cnt := inferInstance
  w := Empty.elim
  m := Empty.elim
  a := Empty.elim
  w_nn := fun l => l.elim
  w_sum := summable_empty
  a_one := fun l => l.elim
  a_snorm := fun l => l.elim

open scoped Classical in
/-- The centre-`X` piece at a centred slot (empty on the other slots). -/
def pieceAtX {G : Garden w} (famC : CentredSlot G → (Fin d → ℤ) → ChainPiece d)
    (X : CentredSlot G → (Fin d → ℤ)) : ReplacementSlot G → ChainPiece d
  | .inl _ => ChainPiece.empty d
  | .inr c => if h : c.1.2 ≠ [] then famC ⟨c, h⟩ (X ⟨c, h⟩) else ChainPiece.empty d

open scoped Classical in
/-- **The slot family at the centre assignment `X`**: `fam₀` off the centred slots, the centre-`X` chain pieces on
them (the `fam₀` modes are kept at weight `0` on the centred slots, as α's `combineFam`). -/
def famX {G : Garden w} (fam₀ : SlotFam G d) (famC : CentredSlot G → (Fin d → ℤ) → ChainPiece d)
    (X : CentredSlot G → (Fin d → ℤ)) : SlotFam G d where
  Λ s := fam₀.Λ s ⊕ (pieceAtX famC X s).Λ
  cnt s := by
    haveI := fam₀.cnt s
    haveI := (pieceAtX famC X s).cnt
    infer_instance
  w s := Sum.elim (fun l => if IsCentred s then 0 else fam₀.w s l) (pieceAtX famC X s).w
  m s := Sum.elim (fam₀.m s) (pieceAtX famC X s).m
  n s := Sum.elim (fam₀.n s) (fun _ => 0)
  a s := Sum.elim (fam₀.a s) (pieceAtX famC X s).a
  w_nn s l := by
    rcases l with l | l
    · show 0 ≤ (if IsCentred s then 0 else fam₀.w s l)
      split_ifs
      · exact le_rfl
      · exact fam₀.w_nn s l
    · exact (pieceAtX famC X s).w_nn l
  w_sum s := by
    refine Summable.sum _ ?_ ?_
    · by_cases h : IsCentred s
      · simp only [Function.comp_def, Sum.elim_inl, h, ite_true]
        exact summable_zero
      · simp only [Function.comp_def, Sum.elim_inl, h, ite_false]
        exact fam₀.w_sum s
    · simp only [Function.comp_def, Sum.elim_inr]
      exact (pieceAtX famC X s).w_sum
  a_one s l k := by
    rcases l with l | l
    · exact fam₀.a_one s l k
    · exact (pieceAtX famC X s).a_one l k
  a_snorm s l := by
    rcases l with l | l
    · exact fam₀.a_snorm s l
    · exact (pieceAtX famC X s).a_snorm l
  a_supp q l k hk := by
    rcases l with l | l
    · exact fam₀.a_supp q l k hk
    · exact l.elim

/-- **The node partition at the centred slots**: `∏_{c centred} chi d (X c) (k_c)` at the slot momenta
`k_c = base + latticePoint L (z c)` (main's `RepAnalytic.chiC`). -/
def chiX {G : Garden w} (L : ℝ) (base : Mom d) (X : CentredSlot G → (Fin d → ℤ)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) : ℂ :=
  ∏ c : CentredSlot G, chiC d (X c) (base + latticePoint L (z.1 c.1.toNode))

/-- **The partition of unity**: `Σ_X chiX L base X z = 1` for every decoration (main's `hasSum_chi`, product over the
finitely many centred slots as in `RepAnalytic.hasSum_node_chi`). -/
theorem hasSum_chiX {G : Garden w} (L : ℝ) (base : Mom d) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration G d roots 0) :
    HasSum (fun X : CentredSlot G → (Fin d → ℤ) => chiX L base X z) 1 := by
  classical
  have hs : ∀ c : CentredSlot G, Summable fun m : Fin d → ℤ =>
      ‖chi d m (base + latticePoint L (z.1 c.1.toNode))‖ := fun c => by
    have := (hasSum_chi d (base + latticePoint L (z.1 c.1.toNode))).summable
    simpa [Real.norm_of_nonneg (chi_nonneg d _ _)] using this
  have := (VineEstS3.Eng.hasSum_pi_prod (M := Fin d → ℤ) (𝕜 := ℝ)
    (fun c : CentredSlot G => fun m => chi d m (base + latticePoint L (z.1 c.1.toNode))) hs).2
  have h1 : HasSum (fun X : CentredSlot G → (Fin d → ℤ) =>
      ∏ c, chi d (X c) (base + latticePoint L (z.1 c.1.toNode))) 1 := by
    simpa [(hasSum_chi d _).tsum_eq] using this
  have h2 := (Complex.ofRealCLM.hasSum h1)
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, Complex.ofReal_prod] at h2
  exact h2

/-! ## The engine statement -/

end WaveTurbulence.Flower.MkSlotsI
