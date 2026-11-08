/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.GeoSb

/-! # B3s MK-SLOTS: the six B3s fields of `MkPieceRest` for the class piece (milestone α)

For the piece `classPiece P mkF a prot nProt fix filt ind` of B4's hypothesis with the α data
* `prot = protOf …` (atoms whose core node is protected), `nProt = |Π(a)|`,
* `fix = fixOf J plain t s mkF a` (capped flower parents at `s`),
* `filt = none` (no stem filter, no selection),
* `ind = sibIndOf …` (the dagger sibling indicator at `G_sb` flower parents),
`pieceRest_alpha` proves `PieceRestB3s`: `prot_card` (`|prot| ≤ |Π| ≤ 2|Π|`), `fix_prot` (pins are seeds),
`fix_layer` (capped flower parents in layer `p`, `s ∈ (p, t)`), `filt_ok` (vacuous), `ind_ok`, `ind_local`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.Flower.Stage1MKGate WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden

namespace WaveTurbulence.Flower.MkSlots

/-- The layer of a branch of the class piece is the layer of its core branch. -/
theorem classPiece_layer (P : WTParams) {R : ℕ} (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))
    (prot : Finset (GBranch (stA mkF a).G.tree)) (nProt : ℕ) (fix : GBranch (stA mkF a).G.tree → Option ℝ)
    (filt : GBranch (stA mkF a).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stA mkF a).G.tree → Mom P.d) → ℝ) (c : GBranch (stA mkF a).G.tree) :
    (classPiece P mkF a prot nProt fix filt ind).layer c = a.layered.layer (coreOf mkF a c).toNode := rfl

/-- **The B3s fields for the α data** (no lower bounds: `lb := none`, R187's three `lb` fields are vacuous). -/
theorem pieceRest_alpha (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (p : ℕ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (hG : CapGeo a.layered J p) (t s : ℝ) (hs : s ∈ Ioo (p : ℝ) t)
    (ht : t < p + 1) (kSel : Fin (2 * R) → Option ℕ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (flw : GBranch (stA mkF a).G.tree → Fin 3 → Prop) (cθ : ℝ) :
    PieceRestB3s (classPiece P mkF a (protOf J (fun _ => FixPat.plain) t s kSel mkF a)
      (protI a.layered J (fun _ => FixPat.plain) t s kSel).card (fixOf J (fun _ => FixPat.plain) t s mkF a)
      (fun _ => none) (sibIndOf J mkF a dag flw)) cθ where
  prot_card := (card_protOf_le J _ t s kSel mkF a).trans (Nat.le_mul_of_pos_left _ (by norm_num))
  fix_prot b hb := fixOf_prot b hb
  fix_layer b x hb := by
    have hb' : fixOf J (fun _ => FixPat.plain) t s mkF a b = some x := hb
    have := ((admissibleSb_plain J p mkF a hG t s hs ht).val b x hb').1
    exact ⟨this.1, this.2⟩
  filt_ok a q hq := by
    change (none : Option (ℝ × SchwartzMap ℝ ℂ)) = some q at hq
    exact absurd hq (by simp)
  ind_ok k := sibIndOf_mem J mkF a dag flw k
  ind_local k k' h := sibIndOf_local J (fun _ => FixPat.plain) t s kSel mkF a dag flw k k'
    fun c hc i => (h c (Finset.mem_union_right _ hc) i).1
  lb_free b hb := by
    change ((none : Option ℝ)).isSome = true at hb
    simp at hb
  lb_prot b hb := by
    change ((none : Option ℝ)).isSome = true at hb
    simp at hb
  lb_layer b x hb := by
    change (none : Option ℝ) = some x at hb
    simp at hb

end WaveTurbulence.Flower.MkSlots
