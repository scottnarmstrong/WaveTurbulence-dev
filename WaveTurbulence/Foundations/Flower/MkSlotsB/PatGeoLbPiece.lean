/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoLb
public import WaveTurbulence.Foundations.Flower.MkSlotsB.PatGeoU

/-! # B3s-HELPER3 B4 (R187): the lower bounds of the class piece

`lbAt J pat t s a Mk c` (`lbOf … mkF a` at the class marking): the representative's `lbS` (free core, a pinned native
top attached below) read at the old name of the `G_sb` branch `c`. By `pinnedTop_freeClock_cases` it is `some s`
exactly at the free `G_sb` atoms whose core is the garden parent of a pinned native couple root of a cap pair
(T1's root: `dParent`-pinned, or a capped flower parent — the latter excluded by `|X.lonePath| ≥ 2`, see
`PatGeoT1`).

* `lbAt_spec`: lower-bounded atoms are free, protected, in layer `p`;
* **`pieceRest_patLb`**, `pieceRest_patLbJ`: the six B3s fields and R187's `lb_free`, `lb_prot`, `lb_layer` for the
  pattern piece with `lb := lbOf J pat t s mkF a`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsB

variable {w : ℕ}

/-- `lbS` on a decoded garden: lower-bounded cores are free, protected, in layer `p`. -/
theorem lbS_spec_decoded {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (LG : LayeredGarden w)
    (hspec : layeredReconstruction D hS layer hLayer = LG) (hd : D.Decodes hS LG.garden) (J : Finset (Fin w))
    (pat : Fin w → FixPat) (t s : ℝ) {p : ℕ} (hG : CapGeo LG J p) (kSel : Fin w → Option ℕ) (c : GBranch S.tree)
    (h : (lbS D hS (fixCap (layeredReconstruction D hS layer hLayer) J pat t s) s c).isSome) :
    fixCap LG J pat t s (D.decodedCoreBranch hS hd c) = none ∧
      (D.decodedCoreBranch hS hd c).toNode ∈ protI LG J pat t s kSel ∧
      LG.layer (D.decodedCoreBranch hS hd c).toNode = p := by
  subst hspec
  exact lbS_spec D hS layer hLayer J hG.cap_leaf pat t s hG kSel c h

theorem lbS_value {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (fixG : GBranch (D.forest hS) → Option ℝ)
    (s : ℝ) (c : GBranch S.tree) (x : ℝ) (h : lbS D hS fixG s c = some x) : x = s := by
  unfold lbS at h
  split_ifs at h
  exact (Option.some.inj h).symm

section Piece
variable (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (a : PrescribedPrimeGarden w)

/-- **The lower bounds of the piece at a marked set `Mk`.** -/
def lbAt (Mk : Set (Stage1.CLVine a.prime.skeleton)) (c : GBranch (stM a Mk).G.tree) : Option ℝ :=
  lbS a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) s ((stM a Mk).M.ob c)

/-- **The lower bounds of the class piece** (`lbAt` at the class marking `classMk mkF a`). -/
abbrev lbOf (mkF : Stage1Mk.MarkFn w) : GBranch (stA mkF a).G.tree → Option ℝ :=
  lbAt J pat t s a (classMk mkF a)

theorem lbAt_value (Mk : Set (Stage1.CLVine a.prime.skeleton)) (c : GBranch (stM a Mk).G.tree) (x : ℝ)
    (h : lbAt J pat t s a Mk c = some x) : x = s :=
  lbS_value _ _ _ s _ x h

/-- **Lower-bounded atoms are free, protected and in layer `p`.** -/
theorem lbAt_spec (Mk : Set (Stage1.CLVine a.prime.skeleton)) {p : ℕ} (hG : CapGeo a.layered J p)
    (kSel : Fin w → Option ℕ) (c : GBranch (stM a Mk).G.tree) (h : (lbAt J pat t s a Mk c).isSome) :
    fixAt J pat t s a Mk c = none ∧ (coreAt a Mk c).toNode ∈ protI a.layered J pat t s kSel ∧
      a.layered.layer (coreAt a Mk c).toNode = p :=
  lbS_spec_decoded a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) a.layered
    (sourceLayer_reconstructs a) a.prime.decodes J pat t s hG kSel _ h

end Piece

/-- **The six B3s fields and R187's three `lb` fields for the pattern piece with the lower bounds `lbOf`.** -/
theorem pieceRest_patLb (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (p : ℕ) (pat : Fin (2 * R) → FixPat)
    (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R)) (hG : CapGeo a.layered J p)
    (hpat : CapPatValid a.layered J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf a.layered.garden.tree, IsCapFlower a.layered J ℓ ∧ ℓ.1.1 = j)
    (t s : ℝ) (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1) (kSel : Fin (2 * R) → Option ℕ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (flw : GBranch (stA mkF a).G.tree → Fin 3 → Prop) (cθ : ℝ) :
    PieceRestB3s (classPiece P mkF a (protOf J pat t s kSel mkF a) (protI a.layered J pat t s kSel).card
      (fixOf J pat t s mkF a) (fun _ => none) (sibIndOf J mkF a dag flw) (lbOf J pat t s a mkF)) cθ where
  prot_card := (card_protOf_le J _ t s kSel mkF a).trans (Nat.le_mul_of_pos_left _ (by norm_num))
  fix_prot b hb := fixOf_prot b hb
  fix_layer b x hb := by
    have hb' : fixOf J pat t s mkF a b = some x := hb
    have := fixOf_val J pat t s mkF a hG hpat hroot hs ht b x hb'
    exact ⟨this.1.le, this.2.1⟩
  filt_ok a q hq := by
    change (none : Option (ℝ × SchwartzMap ℝ ℂ)) = some q at hq
    exact absurd hq (by simp)
  ind_ok k := sibIndOf_mem J mkF a dag flw k
  ind_local k k' h := sibIndOf_local J pat t s kSel mkF a dag flw k k'
    fun c hc i => (h c (Finset.mem_union_right _ hc) i).1
  lb_free b hb := (lbAt_spec J pat t s a (classMk mkF a) hG kSel b hb).1
  lb_prot b hb := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (lbAt_spec J pat t s a (classMk mkF a) hG kSel b hb).2.1⟩
  lb_layer b x hb := by
    have hb' : lbAt J pat t s a (classMk mkF a) b = some x := hb
    have hx := lbAt_value J pat t s a _ b x hb'
    have hl := (lbAt_spec J pat t s a (classMk mkF a) hG kSel b (by rw [hb']; rfl)).2.2
    show (a.layered.layer (coreOf mkF a b).toNode : ℝ) ≤ x ∧ x ≤ a.layered.layer (coreOf mkF a b).toNode + 1
    rw [show coreOf mkF a b = coreAt a (classMk mkF a) b from rfl, hl, hx]
    exact ⟨hs.1.le, by linarith [hs.2]⟩

/-- `pieceRest_patLb` from `J.card = R`. -/
theorem pieceRest_patLbJ (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (hJ : J.card = R) (p : ℕ)
    (pat : Fin (2 * R) → FixPat) (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))
    (hG : CapGeo a.layered J p) (hpat : CapPatValid a.layered J pat p) (hpl : a.layered.garden.IsPlain)
    (hirr : a.layered.garden.Irreducible)
    (t s : ℝ) (hs : s ∈ Ioo (p : ℝ) t) (ht : t < p + 1) (kSel : Fin (2 * R) → Option ℕ)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (flw : GBranch (stA mkF a).G.tree → Fin 3 → Prop) (cθ : ℝ) :
    PieceRestB3s (classPiece P mkF a (protOf J pat t s kSel mkF a) (protI a.layered J pat t s kSel).card
      (fixOf J pat t s mkF a) (fun _ => none) (sibIndOf J mkF a dag flw) (lbOf J pat t s a mkF)) cθ :=
  pieceRest_patLb P J p pat mkF a hG hpat (exists_capFlower_of_capGeo hG hpl hirr (by rw [hJ])) t s hs ht kSel dag
    flw cθ

end WaveTurbulence.Flower.MkSlotsB
