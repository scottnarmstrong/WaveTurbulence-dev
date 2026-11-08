/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSubpro.Support
public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Piece
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceFinalR83
public import WaveTurbulence.Foundations.Stage1.Geometry.RedSpliceAmend7R83
public import WaveTurbulence.Foundations.Vine.A.VineNormalizedPiece

/-! # B2c MK-SUBPRO (world side), part 3: the geometry of a marked Stage-1′ piece (`SoundMKFull`)

`stage1PieceMKOf` is the marked Stage-1′ piece of the construction: main's `stage1PieceOf … σ Mk` (garden
`stSt G σ Mk`, `𝒞₁ = collectionChoices G σ Mk`, gap specification `gapSpecificationMk`) with the survivors
`survData G σ Mk prot` and B4's pin/filter/indicator data.

`soundMKFull_marked` proves `SoundMKFull` (finding F-C0-3) for it from main's hypotheses of
`stage1Piece_sound_succ_uncond` and R173 (`hMkSG`), given the fields that are not geometric (`MkPieceRest`: the
survivor/protected counts and the pin, filter and indicator facts, which B3s/B4 supply).  The geometric fields:
* `plain` … `layer_le`, `molecule` … `bond_count`, `structural`, `hingeOutsideFirst`: main's `construction_factsMk`;
* `survivors` (R169 `Structural`) and `chainOrder`: `survData_structural`, `survData_chainOrder`;
* `support` (Theorem 7.5′ (2), (4)–(6′)): `subproSupportMK_survData`;
* `tripleDesignated`, `hingeNoLoop`: main's `tripleDesignated_collectionChoicesMk`, `hingeNoLoop_collectionChoicesMk`.
-/

@[expose] public section
set_option autoImplicit false

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Finset WaveTurbulence.Reg.Skeleton
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)

namespace WaveTurbulence.Flower.MkSubpro
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs

/-- **The marked Stage-1′ piece of the construction** (main's `stage1PieceOf` at the marking `Mk`, the survivors,
and B4's protected set, pins, filters and indicator). -/
noncomputable def stage1PieceMKOf (P : WTParams) {R : ℕ} {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    (Mk : Set (Stage1.CLVine S)) (prot : Finset (GBranch (stSt S σ Mk).G.tree)) (nProt : ℕ)
    (fix : GBranch (stSt S σ Mk).G.tree → Option ℝ)
    (filt : GBranch (stSt S σ Mk).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stSt S σ Mk).G.tree → Mom P.d) → ℝ) : Stage1PieceMK P.d R where
  toStage1PieceD := VineA.NormalizedSplice.stage1PieceOf P.d hS LG hd σ Mk
  surv := survData S σ Mk prot
  nProt := nProt
  fix := fix
  filt := filt
  ind := ind

/-- The fields of `SoundMK`/`SoundMKFull` that are not geometric (copied from them verbatim): the survivor and
protected counts (B4) and the pin, filter and indicator facts (B3s/B4). -/
structure MkPieceRest {P : WTParams} {R : ℕ} (π : Stage1PieceMK P.d R) (cθ : ℝ) : Prop where
  survivors_card : π.surv.m ≤ 6 * π.nProt
  prot_card : π.surv.prot.card ≤ 2 * π.nProt
  fix_prot : ∀ b, (π.fix b).isSome → b ∈ π.surv.prot
  fix_layer : ∀ b t, π.fix b = some t → (π.layer b : ℝ) ≤ t ∧ t ≤ π.layer b + 1
  filt_ok : ∀ a q, π.filt a = some q → a ∉ π.Cs.hinges ∧ 1 ≤ q.1 ∧ (∀ u, ‖q.2 u‖ ≤ 1) ∧ filterB ⇑q.2 ≤ cθ
  ind_ok : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1
  ind_local : ∀ k k', (∀ a ∈ π.surv.joints ∪ π.surv.prot, ∀ i : Fin 3,
    k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → π.ind k = π.ind k'

/-- **`SoundMKFull` for the marked Stage-1′ piece** (F-C0-3): main's hypotheses of `stage1Piece_sound_succ_uncond`,
ruling R173 (`hMkSG`) and the non-geometric fields (`MkPieceRest`). -/
theorem soundMKFull_marked (P : WTParams) {R : ℕ} {S : Garden (2 * R)} {D : ReconstructionData S}
    (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden) (σ : Prescription S)
    {Mk : Set (Stage1.CLVine S)} (hMkSG : Mk ⊆ vinesV0 S σ)
    (hP : IsPrimeGarden S) (hI : S.Irreducible) (hbal : IsBalancedSig S.sig) (hn : 1 ≤ S.order)
    (p : ℕ) (hN : S.order ≤ P.N (p + 1) ^ 4) (hlayer : ∀ v, RegRed.coreLayer LG D hS hd v ≤ p)
    (hL : P.L ≠ 0) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (cθ : ℝ)
    (prot : Finset (GBranch (stSt S σ Mk).G.tree)) (nProt : ℕ)
    (fix : GBranch (stSt S σ Mk).G.tree → Option ℝ)
    (filt : GBranch (stSt S σ Mk).G.tree → Option (ℝ × SchwartzMap ℝ ℂ))
    (ind : (GNode (stSt S σ Mk).G.tree → Mom P.d) → ℝ)
    (hrest : MkPieceRest (stage1PieceMKOf P hS LG hd σ Mk prot nProt fix filt ind) cθ) :
    SoundMKFull (stage1PieceMKOf P hS LG hd σ Mk prot nProt fix filt ind) p base roots cθ := by
  obtain ⟨hB, hStr, hHinge⟩ := VineA.NormalizedSplice.construction_factsMk (Mk := Mk) S hP hI hbal hn σ
    (RegRed.coreLayer LG D hS hd) p (P.N (p + 1) ^ 4) hN hlayer
  exact
    { plain := hB.plain
      irreducible := hB.irreducible
      balanced := hB.balanced
      order_pos := hB.order_pos
      order_le := hB.order_le
      layer_le := hB.layer_le
      survivors := survData_structural S σ Mk prot
      survivors_card := hrest.survivors_card
      prot_card := hrest.prot_card
      molecule := hB.molecule
      connected := hB.connected
      atom_count := hB.atom_count
      bond_count := hB.bond_count
      structural := hStr
      support := fun z h1 h2 =>
        subproSupportMK_survData σ hMkSG _ rfl hB.plain hL P.γ P.η base roots z h1 h2 prot
      hingeOutsideFirst := hHinge
      tripleDesignated := VineA.NormalizedSplice.tripleDesignated_collectionChoicesMk
        (WaveTurbulence.Mole.garden_isMolecule S) (RedSplice.prime_noTriple S hP) σ
      hingeNoLoop := VineA.NormalizedSplice.hingeNoLoop_collectionChoicesMk σ
      chainOrder := survData_chainOrder S σ Mk prot
      fix_prot := hrest.fix_prot
      fix_layer := hrest.fix_layer
      filt_ok := hrest.filt_ok
      ind_ok := hrest.ind_ok
      ind_local := hrest.ind_local }

end WaveTurbulence.Flower.MkSubpro
