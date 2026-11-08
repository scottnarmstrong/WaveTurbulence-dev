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

open scoped Classical in
/-- **`CentreEngine`** — the centre-indexed selected engine (to be proved by helper 9): δ's
`MkSlotsS.representsIntMKSel_of_vineModesFixD` with the centre-indexed slot families `famX (fam₀ i) (famC i) X`
(moment and hinge hypotheses for every centre assignment `X`, uniformly) and the centre-indexed `hval`. -/
def CentreEngine : Prop :=
  ∀ {P : WTParams} {R : ℕ} (hd1 : 1 ≤ P.d) (hL1 : 1 ≤ P.L)
    (hη0 : 0 ≤ P.η)
    (π : Stage1PieceMK P.d R) (hS : π.Gsb.IsPlain) (tt : Fin (2 * R) → ℝ) (base : Mom P.d)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (selSk : GenDecoration π.Gsb P.d roots 0 → Prop)
    (hgsp : ∀ D' : SplicedKernelData π.Gsb P.d, D'.gapSpecification = π.gapSpecification →
      ∀ z : GenDecoration π.Gsb P.d roots 0,
        splicedGapIndicator π.Gsb D' P.L P.γ P.η base z.1 = if selSk z then 1 else 0)
    (Dom : Set (GBranch π.Gsb.tree → ℝ))
    (hsliceD : ∀ τ : {b : GBranch π.Gsb.tree // π.fix b = none} → ℝ,
      π.Gsb.extendFix π.fix τ ∈ Dom ↔ π.Gsb.extendFix π.fix τ ∈ fixLB π.Gsb π.layer tt π.fix π.lb)
    (hfilt : ∀ a q, π.filt a = some q → ∀ u, ‖q.2 u‖ ≤ 1) (hind : ∀ k, 0 ≤ π.ind k ∧ π.ind k ≤ 1)
    (cP : ℝ) (hcP : 0 ≤ cP)
    {J : Type} [Fintype J] [DecidableEq J]
    (route : ReplacementSlot π.Gsb → Fin 2 → ClkSrc π.Gsb ⊕ J)
    (hroute : ∀ s i, route s i = Sum.inl (argSrc hS s i) ∨ ∃ j, route s i = Sum.inr j)
    (hclk : J → Fin 3 → ClkSrc π.Gsb) (hmom : J → Fin 4 → GNode π.Gsb.tree)
    (src : J → Fin 4 → HingeDarts π.Gsb π.Cs.hinges ⊕ Fin (2 * R))
    (src_dart : ∀ j i x, src j i = Sum.inl x → ∀ z : GenDecoration π.Gsb P.d roots 0,
      bondIndex π.Gsb z.1 x.1 = z.1 (hmom j i))
    (src_root : ∀ j i r, src j i = Sum.inr r → ∀ z : GenDecoration π.Gsb P.d roots 0, z.1 (hmom j i) = roots r)
    (sel : Finset (GBranch π.Gsb.tree)) (hselclk : ∀ v ∈ sel, ∀ j i, hclk j i ≠ Sum.inr v)
    {I : Type} [Fintype I] (sgn : I → ℂ)
    (fam₀ : I → SlotFam π.Gsb P.d) (famC : I → CentredSlot π.Gsb → (Fin P.d → ℤ) → ChainPiece P.d)
    (μs : I → ReplacementSlot π.Gsb → ℝ≥0∞)
    (HkM : I → J → ℤ → (Fin 3 → ℝ) → (Fin 4 → Mom P.d) → ℂ) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (θs : ReplacementSlot π.Gsb → ℝ) (hcθ : ∀ s, 2 * c + (selE route sel s 0 + selE route sel s 1) ≤ θs s)
    (hμ : ∀ i (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) s, ∑' l, maxBracketPow (θs s) (half ((famX (fam₀ i) (famC i) X).m s l)) *
      ENNReal.ofReal ((famX (fam₀ i) (famC i) X).w s l) ≤ μs i s)
    (x K Ch : ℝ) (hx : x = P.C₁ * Real.sqrt P.δ) (hK : 1 ≤ K) (hCh : 1 ≤ Ch)
    (hC : Cchi P.d * (nodeBallCard P.d : ℝ) * (9 * K) ^ 2 * Ch ≤ P.C₁)
    (sz g : ReplacementSlot π.Gsb → ℕ) (lf : I → ReplacementSlot π.Gsb → ℝ) (hlf : ∀ i s, 0 ≤ lf i s)
    (hμb : ∀ i s, μs i s ≤ ENNReal.ofReal (K * x ^ (sz s) * P.L ^ (-(P.η ^ 8) * (g s : ℝ)) * lf i s))
    (M0 : I → J → ℝ) (cl2 gj nj : J → ℕ) (lfj : I → J → ℝ) (hlfj : ∀ i j, 0 ≤ lfj i j)
    (hM : ∀ i j, 0 ≤ M0 i j ∧ M0 i j ≤ x ^ (cl2 j) *
      P.L ^ (-(P.η ^ 8) * (gj j : ℝ) - P.η ^ 2 / 2 * (nj j : ℝ) + P.η ^ 7) * lfj i j)
    (hhinge : ∀ i (X : CentredSlot π.Gsb → (Fin P.d → ℤ)) (ξ : ∀ s, (famX (fam₀ i) (famC i) X).Λ s), ∃ (H : HingeFam J P.d) (Mh : J → ℝ),
      (∀ j c', ∑' l, H.w j c' l ≤ Mh j) ∧
      HHkPropD π.toStage1PieceD tt base roots selSk Dom hclk hmom
        (fun j => HkM i j (modLam (fun s => (famX (fam₀ i) (famC i) X).m s (ξ s)) route j)) H ∧
      ∏ j, Mh j ≤ (∏ j, (Ch * M0 i j)) *
        ∏ j, (1 + |((modLam (fun s => (famX (fam₀ i) (famC i) X).m s (ξ s)) route j : ℤ) : ℝ)|) ^ c)
    (n : ℕ) (s : ℝ)
    (hs : ∑ i, ‖sgn i‖ * ((∏ t, selF route sel t * lf i t) * ∏ j, lfj i j) ≤
      P.L ^ (7 * (47 * P.d + 2) * (sel.card : ℝ)) * s)
    (hexp : (∑ t, sz t) + ∑ j, cl2 j = n - π.Gsb.order)
    (hg : π.gsk ≤ (∑ t, g t) + ∑ j, gj j) (hb : π.bsk ≤ ∑ j, nj j) (hh : Fintype.card J ≤ π.Cs.hinges.card)
    (hJ : Fintype.card J ≤ π.Gsb.order) (val : ℂ)
    (hval : val = ∑ i, sgn i * ∑' X : CentredSlot π.Gsb → (Fin P.d → ℤ),
      ∑' ξ : ∀ t, (famX (fam₀ i) (famC i) X).Λ t, (((∏ t, (famX (fam₀ i) (famC i) X).w t (ξ t) : ℝ)) : ℂ) *
        outerValMμD π.Gsb P.L P.γ P.δ base roots tt Dom π.Cs.hinges
          (fun z => pieceAtomW π (cosetDecoration π.Gsb P.L base z.1) * (if selSk z then 1 else 0) *
            chiX P.L base X z) hS
          (fixMeasure π.fix)
          (fun t => (famX (fam₀ i) (famC i) X).a t (ξ t)) (fun t => (famX (fam₀ i) (famC i) X).m t (ξ t))
          route hclk hmom (HkM i)),
    RepresentsIntMKSel π sel n cP tt base roots s val

end WaveTurbulence.Flower.MkSlotsI
