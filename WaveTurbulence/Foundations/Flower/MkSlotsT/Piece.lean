/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Profile

/-! # B3s-HELPER5 (γ) T4 + T2 data: the stem filters of a piece, on a splice shape

For a skeleton `S` with data `D`, a splice shape `Φ : SpliceShape blk Gsb` and a list of radii `rad z` at every
branch `z` of the reconstruction `LG = layeredReconstruction D hS layer hLayer` (the generic stem filter family of
`Weight.lean`), the three pieces of data the chain consumes:
* **`filtStem`** (kind (a), atom filters of the piece): at a non-hinge `G_sb` branch `c` whose core is a capped-stem
  node with radii `r :: rs`, the filter `(r₀, stemProfile …)` with `r₀ = foldl min r rs` (so every layer ratio is
  `≤ 1`); `none` elsewhere (in particular at every hinge, `filtStem_hinge`);
* **`SUStem`** (kind (b), T2: B3-2's per-unit radius lists): the radii of the core of the upper joint of unit `j` if it
  is a capped-stem node, `[]` otherwise;
* **`ThetaStem`** (kind (c), the per-slot factors `Θs`): the product of the node filters over the non-core capped-stem
  nodes of the slot.

**T4 (the member weight factor, on every decoration)** `stemFiltG_factor`: under `StemRet` (T1),
`stemFiltG LG J rad k = (∏_c filtW (filtStem c) (Ω_{Φ.br c})) · (∏_j nodeWeight (topFilterWeightL (SUStem j)) …) ·
∏_s ThetaStem s`, with `k` the coset decoration of `κ`, the atom and top factors read on the collapsed skeleton
decoration, and `ThetaStem s` reading only the native nodes of `s` (`slotFac_congr`).

**`filt_ok`** (`filtStem_ok`): `filt c = some q → c ∉ hinges ∧ 1 ≤ q.1 ∧ ‖q.2 u‖ ≤ 1`, for radii `≥ 1`; the
`𝔟`-norm of a one-layer filter is `filterB χ₀` (`Profile.filterB_stemProfile_single`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs
open WaveTurbulence.VineB (SpliceShape Ret Disj)
open WaveTurbulence.RedSplice (CLBlock)

namespace WaveTurbulence.Flower.MkSlotsT

variable {w d : ℕ}

/-! ## The base radius -/

/-- The smallest radius of a nonempty list. -/
def rmin (r : ℝ) (rs : List ℝ) : ℝ := rs.foldl min r

theorem rmin_le_head (r : ℝ) (rs : List ℝ) : rmin r rs ≤ r := by
  unfold rmin
  induction rs generalizing r with
  | nil => exact le_rfl
  | cons r' rs ih => exact (ih (min r r')).trans (min_le_left _ _)

theorem le_rmin (r : ℝ) (rs : List ℝ) (c : ℝ) (hr : c ≤ r) (hrs : ∀ x ∈ rs, c ≤ x) : c ≤ rmin r rs := by
  unfold rmin
  induction rs generalizing r with
  | nil => exact hr
  | cons r' rs ih =>
    exact ih (min r r') (le_min hr (hrs r' (List.mem_cons_self ..))) fun x hx => hrs x (List.mem_cons_of_mem _ hx)

theorem one_le_rmin (r : ℝ) (rs : List ℝ) (hrs : ∀ x ∈ r :: rs, 1 ≤ x) : 1 ≤ rmin r rs :=
  le_rmin r rs 1 (hrs r (List.mem_cons_self ..)) fun x hx => hrs x (List.mem_cons_of_mem _ hx)

theorem rmin_div_ne_zero (r : ℝ) (rs : List ℝ) (hrs : ∀ x ∈ r :: rs, 1 ≤ x) : rmin r rs / r ≠ 0 := by
  have h1 := one_le_rmin r rs hrs
  have h2 : 1 ≤ r := hrs r (List.mem_cons_self ..)
  exact div_ne_zero (by linarith) (by linarith)

/-- The atom filter of a node with radii `rs` (all radii `≥ 1`): `none` without radii. -/
def filtOfRad (rs : List ℝ) (hrs : ∀ x ∈ rs, 1 ≤ x) : Option (ℝ × SchwartzMap ℝ ℂ) :=
  match rs, hrs with
  | [], _ => none
  | r :: rs, h => some (rmin r rs, stemProfile r rs (rmin r rs) (rmin_div_ne_zero r rs h))

/-- The atom weight read by the engine (`(filt a).elim 1 fun q => q.2 (Ω / q.1)`). -/
def filtW (q : Option (ℝ × SchwartzMap ℝ ℂ)) (x : ℝ) : ℂ := q.elim 1 fun q => q.2 (x / q.1)

/-- **The atom filter reproduces the node's filters.** -/
theorem filtW_filtOfRad (rs : List ℝ) (hrs : ∀ x ∈ rs, 1 ≤ x) (x : ℝ) :
    filtW (filtOfRad rs hrs) x = (radProd rs x : ℂ) := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    have h1 := one_le_rmin r rs hrs
    show stemProfile r rs (rmin r rs) (rmin_div_ne_zero r rs hrs) (x / rmin r rs) = _
    exact stemProfile_apply_div r rs (rmin r rs) _ (by linarith) x

/-- **`filt_ok` for the atom filters** (all radii `≥ 1`). -/
theorem filtOfRad_ok (rs : List ℝ) (hrs : ∀ x ∈ rs, 1 ≤ x) (q : ℝ × SchwartzMap ℝ ℂ)
    (hq : filtOfRad rs hrs = some q) : 1 ≤ q.1 ∧ ∀ u, ‖q.2 u‖ ≤ 1 := by
  cases rs with
  | nil => cases hq
  | cons r rs =>
    simp only [filtOfRad, Option.some.injEq] at hq
    subst hq
    exact ⟨one_le_rmin r rs hrs, fun u => norm_stemProfile_le r rs _ (rmin_div_ne_zero r rs hrs) u⟩

/-! ## The data on a splice shape -/

section Data
variable {S Gsb : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) {ι : Type} [Fintype ι] [DecidableEq ι]
  {blk : ι → CLBlock S} (Φ : SpliceShape blk Gsb) (hd : Disj blk)
  (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (J : Finset (Fin w))
  (rad : GBranch (layeredReconstruction D hS layer hLayer).garden.tree → List ℝ)
  (hrad : ∀ b, ∀ x ∈ rad b, 1 ≤ x)

/-- The core branch of `β`, typed as a branch of the layered reconstruction. -/
abbrev coreLG (β : GBranch S.tree) : GBranch (layeredReconstruction D hS layer hLayer).garden.tree :=
  D.coreBranch hS β

/-- A capped-stem branch of the reconstruction (a member of some `stemSetCap`). -/
def StemB (b : GBranch (layeredReconstruction D hS layer hLayer).garden.tree) : Prop :=
  ∃ j, b ∈ stemSetCap (layeredReconstruction D hS layer hLayer) J j

/-- **The atom filters** (kind (a)). -/
def filtStem (c : GBranch Gsb.tree) : Option (ℝ × SchwartzMap ℝ ℂ) :=
  if c ∉ Φ.hinges hd ∧ StemB D hS layer hLayer J (coreLG D hS layer hLayer (Φ.br c)) then
    filtOfRad (rad (coreLG D hS layer hLayer (Φ.br c))) (hrad _)
  else none

/-- **T2: the per-unit radius lists** (kind (b)). -/
def SUStem (j : ι) : List ℝ :=
  if StemB D hS layer hLayer J (coreLG D hS layer hLayer (blk j).upper) then
    rad (coreLG D hS layer hLayer (blk j).upper) else []

/-- **The per-slot factors** (kind (c)). -/
def ThetaStem (k : GNode (D.forest hS) → Mom d) (s : ReplacementSlot S) : ℂ :=
  slotFac D hS (brExt (stemBW (layeredReconstruction D hS layer hLayer) J rad k)) s

omit [DecidableEq ι] in
theorem filtStem_hinge (c : GBranch Gsb.tree) (hc : c ∈ Φ.hinges hd) :
    filtStem D hS Φ hd layer hLayer J rad hrad c = none := by
  unfold filtStem
  rw [if_neg (fun h => h.1 hc)]

omit [DecidableEq ι] in
/-- **`filt_ok` (without the `𝔟`-norm)** for the atom filters. -/
theorem filtStem_ok (c : GBranch Gsb.tree) (q : ℝ × SchwartzMap ℝ ℂ)
    (hq : filtStem D hS Φ hd layer hLayer J rad hrad c = some q) :
    c ∉ Φ.hinges hd ∧ 1 ≤ q.1 ∧ ∀ u, ‖q.2 u‖ ≤ 1 := by
  unfold filtStem at hq
  split_ifs at hq with h
  · exact ⟨h.1, filtOfRad_ok _ _ q hq⟩

omit [Fintype ι] [DecidableEq ι] in
include hrad in
theorem SUStem_pos (j : ι) : ∀ s ∈ SUStem D hS layer hLayer J rad (blk := blk) j, 0 < s := by
  intro s hs
  unfold SUStem at hs
  split_ifs at hs
  · exact lt_of_lt_of_le zero_lt_one (hrad _ s hs)
  · cases hs

variable {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}

/-- **T4 (the member weight factor).** Under `StemRet`, on every decoration `κ` of the reconstruction: the generic
stem filter weight is the atom part (the piece's atom filters `filtStem` at the skeleton resonance factors
`Ω_{Φ.br c}` of the collapsed decoration) times the top part (B3-2's unit top filters at radii `SUStem`) times the
slot part (`ThetaStem`). -/
theorem stemFiltG_factor (hR : StemRet S D.tree blk (layeredReconstruction D hS layer hLayer) J)
    (κ : GenDecoration (D.garden hS) d n nfl) (L : ℝ) (base : Mom d) :
    (stemFiltG (layeredReconstruction D hS layer hLayer) J rad
        (cosetDecoration (D.garden hS) L base κ.1) : ℂ) =
      (∏ c ∈ univ.filter (fun c => c ∉ Φ.hinges hd),
          filtW (filtStem D hS Φ hd layer hLayer J rad hrad c)
            (omegaNode S (cosetDecoration S L base (collapseGenDecoration D hS κ).1) (Φ.br c))) *
        (∏ j, VineSpaceK.nodeWeight (V5W2L.topFilterWeightL (SUStem D hS layer hLayer J rad (blk := blk) j)) L base
          (blk j).upper (collapseGenDecoration D hS κ).1) *
        ∏ s, ThetaStem D hS layer hLayer J rad (cosetDecoration (D.garden hS) L base κ.1) s := by
  refine (stemFiltG_eq_prod _ J rad _).trans ?_
  have hG : ∀ z : GNode (D.forest hS), ¬ OnStemAddr (layeredReconstruction D hS layer hLayer) J z.1 →
      brExt (stemBW (layeredReconstruction D hS layer hLayer) J rad
        (cosetDecoration (D.garden hS) L base κ.1)) z = 1 := by
    intro z hz
    unfold brExt
    split_ifs with hb
    · unfold stemBW
      rw [if_neg]
      rintro ⟨j, hj⟩
      exact hz (onStemAddr_of_mem_stemSetCap hj)
    · rfl
  refine (stem_split D hS Φ hd hR _ hG).trans ?_
  congr 1
  congr 1
  · refine Finset.prod_congr rfl fun c hc => ?_
    have hc' : c ∉ Φ.hinges hd := (Finset.mem_filter.mp hc).2
    refine (brExt_toNode _ (coreLG D hS layer hLayer (Φ.br c))).trans ?_
    have hω : omegaNode (layeredReconstruction D hS layer hLayer).garden (cosetDecoration (D.garden hS) L base κ.1)
        (coreLG D hS layer hLayer (Φ.br c)) =
        omegaNode S (cosetDecoration S L base (collapseGenDecoration D hS κ).1) (Φ.br c) :=
      omegaNode_core_collapse D hS κ L base (Φ.br c)
    unfold stemBW filtStem
    by_cases hst : StemB D hS layer hLayer J (coreLG D hS layer hLayer (Φ.br c))
    · have hst' := hst
      unfold StemB at hst'
      rw [if_pos hst', if_pos ⟨hc', hst⟩, filtW_filtOfRad, hω]
    · have hst' := hst
      unfold StemB at hst'
      rw [if_neg hst', if_neg (fun h => hst h.2)]
      rfl
  · refine Finset.prod_congr rfl fun j _ => ?_
    refine (brExt_toNode _ (coreLG D hS layer hLayer (blk j).upper)).trans ?_
    have hω : omegaNode (layeredReconstruction D hS layer hLayer).garden (cosetDecoration (D.garden hS) L base κ.1)
        (coreLG D hS layer hLayer (blk j).upper) =
        omegaNode (D.garden hS) (cosetDecoration (D.garden hS) L base κ.1) (D.coreBranch hS (blk j).upper) := rfl
    rw [← radProd_core_eq_nodeWeight D hS κ L base, ← hω]
    unfold stemBW SUStem
    by_cases hst : StemB D hS layer hLayer J (coreLG D hS layer hLayer (blk j).upper)
    · have hst' := hst
      unfold StemB at hst'
      rw [if_pos hst', if_pos hst]
    · have hst' := hst
      unfold StemB at hst'
      rw [if_neg hst', if_neg hst]
      rfl

end Data

end WaveTurbulence.Flower.MkSlotsT
