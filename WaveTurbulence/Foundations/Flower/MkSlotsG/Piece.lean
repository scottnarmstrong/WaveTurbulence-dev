/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlots.Data
public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelSpec
public import WaveTurbulence.Foundations.Flower.MkSlotsT.Piece
public import WaveTurbulence.Foundations.Flower.MkSlotsT.Rep
public import WaveTurbulence.Foundations.Vine.Align.Export

/-! # B3s-HELPER6 G1: the general class piece `pieceGen` and the analytic core `ClassRepGen`

At a prescribed point `a` (the representative `repPt π` of a fine′ class), for cap trees `J`, patterns `pat`, times
`t s`, depth selections `kSel`, capped-stem scales `σ`, selection scales `Rs`, a fine marking `mkF` and a dagger
datum `dag`, the piece of B4's hypothesis `MarkedClassRepresentsMK` (W:Stage1MKGate/Hyp.lean) is fixed here:

* `selRGen` (δ's `MkSlotsS.selROf`): the residual selected atoms (atoms of `G_sb` whose core branch is a selected
  vertex; not hinges, unpinned for plain patterns, at most one per tree);
* `radRaw LG …` (at every branch `b` of a layered garden): the radii of the stem filters of the class weight at `b` —
  σ's dyadic radius `2^{σ j} L` (`MkSlotsT.radSigma`) and the selection shell `Rs j` when `b` is not the selected
  vertex of its tree (`selWeightCap` puts `chi0(|Ω_b|/Rs j)` on `stemSetCap … j` minus the selected vertex); at most two
  radii (`radRaw_length_le`); `radGen = radRaw` clamped at `1` (equal to `radRaw` for `1 ≤ L ≤ Rs`, `radGen_eq_raw`);
* `filtGen c`: `(Rs j, chiDN)` at a residual selected atom `c` (forced by `ClassPieceOK.sel_spec`), else γ's atom
  filter `MkSlotsT.filtStem` at the representative's reconstruction data (`a.prime.data`, its source layering,
  main's splice shape `MkSlotsT.shapeRep`) with the radii `radGen` (no filter at hinges, nor off the capped stems);
* `indGen k`: the dagger sibling indicator (`sibIndOf … (flwGen …)`, as α's `flwOf`) times σ's filter at the residual
  selected
atoms, `∏_{v ∈ selRGen} radProd (radSigma L σ v) (Ω_v k)` (that filter cannot sit in `filt v`, which `sel_spec`
  forces to be `(Rs, chiDN)`); `[0,1]`-valued (`indGen_mem`), reading only the momenta at protected atoms and their
  children (`indGen_local`: residual selected atoms are protected);
* `lbGen c` (ruling R187, finding F-H3-1): `some s` at a free atom `c` of a `dParent` tree whose core branch is the
  garden parent of a pinned branch `u` that is the core branch of no atom (a pinned object top inside a slot), `none`
  elsewhere (in particular `none` for every non-`dParent` tree: `lbGen_not_dParent`, `lbGen_plain`);
* **`pieceGen`** `:= classPiece P mkF a (protOf …) |Π(a)| (fixOf J pat t s mkF a) filtGen indGen lbGen`; for
  `pat ≡ plain`, `σ ≡ none`, `kSel ≡ none` it is α's `pieceα` (`Alpha.lean`, `pieceGen_alpha`);
* **`ClassRepGen cP P`**: the binders of `MarkedClassRepresentsMK` (with `J.card = R` and the non-zero class
  hypothesis) ⟹ `RepresentsIntMKSel` of the class value by `pieceGen (repPt π)` with the residual selected atoms
  `selRGen (repPt π)` at the mass `selMassMK`, and `RepresentsIntMK` at `cP + 343` and mass `b ^ N`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)
open WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.Flower.MkSlots (stA coreOf protOf fixOf sibIndOf sibIndOf_mem)

namespace WaveTurbulence.Flower.MkSlotsG

variable {w : ℕ}

/-! ## The residual selected atoms and the reconstruction of the representative -/

/-- **The residual selected atoms** of the piece of `a` (δ's `selROf`). -/
abbrev selRGen (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) : Finset (GBranch (stA mkF a).G.tree) :=
  MkSlotsS.selROf J kSel mkF a

/-- The reconstruction of `a` at its source layering (it is `a.layered`, `VineAlign.sourceLayer_reconstructs`;
definitionally B3s's `MkSlots.recLG`). -/
abbrev recA (a : PrescribedPrimeGarden w) : LayeredGarden w :=
  RegRed.layeredReconstruction a.prime.data a.prime.prime.1 (VineAlign.sourceLayer a)
    (VineAlign.sourceLayer_isLayering a)

theorem recA_eq (a : PrescribedPrimeGarden w) : recA a = a.layered := VineAlign.sourceLayer_reconstructs a

/-! ## The radii of the stem filters -/

/-- The selection shell at `b`: `[Rs j]` if `b` is a stem node other than the selected vertex `v_j` of its tree
(`selWeightCap` carries `chi0(|Ω_b| / Rs j)` on `stemSetCap LG J j \ {v_j}`), else `[]`. -/
def shellRad (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (b : GBranch LG.garden.tree) : List ℝ :=
  if ∃ v, selCap LG J kSel b.1.1 = some v ∧ v ≠ b then [Rs b.1.1] else []

/-- **The radii of the class weight's stem filters at `b`**: σ's `2^{σ j} L`, then the selection shell `Rs j`. -/
def radRaw (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (b : GBranch LG.garden.tree) : List ℝ :=
  MkSlotsT.radSigma L σ b ++ shellRad LG J kSel Rs b

/-- The radii clamped at `1` (so that γ's atom filters are defined unconditionally). -/
def radGen (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (b : GBranch LG.garden.tree) : List ℝ :=
  (radRaw LG J L σ kSel Rs b).map (max 1)

theorem one_le_radGen (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (b : GBranch LG.garden.tree) : ∀ x ∈ radGen LG J L σ kSel Rs b, 1 ≤ x := by
  intro x hx
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
  exact le_max_left _ _

theorem radSigma_length_le (L : ℝ) (σ : Fin w → Option ℕ) {T : Fin w → TTree} (b : GBranch T) :
    (MkSlotsT.radSigma L σ b).length ≤ 1 := by
  unfold MkSlotsT.radSigma
  cases σ b.1.1 <;> simp

theorem shellRad_length_le (LG : LayeredGarden w) (J : Finset (Fin w)) (kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (b : GBranch LG.garden.tree) : (shellRad LG J kSel Rs b).length ≤ 1 := by
  unfold shellRad
  split_ifs <;> simp

/-- At most two radii (two layers) per node. -/
theorem radRaw_length_le (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (b : GBranch LG.garden.tree) : (radRaw LG J L σ kSel Rs b).length ≤ 2 := by
  unfold radRaw
  rw [List.length_append]
  have h1 := radSigma_length_le L σ b
  have h2 := shellRad_length_le LG J kSel Rs b
  omega

theorem radGen_length_le (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ)
    (Rs : Fin w → ℝ) (b : GBranch LG.garden.tree) : (radGen LG J L σ kSel Rs b).length ≤ 2 := by
  unfold radGen
  rw [List.length_map]
  exact radRaw_length_le LG J L σ kSel Rs b

/-- For `1 ≤ L` and `1 ≤ Rs`, every raw radius is at least `1`. -/
theorem one_le_radRaw {LG : LayeredGarden w} {J : Finset (Fin w)} {L : ℝ} {σ kSel : Fin w → Option ℕ}
    {Rs : Fin w → ℝ} (hL : 1 ≤ L) (hRs : ∀ j, 1 ≤ Rs j) (b : GBranch LG.garden.tree) :
    ∀ x ∈ radRaw LG J L σ kSel Rs b, 1 ≤ x := by
  intro x hx
  unfold radRaw at hx
  rcases List.mem_append.1 hx with h | h
  · unfold MkSlotsT.radSigma at h
    rcases hσ : σ b.1.1 with _ | i
    · rw [hσ] at h; simp at h
    · rw [hσ] at h
      simp only [Option.elim, List.mem_singleton] at h
      subst h
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hL
  · unfold shellRad at h
    split_ifs at h
    · rw [List.mem_singleton] at h; subst h; exact hRs _
    · simp at h

/-- **The clamp is inactive** for `1 ≤ L` and `1 ≤ Rs`. -/
theorem radGen_eq_raw {LG : LayeredGarden w} {J : Finset (Fin w)} {L : ℝ} {σ kSel : Fin w → Option ℕ}
    {Rs : Fin w → ℝ} (hL : 1 ≤ L) (hRs : ∀ j, 1 ≤ Rs j) :
    radGen LG J L σ kSel Rs = radRaw LG J L σ kSel Rs := by
  funext b
  unfold radGen
  conv_rhs => rw [← List.map_id (radRaw LG J L σ kSel Rs b)]
  exact List.map_congr_left fun x hx => max_eq_right (one_le_radRaw hL hRs b x hx)

/-! ## The flower children and the lower bounds -/

/-- The flower children of a `G_sb` branch: leaves paired with a cap root (α's `MkSlots.flwOf`, same body). -/
def flwGen (J : Finset (Fin w)) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    GBranch (stA mkF a).G.tree → Fin 3 → Prop :=
  fun c i => ∃ ℓ : GLeaf (stA mkF a).G.tree, ℓ.toNode = c.child i ∧ ((stA mkF a).G.pair ℓ).1.1 ∈ J

/-- The pinned object tops below an atom `c`: pinned branches `u` of `a.layered` that are children of the core branch
of `c` and the core branch of no atom of `G_sb` (they lie inside a slot). -/
def PinTopBelow (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) (c : GBranch (stA mkF a).G.tree) (u : GBranch a.layered.garden.tree) : Prop :=
  (fixCap a.layered J pat t s u).isSome ∧ u.IsChildOf (coreOf mkF a c) ∧ ∀ c' : GBranch (stA mkF a).G.tree,
    coreOf mkF a c' ≠ u

/-- **The constant lower bounds of the piece** (ruling R187): `lb c = some s` at a free atom `c` of a `dParent` tree
with a pinned object top below it (F-H3-1: the frozen kernel keeps `s < τ_c`), `none` elsewhere. -/
def lbGen (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) (c : GBranch (stA mkF a).G.tree) : Option ℝ :=
  if pat c.1.1 = FixPat.dParent ∧ fixOf J pat t s mkF a c = none ∧ ∃ u, PinTopBelow J pat t s mkF a c u
  then some s else none

theorem lbGen_spec {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ} {mkF : Stage1Mk.MarkFn w}
    {a : PrescribedPrimeGarden w} {c : GBranch (stA mkF a).G.tree} {x : ℝ} (h : lbGen J pat t s mkF a c = some x) :
    x = s ∧ pat c.1.1 = FixPat.dParent ∧ fixOf J pat t s mkF a c = none ∧ ∃ u, PinTopBelow J pat t s mkF a c u := by
  unfold lbGen at h
  split_ifs at h with hc
  · exact ⟨(Option.some.inj h).symm, hc⟩

theorem lbGen_isSome {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ} {mkF : Stage1Mk.MarkFn w}
    {a : PrescribedPrimeGarden w} {c : GBranch (stA mkF a).G.tree} (h : (lbGen J pat t s mkF a c).isSome) :
    pat c.1.1 = FixPat.dParent ∧ fixOf J pat t s mkF a c = none ∧ ∃ u, PinTopBelow J pat t s mkF a c u := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h
  exact (lbGen_spec hx).2

/-- No lower bound outside the `dParent` trees. -/
theorem lbGen_not_dParent {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ} {mkF : Stage1Mk.MarkFn w}
    {a : PrescribedPrimeGarden w} {c : GBranch (stA mkF a).G.tree} (h : pat c.1.1 ≠ FixPat.dParent) :
    lbGen J pat t s mkF a c = none := by
  unfold lbGen
  exact ite_eq_right_of_eq_false _ _ (eq_false fun hc => h hc.1)

/-- **No lower bound for plain patterns** (α). -/
theorem lbGen_plain (J : Finset (Fin w)) (t s : ℝ) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    lbGen J (fun _ => FixPat.plain) t s mkF a = fun _ => none := by
  funext c
  exact lbGen_not_dParent (by simp)

/-! ## The filters and the indicator of the piece -/

/-- **The atom filters of the piece**: `(Rs j, chiDN)` at a residual selected atom, else γ's atom filter (radii
`radGen` at the representative's reconstruction). -/
def filtGen (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) (c : GBranch (stA mkF a).G.tree) : Option (ℝ × SchwartzMap ℝ ℂ) :=
  if c ∈ selRGen J kSel mkF a then some (Rs c.1.1, MkSlotsS.chiDNS)
  else MkSlotsT.filtStem a.prime.data a.prime.prime.1 (MkSlotsT.shapeRep mkF a) (MkSlotsT.unitsRep_disj mkF a)
    (VineAlign.sourceLayer a) (VineAlign.sourceLayer_isLayering a) J (radGen (recA a) J L σ kSel Rs)
    (one_le_radGen (recA a) J L σ kSel Rs) c

/-- **The indicator of the piece**: the dagger sibling indicator times σ's filter at the residual selected atoms. -/
def indGen {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) (dag : Option (Fin w → Fin 3 → Mom d)) (k : GNode (stA mkF a).G.tree → Mom d) :
    ℝ :=
  sibIndOf J mkF a dag (flwGen J mkF a) k *
    ∏ v ∈ selRGen J kSel mkF a, MkSlotsT.radProd (MkSlotsT.radSigma L σ v) (omegaNode (stA mkF a).G k v)

theorem filtGen_sel {J : Finset (Fin w)} {L : ℝ} {σ kSel : Fin w → Option ℕ} {Rs : Fin w → ℝ}
    {mkF : Stage1Mk.MarkFn w} {a : PrescribedPrimeGarden w} {c : GBranch (stA mkF a).G.tree}
    (hc : c ∈ selRGen J kSel mkF a) : filtGen J L σ kSel Rs mkF a c = some (Rs c.1.1, MkSlotsS.chiDNS) := by
  unfold filtGen
  simp only [hc, ↓reduceIte]

theorem filtGen_not_sel {J : Finset (Fin w)} {L : ℝ} {σ kSel : Fin w → Option ℕ} {Rs : Fin w → ℝ}
    {mkF : Stage1Mk.MarkFn w} {a : PrescribedPrimeGarden w} {c : GBranch (stA mkF a).G.tree}
    (hc : c ∉ selRGen J kSel mkF a) :
    filtGen J L σ kSel Rs mkF a c =
      MkSlotsT.filtStem a.prime.data a.prime.prime.1 (MkSlotsT.shapeRep mkF a) (MkSlotsT.unitsRep_disj mkF a)
        (VineAlign.sourceLayer a) (VineAlign.sourceLayer_isLayering a) J (radGen (recA a) J L σ kSel Rs)
        (one_le_radGen (recA a) J L σ kSel Rs) c := by
  unfold filtGen
  simp only [hc, ↓reduceIte]

/-- The selected product of the indicator lies in `[0,1]`. -/
theorem selProd_mem {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) (k : GNode (stA mkF a).G.tree → Mom d) :
    0 ≤ ∏ v ∈ selRGen J kSel mkF a, MkSlotsT.radProd (MkSlotsT.radSigma L σ v) (omegaNode (stA mkF a).G k v) ∧
      ∏ v ∈ selRGen J kSel mkF a, MkSlotsT.radProd (MkSlotsT.radSigma L σ v) (omegaNode (stA mkF a).G k v) ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (MkSlotsT.radProd_mem_Icc _ _).1,
    Finset.prod_le_one₀ (fun _ _ => (MkSlotsT.radProd_mem_Icc _ _).1) fun _ _ => (MkSlotsT.radProd_mem_Icc _ _).2⟩

/-- **`ind_ok`**: the indicator of the piece takes values in `[0,1]`. -/
theorem indGen_mem {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) (dag : Option (Fin w → Fin 3 → Mom d)) (k : GNode (stA mkF a).G.tree → Mom d) :
    0 ≤ indGen J L σ kSel mkF a dag k ∧ indGen J L σ kSel mkF a dag k ≤ 1 := by
  have h1 := sibIndOf_mem J mkF a dag (flwGen J mkF a) k
  have h2 := selProd_mem J L σ kSel mkF a k
  refine ⟨mul_nonneg h1.1 h2.1, ?_⟩
  calc _ ≤ 1 * 1 := mul_le_mul h1.2 h2.2 h2.1 zero_le_one
    _ = 1 := one_mul 1

/-- `Ω_v` reads only the momenta at `v` and its children. -/
theorem omegaNode_congr {d : ℕ} {G : Garden w} {k k' : GNode G.tree → Mom d} {v : GBranch G.tree}
    (h : ∀ i : Fin 3, k (v.child i) = k' (v.child i) ∧ k v.toNode = k' v.toNode) :
    omegaNode G k v = omegaNode G k' v := by
  unfold omegaNode
  rw [(h 0).1, (h 1).1, (h 2).1, (h 0).2]

/-- **`ind_local`**: the indicator reads only the momenta at protected atoms and their children (the dagger
indicator at capped flower parents, σ's filter at residual selected atoms, both seeds of `Π`). -/
theorem indGen_local {d : ℕ} (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (L : ℝ)
    (σ kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w)
    (dag : Option (Fin w → Fin 3 → Mom d)) (k k' : GNode (stA mkF a).G.tree → Mom d)
    (h : ∀ c ∈ protOf J pat t s kSel mkF a, ∀ i : Fin 3, k (c.child i) = k' (c.child i) ∧ k c.toNode = k' c.toNode) :
    indGen J L σ kSel mkF a dag k = indGen J L σ kSel mkF a dag k' := by
  unfold indGen
  rw [MkSlots.sibIndOf_local J pat t s kSel mkF a dag (flwGen J mkF a) k k' fun c hc i => (h c hc i).1]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [omegaNode_congr (h v (MkSlotsS.selROf_sub_protOf pat t s hv))]

/-! ## The general piece -/

/-- **The general class piece** at a prescribed point `a`. -/
def pieceGen (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) : Stage1PieceMK P.d R :=
  classPiece P mkF a (protOf J pat t s kSel mkF a) (protI a.layered J pat t s kSel).card (fixOf J pat t s mkF a)
    (filtGen J P.L σ kSel Rs mkF a) (indGen J P.L σ kSel mkF a dag) (lbGen J pat t s mkF a)

theorem pieceGen_filt (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    (pieceGen P J pat t s kSel σ Rs mkF a dag).filt = filtGen J P.L σ kSel Rs mkF a := rfl

theorem pieceGen_ind (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    (pieceGen P J pat t s kSel σ Rs mkF a dag).ind = indGen J P.L σ kSel mkF a dag := rfl

theorem pieceGen_fix (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    (pieceGen P J pat t s kSel σ Rs mkF a dag).fix = fixOf J pat t s mkF a := rfl

theorem pieceGen_lb (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    (pieceGen P J pat t s kSel σ Rs mkF a dag).lb = lbGen J pat t s mkF a := rfl

theorem pieceGen_nProt (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) :
    (pieceGen P J pat t s kSel σ Rs mkF a dag).nProt = (protI a.layered J pat t s kSel).card := rfl

/-! ## The α case -/

/-- Without depth selections there is no residual selected atom. -/
theorem selRGen_none (J : Finset (Fin w)) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    selRGen J (fun _ => none) mkF a = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun c hc => ?_
  obtain ⟨j, hj⟩ := (Finset.mem_filter.1 (MkSlotsS.mem_selROf.1 hc)).2
  simp [selCap] at hj

theorem filtOfRad_nil (rs : List ℝ) (hrs : ∀ x ∈ rs, 1 ≤ x) (h : rs = []) : MkSlotsT.filtOfRad rs hrs = none := by
  subst h
  rfl

/-- Without σ and selections there are no radii. -/
theorem radGen_none (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (Rs : Fin w → ℝ)
    (b : GBranch LG.garden.tree) : radGen LG J L (fun _ => none) (fun _ => none) Rs b = [] := by
  simp [radGen, radRaw, MkSlotsT.radSigma, shellRad, selCap]

/-- **α filters**: without σ and selections the piece has no filter. -/
theorem filtGen_alpha (J : Finset (Fin w)) (L : ℝ) (Rs : Fin w → ℝ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) : filtGen J L (fun _ => none) (fun _ => none) Rs mkF a = fun _ => none := by
  funext c
  rw [filtGen_not_sel (by rw [selRGen_none]; exact Finset.notMem_empty c)]
  unfold MkSlotsT.filtStem
  split_ifs
  · exact filtOfRad_nil _ _ (radGen_none _ J L Rs _)
  · rfl

/-- **α indicator**: without selections the indicator is the dagger sibling indicator. -/
theorem indGen_alpha {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) (dag : Option (Fin w → Fin 3 → Mom d)) :
    indGen J L σ (fun _ => none) mkF a dag = sibIndOf J mkF a dag (flwGen J mkF a) := by
  funext k
  unfold indGen
  rw [selRGen_none, Finset.prod_empty, mul_one]

/-! ## The analytic core -/

/-- **The analytic core of B3s** (`pieceGen` represents the class value). Binders: those of B4's
`MarkedClassRepresentsMK` (W:Stage1MKGate/Hyp.lean, sha256 `221164b2…` after ruling R187, binders unchanged since
`dd72bd04…`; with `J.card = R` and the non-zero class hypothesis), verbatim. Conclusion: `RepresentsIntMKSel` of the
class value by the general piece of the representative with its residual selected atoms at the mass `selMassMK`
(selected trees `= image of selRGen`), and `RepresentsIntMK` at `cP + 343` and mass `b ^ N`. -/
def ClassRepGen (cP : ℝ) (P : WTParams) : Prop :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ (J : Finset (Fin (2 * R))), J.card = R → ∀ (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ),
  ∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t,
  ∀ A : Finset (LayeredGarden (2 * R)),
    (∀ LG ∈ A, MkCarries P p N LG ∧ (∀ h : 2 * R = 2, ¬ IsRegularCouple (h ▸ LG.garden : Garden 2)) ∧
      LG.garden.Irreducible ∧ (∀ j ∈ J, LG.garden.tree j = TTree.leaf) ∧ CapGeo LG J p ∧ CapPatValid LG J pat p) →
    (∀ j, (kSel j).isSome → pat j = FixPat.plain) →
    MarkedTwistClosed p A (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) →
  ∀ (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (Rf : Fin (2 * R) → Option ℝ)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)),
    1 ≤ b → (∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b) →
    (∀ j r, Rf j = some r → P.L / 2 ≤ r) → (∀ j, P.L ≤ Rs j) →
    (((∃ i, σ i ≠ none) ∨ ∃ i, kSel i ≠ none) → ∀ j, j ∉ J → ∃ r, Rf j = some r ∧
      (∀ j' x, ‖x‖ ≥ r → h p j j' x = 0 ∧ h p j' j x = 0) ∧ r ^ 10 ≤ ‖latticePoint P.L (roots j)‖) →
  ∀ (mkF : Stage1Mk.MarkFn (2 * R)), FineMarking J pat t s kSel σ mkF →
  ∀ π : PcA R p (objKind (2 * R)) A mkF,
    (¬ StemDep σ kSel ∨ ∀ a : PrescribedPrimeGarden (2 * R),
      Related (p := p) (kind := objKind (2 * R)) (repPt π) a mkF → CleanPt J a) →
  RepresentsIntMKSel (pieceGen P J pat t s kSel σ Rs mkF (repPt π) dag) (selRGen J kSel mkF (repPt π)) N cP
      (fun _ => t) 0 roots (selMassMK N b Rs kSel ((selRGen J kSel mkF (repPt π)).image fun v => v.1.1))
      (classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π) ∧
    (pieceGen P J pat t s kSel σ Rs mkF (repPt π) dag).RepresentsIntMK N (cP + 343) (fun _ => t) 0 roots (b ^ N)
      (classValue P p J pat kSel t s A roots h Rf σ Rs dag mkF π)

end WaveTurbulence.Flower.MkSlotsG
