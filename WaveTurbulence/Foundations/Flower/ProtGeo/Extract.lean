/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtGeo.Geo
public import WaveTurbulence.Foundations.RegStruct.DecodedTree
public import WaveTurbulence.Foundations.RegStruct.DecodedCouple
public import WaveTurbulence.Foundations.RegStruct.PairNaturality
public import WaveTurbulence.Foundations.VineEst.CodeConjPairs

/-! # D2b PROT-GEO (2): protected objects as layered gardens, and item (i) `ProtShape`

* `objTree LG X ζ u hE`: an embedded paired tree as its own layered garden: main's decoded carrier
  `decodedTree X ζ` with the carrier's layers at the relocated addresses (`addrExt u`).
* `normChain ζ X`: the sign-normalized chain code (`X` for `ζ = 1`, the conjugate code for `ζ = -1`), with
  `(normChain ζ X).plug 1 h = X.plug ζ h` and the same lone path.
* `objCpl LG X ζ u c hE hc`: a cap couple as its own layered garden: `decodedCouple (type2 (normChain ζ X) nil triv)`
  (tree `0` the original subtree, tree `1` the cap), the carrier's layers.
* `embeds_stem_cap` (o73 Prop 3.1, couples): an embedded couple meeting a capped stem branching node is a cap couple
  `type2 X nil triv` (cap at the `-` root) or `type2 nil X triv` (cap at the `+` root).
* **(i)** `protShape_objTree`, `protShape_objCpl`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.Flower.MkDefs
  WaveTurbulence.Flower.ProtDefs

namespace WaveTurbulence.Flower.ProtGeo

variable {w : ℕ}

/-! ## Relocation of object addresses into the carrier -/

/-- Object addresses (any width) relocated below the carrier root `u`. -/
def reloc {v : ℕ} (u : Fin w × Path) (z : Fin v × Path) : Fin w × Path := addrExt u z.2

theorem reloc_compat {v : ℕ} (u : Fin w × Path) (a : Fin v × Path) (p : Path) :
    reloc u (addrExt a p) = addrExt (reloc u a) p := by
  simp [reloc, addrExt, List.append_assoc]

theorem reloc_root {v : ℕ} (u : Fin w × Path) (i : Fin v) : reloc u (i, ([] : Path)) = u := addrExt_nil' u

/-- Pairs of a chain code at an object root relocate to pairs at the carrier root. -/
theorem pairsAt_reloc (X : RegChain) (ζ : ℤˣ) (u : Fin w × Path) {v : ℕ} (i : Fin v)
    {q : (Fin v × Path) × (Fin v × Path)} (hq : q ∈ X.pairsAt ζ (i, [])) :
    (reloc u q.1, reloc u q.2) ∈ X.pairsAt ζ u := by
  have e := chain_pairsAt_map X (reloc u) (reloc_compat u) ζ (i, [])
  rw [reloc_root] at e
  rw [e]
  exact List.mem_map.mpr ⟨q, hq, rfl⟩

/-- Pair endpoints of a chain code rooted at `(i, [])` lie in tree `i`. -/
theorem pairsAt_root_fst (X : RegChain) (ζ : ℤˣ) {v : ℕ} (i : Fin v) {z : Fin v × Path}
    (hz : z ∈ pairEndpoints (X.pairsAt ζ (i, []))) : z.1 = i := by
  have h1 : z ∈ leafAddresses (X.plug ζ .leaf) (i, []) := by
    rw [chain_leafAddresses]; exact Finset.mem_union_left _ hz
  obtain ⟨q, -, rfl⟩ := mem_leafAddresses'.mp h1
  rfl

theorem mem_symmPairs {α : Type*} {P : List (α × α)} {x : α × α} :
    x ∈ symmPairs P ↔ x ∈ P ∨ (x.2, x.1) ∈ P := by
  unfold symmPairs
  rw [List.mem_append, List.mem_map]
  refine or_congr Iff.rfl ⟨fun ⟨y, hy, he⟩ => ?_, fun h => ⟨(x.2, x.1), h, rfl⟩⟩
  subst he; exact hy

/-- Layer of an address is at most `p` when all layers are. -/
theorem layerAt_le' {LG : LayeredGarden w} {p : ℕ} (hp : ∀ a, LG.layer a ≤ p) (z : Fin w × Path) :
    layerAt LG z ≤ p := by
  unfold layerAt
  split_ifs
  · exact hp _
  · exact Nat.zero_le _

/-- Children of a carrier branch at an object branching position: layers do not increase. -/
theorem layer_child_reloc {LG : LayeredGarden w} {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {h : TTree}
    (hE : ChainEmb LG.garden X ζ u h) {q : Path} (hq : q ∈ (X.plug ζ .leaf).branching) (i : Fin 3) :
    layerAt LG (addrExt u (q ++ [i])) ≤ layerAt LG (addrExt u q) := by
  let B := embBr hE q hq
  have e1 : addrExt u (q ++ [i]) = (B.child i).1 := by
    simp [B, embBr, GBranch.child, addrExt, List.append_assoc]
  have e2 : addrExt u q = B.toNode.1 := rfl
  rw [e1, e2, layerAt_of_mem LG (B.child i).2, layerAt_of_mem LG B.toNode.2]
  exact LG.isLayering.1 B i

/-! ## Paired trees -/

theorem objTree_isLayering {LG : LayeredGarden w} {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {h : TTree}
    (hE : ChainEmb LG.garden X ζ u h) :
    IsLayering (decodedTree X ζ) (fun a => layerAt LG (addrExt u a.1.2)) := by
  refine ⟨fun b i => layer_child_reloc hE (q := b.1.2) b.2 i, fun ℓ => ?_⟩
  obtain ⟨-, hmark, hpair⟩ := decodedTree_decodes X ζ
  by_cases hl : ℓ.1.2 = X.lonePath
  · have hm : (decodedTree X ζ).mark ℓ ≠ none := by rw [hmark ℓ, ite_eq_left hl]; simp
    rw [((decodedTree X ζ).pair_eq_iff ℓ).2 hm]
  · rcases mem_symmPairs.mp (hpair ℓ hl) with h1 | h1
    · exact emb_pair_layer hE (pairsAt_reloc X ζ u (0 : Fin 1) h1)
    · exact (emb_pair_layer hE (pairsAt_reloc X ζ u (0 : Fin 1) h1)).symm

/-- **An embedded paired tree as its own layered garden**: the decoded carrier `decodedTree X ζ` with the carrier's
layers (`layer a = layerAt LG (addrExt u a.1.2)`). -/
def objTree (LG : LayeredGarden w) (X : RegChain) (ζ : ℤˣ) (u : Fin w × Path) {h : TTree}
    (hE : ChainEmb LG.garden X ζ u h) : LayeredGarden 1 :=
  ⟨decodedTree X ζ, fun a => layerAt LG (addrExt u a.1.2), objTree_isLayering hE⟩

theorem objTree_layer (LG : LayeredGarden w) (X : RegChain) (ζ : ℤˣ) (u : Fin w × Path) {h : TTree}
    (hE : ChainEmb LG.garden X ζ u h) (a : GNode (objTree LG X ζ u hE).garden.tree) :
    (objTree LG X ζ u hE).layer a = layerAt LG (addrExt u a.1.2) := rfl

theorem objTree_tree (LG : LayeredGarden w) (X : RegChain) (ζ : ℤˣ) (u : Fin w × Path) {h : TTree}
    (hE : ChainEmb LG.garden X ζ u h) : (objTree LG X ζ u hE).garden.tree 0 = X.plug ζ .leaf := rfl

/-- **(i), paired trees (o73 Prop 3.1).** A stem chain, as its own layered garden, is `ProtShape p X`. -/
theorem protShape_objTree {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} (hG : CapGeo LG J p)
    {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {h : TTree} (hS : StemChain LG J X ζ u h) :
    ProtShape p X (objTree LG X ζ u hS.emb) := by
  refine ⟨hS.wf, decodedTree_decodes X ζ, fun a => layerAt_le' hG.layer_le _, ?_⟩
  intro b _ hb hne
  exact hS.chain_layer hG hb hne

/-! ## The sign-normalized chain code -/

/-- The sign-`1` code with the same plugged trees (`conjChain` for `ζ = -1`). -/
def normChain (ζ : ℤˣ) (X : RegChain) : RegChain := if ζ = 1 then X else ConjCoh.conjChain X

theorem normChain_plug (ζ : ℤˣ) (X : RegChain) (h : TTree) : (normChain ζ X).plug 1 h = X.plug ζ h := by
  rcases Int.units_eq_one_or ζ with rfl | rfl
  · simp [normChain]
  · have e := ConjCoh.plug_conjChain X (-1) h
    rw [neg_neg] at e
    simpa [normChain] using e

theorem normChain_lonePath (ζ : ℤˣ) (X : RegChain) : (normChain ζ X).lonePath = X.lonePath := by
  unfold normChain; split_ifs
  · rfl
  · exact ConjCoh.lonePath_conjChain X

theorem normChain_wf (ζ : ℤˣ) (X : RegChain) : (normChain ζ X).wf = X.wf := by
  unfold normChain; split_ifs
  · rfl
  · exact ConjCoh.wf_conjChain X

theorem normChain_size (ζ : ℤˣ) (X : RegChain) : (normChain ζ X).size = X.size := by
  unfold normChain; split_ifs
  · rfl
  · exact ConjCoh.size_conjChain X

theorem normChain_isNil (ζ : ℤˣ) (X : RegChain) : (normChain ζ X).isNil = X.isNil := by
  unfold normChain; split_ifs
  · rfl
  · exact ConjCoh.isNil_conjChain X

/-- Pairs of the normalized code are the pairs of `X` at sign `ζ`, possibly reoriented. -/
theorem normChain_pairs (ζ : ℤˣ) (X : RegChain) {v : ℕ} (i : Fin v)
    {q : (Fin v × Path) × (Fin v × Path)} (hq : q ∈ (normChain ζ X).pairsAt 1 (i, [])) :
    ∃ r ∈ X.pairsAt ζ (i, []), q = r ∨ q = (r.2, r.1) := by
  rcases Int.units_eq_one_or ζ with rfl | rfl
  · exact ⟨q, by simpa [normChain] using hq, Or.inl rfl⟩
  · have hφ : ConjCoh.AddrCompat (fun z : Fin v × Path => z) := fun _ _ => rfl
    have e := ConjCoh.mem_pairsAt_conjChain hφ X (-1) (i, []) q
    rw [neg_neg] at e
    have hq' : q ∈ (ConjCoh.conjChain X).pairsAt 1 (i, []) := by simpa [normChain] using hq
    obtain ⟨r, hr, rfl⟩ := e.mp hq'
    exact ⟨r, hr, Or.inr rfl⟩

/-- The code of a cap couple with chain `X` at sign `ζ`. -/
def capCode (ζ : ℤˣ) (X : RegChain) : RegCpl := .type2 (normChain ζ X) .nil .triv

theorem capCode_trees (ζ : ℤˣ) (X : RegChain) : (capCode ζ X).trees = (X.plug ζ .leaf, .leaf) := by
  simp only [capCode, RegCpl.trees, RegChain.plug, normChain_plug]

theorem capCode_pairsAt (ζ : ℤˣ) (X : RegChain) :
    (capCode ζ X).pairsAt ((0 : Fin 2), []) ((1 : Fin 2), []) =
      (normChain ζ X).pairsAt 1 ((0 : Fin 2), []) ++ [(((0 : Fin 2), X.lonePath), ((1 : Fin 2), []))] := by
  simp [capCode, RegCpl.pairsAt, RegChain.pairsAt, normChain_lonePath, addrExt, RegChain.lonePath]

/-! ## Cap couples -/

/-- The layer function of a cap couple: tree `0` reads the carrier below `u`, tree `1` (the cap) the cap root. -/
def cplLayer (LG : LayeredGarden w) (u : Fin w × Path) (c : Fin w) (a : Fin 2 × Path) : ℕ :=
  if a.1 = 0 then layerAt LG (addrExt u a.2) else layerAt LG (c, [])

theorem cplLayer_of_zero {LG : LayeredGarden w} {u : Fin w × Path} {c : Fin w} {a : Fin 2 × Path} (h : a.1 = 0) :
    cplLayer LG u c a = layerAt LG (addrExt u a.2) := ite_eq_left h

theorem cplLayer_one (LG : LayeredGarden w) (u : Fin w × Path) (c : Fin w) (q : Path) :
    cplLayer LG u c ((1 : Fin 2), q) = layerAt LG (c, []) := ite_eq_right (show ¬ ((1 : Fin 2) = 0) by decide)

theorem decodedCouple_capCode_tree (ζ : ℤˣ) (X : RegChain) :
    (decodedCouple (capCode ζ X)).tree = ![X.plug ζ .leaf, .leaf] := by
  show coupleForest (capCode ζ X) = _
  unfold coupleForest; rw [capCode_trees]

theorem capCode_branch {ζ : ℤˣ} {X : RegChain} (b : GBranch (decodedCouple (capCode ζ X)).tree) :
    b.1.1 = 0 ∧ b.1.2 ∈ (X.plug ζ .leaf).branching := by
  have hb : b.1.2 ∈ (![X.plug ζ .leaf, TTree.leaf] b.1.1).branching :=
    (congrArg (fun T : Fin 2 → TTree => b.1.2 ∈ (T b.1.1).branching) (decodedCouple_capCode_tree ζ X)).mp b.2
  by_cases h0 : b.1.1 = 0
  · rw [h0] at hb; exact ⟨h0, by simpa using hb⟩
  · have h1 : b.1.1 = 1 := by have := b.1.1.2; omega
    rw [h1] at hb; simp [TTree.branching] at hb

theorem objCpl_isLayering {LG : LayeredGarden w} {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {c : Fin w}
    (hE : ChainEmb LG.garden X ζ u .leaf)
    (hc : ∀ ℓ : GLeaf LG.garden.tree, ℓ.1 = addrExt u X.lonePath → (LG.garden.pair ℓ).1 = (c, [])) :
    IsLayering (decodedCouple (capCode ζ X)) (fun a => cplLayer LG u c a.1) := by
  refine ⟨fun b i => ?_, fun ℓ => ?_⟩
  · obtain ⟨h0, hb⟩ := capCode_branch b
    show cplLayer LG u c (b.child i).1 ≤ cplLayer LG u c b.1
    rw [cplLayer_of_zero (a := (b.child i).1) h0, cplLayer_of_zero h0]
    exact layer_child_reloc hE hb i
  · obtain ⟨-, -, -, hpair⟩ := decodedCouple_decodes (capCode ζ X)
    have hm := hpair ℓ
    change _ ∈ symmPairs ((capCode ζ X).pairsAt ((0 : Fin 2), []) ((1 : Fin 2), [])) at hm
    rw [capCode_pairsAt] at hm
    -- the lone pair: port and cap root have equal layers in the carrier
    have hlone : layerAt LG (addrExt u X.lonePath) = layerAt LG (c, []) := by
      have hl : (addrExt u X.lonePath).2 ∈ (LG.garden.tree (addrExt u X.lonePath).1).leaves :=
        (node_iff_of_subtree hE.node hE.tree X.lonePath).2.1.2 (chain_lone_mem_leaves X ζ)
      let ℓp : GLeaf LG.garden.tree := ⟨_, hl⟩
      have hp := hc ℓp rfl
      have n2 : ([] : Path) ∈ (LG.garden.tree c).nodes := by
        have h2 := (LG.garden.pair ℓp).2
        rw [hp] at h2
        exact TTree.leaves_subset_nodes _ h2
      rw [layerAt_of_mem LG (TTree.leaves_subset_nodes _ hl), layerAt_of_mem (z := (c, [])) LG n2]
      have e2 : (⟨(c, []), n2⟩ : GNode LG.garden.tree) = GLeaf.toNode (LG.garden.pair ℓp) :=
        Subtype.ext hp.symm
      rw [e2]; exact LG.isLayering.2 ℓp
    -- a pair of the chain: both ends in tree `0`, relocated pair of the carrier
    have hchain : ∀ x y : Fin 2 × Path, (x, y) ∈ (normChain ζ X).pairsAt 1 ((0 : Fin 2), []) →
        cplLayer LG u c x = cplLayer LG u c y := by
      intro x y hxy
      obtain ⟨r, hr, hre | hre⟩ := normChain_pairs ζ X (0 : Fin 2) hxy
      · subst hre
        have e1 : x.1 = 0 := pairsAt_root_fst X ζ (0 : Fin 2) ((mem_pairEndpoints_iff _ _).2 ⟨_, hr, Or.inl rfl⟩)
        have e2 : y.1 = 0 := pairsAt_root_fst X ζ (0 : Fin 2) ((mem_pairEndpoints_iff _ _).2 ⟨_, hr, Or.inr rfl⟩)
        rw [cplLayer_of_zero e1, cplLayer_of_zero e2]
        exact emb_pair_layer hE (pairsAt_reloc X ζ u (0 : Fin 2) hr)
      · rw [Prod.mk.injEq] at hre
        obtain ⟨rfl, rfl⟩ := hre
        have e1 : r.1.1 = 0 := pairsAt_root_fst X ζ (0 : Fin 2) ((mem_pairEndpoints_iff _ _).2 ⟨_, hr, Or.inl rfl⟩)
        have e2 : r.2.1 = 0 := pairsAt_root_fst X ζ (0 : Fin 2) ((mem_pairEndpoints_iff _ _).2 ⟨_, hr, Or.inr rfl⟩)
        rw [cplLayer_of_zero e1, cplLayer_of_zero e2]
        exact (emb_pair_layer hE (pairsAt_reloc X ζ u (0 : Fin 2) hr)).symm
    suffices key : ∀ x y : Fin 2 × Path, (x, y) ∈ symmPairs ((normChain ζ X).pairsAt 1 ((0 : Fin 2), []) ++
        [(((0 : Fin 2), X.lonePath), ((1 : Fin 2), []))]) → cplLayer LG u c x = cplLayer LG u c y from key _ _ hm
    intro x y hxy
    rcases mem_symmPairs.mp hxy with h1 | h1 <;> rcases List.mem_append.mp h1 with h2 | h2
    · exact hchain x y h2
    · rw [List.mem_singleton, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rw [cplLayer_of_zero (a := ((0 : Fin 2), X.lonePath)) rfl, cplLayer_one]; exact hlone
    · exact (hchain y x h2).symm
    · rw [List.mem_singleton, Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      rw [cplLayer_one, cplLayer_of_zero (a := ((0 : Fin 2), X.lonePath)) rfl]; exact hlone.symm

/-- **A cap couple as its own layered garden**: `decodedCouple (type2 (normChain ζ X) nil triv)` (tree `0` the
original subtree `X.plug ζ .leaf`, tree `1` the cap), with the carrier's layers. -/
def objCpl (LG : LayeredGarden w) (X : RegChain) (ζ : ℤˣ) (u : Fin w × Path) (c : Fin w)
    (hE : ChainEmb LG.garden X ζ u .leaf)
    (hc : ∀ ℓ : GLeaf LG.garden.tree, ℓ.1 = addrExt u X.lonePath → (LG.garden.pair ℓ).1 = (c, [])) :
    LayeredGarden 2 :=
  ⟨decodedCouple (capCode ζ X), fun a => cplLayer LG u c a.1, objCpl_isLayering hE hc⟩

theorem objCpl_tree (LG : LayeredGarden w) (X : RegChain) (ζ : ℤˣ) (u : Fin w × Path) (c : Fin w)
    (hE : ChainEmb LG.garden X ζ u .leaf)
    (hc : ∀ ℓ : GLeaf LG.garden.tree, ℓ.1 = addrExt u X.lonePath → (LG.garden.pair ℓ).1 = (c, [])) :
    (objCpl LG X ζ u c hE hc).garden.tree = ![X.plug ζ .leaf, .leaf] :=
  decodedCouple_capCode_tree ζ X

theorem isNil_eq_false {X : RegChain} (h : X ≠ .nil) : X.isNil = false := by
  cases X with
  | nil => exact absurd rfl h
  | pair => rfl

/-- A stem chain's code is not `nil`. -/
theorem StemChain.ne_nil {LG : LayeredGarden w} {J : Finset (Fin w)} {X : RegChain} {ζ : ℤˣ}
    {u : Fin w × Path} {h : TTree} (hS : StemChain LG J X ζ u h) : X ≠ .nil := by
  obtain ⟨v, hv, -⟩ := hS.meets
  obtain ⟨q, hq, -⟩ := mem_branchAddresses'.mp hv
  intro hX; subst hX
  simp [RegChain.plug, TTree.branching] at hq

/-- **(i), cap couples (o73 Prop 3.1).** A cap chain, as its own couple, is `ProtShape p (normChain ζ X)`. -/
theorem protShape_objCpl {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} (hG : CapGeo LG J p)
    {X : RegChain} {ζ : ℤˣ} {u : Fin w × Path} {c : Fin w} (hC : CapChain LG J X ζ u c) :
    ProtShape p (normChain ζ X) (objCpl LG X ζ u c hC.stem.emb hC.pair) := by
  have hnil : (normChain ζ X).isNil = false := by
    rw [normChain_isNil]; exact isNil_eq_false hC.stem.ne_nil
  refine ⟨?_, decodedCouple_decodes (capCode ζ X), ?_, fun a => ?_, ?_⟩
  · show (RegCpl.type2 (normChain ζ X) .nil .triv).wf = true
    simp only [RegCpl.wf, normChain_wf, hC.stem.wf, hnil]
    rfl
  · rw [objCpl_tree]; rfl
  · show cplLayer LG u c a.1 ≤ p
    unfold cplLayer; split_ifs <;> exact layerAt_le' hG.layer_le _
  · intro b hb0 hb hne
    rw [normChain_lonePath] at hb hne
    show cplLayer LG u c b.1 = p
    rw [cplLayer_of_zero (Fin.ext hb0)]
    exact hC.stem.chain_layer hG hb hne

end WaveTurbulence.Flower.ProtGeo
