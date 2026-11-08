/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsT.Rep
public import WaveTurbulence.Foundations.Flower.V5W2L.Defs
public import WaveTurbulence.Foundations.VineEst.VineSpaceK.StatementDefs
public import WaveTurbulence.Foundations.WaveB.Bridges

/-! # B3s-HELPER5 (γ) T4: a generic stem-filter weight in the chain's interface

**The generic stem filter family.** `stemFiltG LG J rad k = ∏_j ∏_{b ∈ stemSetCap LG J j} ∏_{r ∈ rad b} χ₀(|Ω_b| / r)`
with an arbitrary list of radii per stem node (`rad b = []`: no filter; two entries: two layers). Instances:
* σ's capped stem filters: `rad = radSigma L σ` (`[2^i L]` on tree `j` when `σ j = some i`), `stemFilterCap_eq`;
* δ's selection shells: `rad b = [Rs j]` off the selected vertex (δ's choice);
* both at once: the concatenation of the two lists (`stemFiltG_append`).

**The partition** (`stemFiltG_split`, on the reconstruction `LG` of a skeleton `S` with a splice shape
`Φ : SpliceShape blk Gsb` and the retention `StemRet`, T1): the product of the node weights over all nodes is
* the ATOM part `∏_{c ∉ hinges} w(core(Φ.br c))` (kind (a)),
* times the TOP part `∏_j w(core((blk j).upper))` (kind (b)),
* times the SLOT part `∏_s slotFac w s` (kind (c)): the product over the non-core native nodes of the slot `s`;
  only retained slots carry stem nodes (`slotFac_eq_one_of_not_slotRet`).

**The interface identities.**
* `omegaNode_core_collapse`: the resonance factor at the core of `β` on a decoration `κ` of the reconstruction is the
  skeleton resonance factor at `β` on the collapsed decoration `collapseGenDecoration D hS κ`; hence the top part is
  B3-2's unit top filter `nodeWeight (topFilterWeightL (SU j)) L base (blk j).upper (collapse κ)`
  (`stemNodeW_core_eq_nodeWeight`), and the atom part is a function of the collapsed decoration;
* `omegaNode_shape`: at a non-hinge `G_sb` atom `c`, the `G_sb` resonance factor on a `G_sb` momentum assignment `kG`
  is the skeleton resonance factor at `Φ.br c` on any skeleton assignment agreeing with `kG` through `Φ.node`;
* `slotFac_congr`: the slot part only reads the native nodes of the slot. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.VineB (SpliceShape Ret Disj)
open WaveTurbulence.RedSplice (CLBlock)
open WaveTurbulence.Flower.MkSlots (slotOf)

namespace WaveTurbulence.Flower.MkSlotsT

variable {w d : ℕ}

/-! ## The generic stem filter family -/

/-- The filters of one node: `∏_{r ∈ rs} χ₀(|x| / r)`. -/
def radProd (rs : List ℝ) (x : ℝ) : ℝ := (rs.map fun r => chi0 (|x| / r)).prod

theorem radProd_nil (x : ℝ) : radProd [] x = 1 := rfl

theorem radProd_append (rs rs' : List ℝ) (x : ℝ) : radProd (rs ++ rs') x = radProd rs x * radProd rs' x := by
  simp [radProd, List.map_append, List.prod_append]

theorem radProd_mem_Icc (rs : List ℝ) (x : ℝ) : 0 ≤ radProd rs x ∧ radProd rs x ≤ 1 := by
  unfold radProd
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons]
    have h0 : 0 ≤ chi0 (|x| / r) := by rw [WaveBBridges.chi0_eq_fourier_chi0]; exact Fourier.chi0_nonneg _
    have h1 : chi0 (|x| / r) ≤ 1 := by rw [WaveBBridges.chi0_eq_fourier_chi0]; exact Fourier.chi0_le_one _
    exact ⟨mul_nonneg h0 ih.1, mul_le_one₀ h1 ih.1 ih.2⟩

/-- **The generic stem filter weight** (radii `rad b` at the stem node `b`). -/
def stemFiltG (LG : LayeredGarden w) (J : Finset (Fin w)) (rad : GBranch LG.garden.tree → List ℝ)
    (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, ∏ b ∈ stemSetCap LG J j, radProd (rad b) (omegaNode LG.garden k b)

/-- Two families at once (two layers per node). -/
theorem stemFiltG_append (LG : LayeredGarden w) (J : Finset (Fin w)) (rad rad' : GBranch LG.garden.tree → List ℝ)
    (k : GNode LG.garden.tree → Mom d) :
    stemFiltG LG J (fun b => rad b ++ rad' b) k = stemFiltG LG J rad k * stemFiltG LG J rad' k := by
  unfold stemFiltG
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun b _ => radProd_append _ _ _

/-- σ's radii: `2^i L` on tree `j` when `σ j = some i`. -/
def radSigma (L : ℝ) (σ : Fin w → Option ℕ) {T : Fin w → TTree} (b : GBranch T) : List ℝ :=
  (σ b.1.1).elim [] fun i => [2 ^ i * L]

/-- **σ's capped stem filters are an instance** of the generic family. -/
theorem stemFilterCap_eq (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ) (σ : Fin w → Option ℕ)
    (k : GNode LG.garden.tree → Mom d) :
    stemFilterCap LG J L σ k = stemFiltG LG J (radSigma L σ) k := by
  unfold stemFilterCap stemFiltG
  refine Finset.prod_congr rfl fun j _ => ?_
  rcases hσ : σ j with _ | i
  · simp only [Option.elim]
    symm
    refine Finset.prod_eq_one fun b hb => ?_
    have hbj : b.1.1 = j := (Finset.mem_filter.mp hb).2.1
    simp [radSigma, hbj, hσ, radProd]
  · simp only [Option.elim, prodDyadicCut, if_true]
    refine Finset.prod_congr rfl fun b hb => ?_
    have hbj : b.1.1 = j := (Finset.mem_filter.mp hb).2.1
    simp [radSigma, hbj, hσ, radProd]

/-! ## Branch products as node products -/

section Nodes
variable {T : Fin w → TTree}

/-- A branch weight extended by `1` to the leaves. -/
def brExt (g : GBranch T → ℂ) (z : GNode T) : ℂ :=
  if h : z.1.2 ∈ (T z.1.1).branching then g ⟨z.1, h⟩ else 1

theorem brExt_toNode (g : GBranch T → ℂ) (b : GBranch T) : brExt g b.toNode = g b := by
  show (if h : b.1.2 ∈ (T b.1.1).branching then g ⟨b.1, h⟩ else 1) = g b
  rw [dif_pos b.2]
  rfl

theorem prod_brExt (g : GBranch T → ℂ) : ∏ z, brExt g z = ∏ b, g b := by
  have h1 : ∏ z, brExt g z = ∏ z ∈ univ.filter (fun z : GNode T => z.1.2 ∈ (T z.1.1).branching), brExt g z := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun z _ => ?_
    unfold brExt
    split_ifs <;> rfl
  have h2 : univ.filter (fun z : GNode T => z.1.2 ∈ (T z.1.1).branching) =
      Finset.univ.image (fun b : GBranch T => b.toNode) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨⟨z.1, h⟩, rfl⟩
    · rintro ⟨b, -, rfl⟩; exact b.2
  rw [h1, h2, Finset.prod_image (fun b _ b' _ h => Mole.branch_toNode_injective h)]
  exact Finset.prod_congr rfl fun b _ => brExt_toNode g b

end Nodes

/-- The node weight of the generic stem filters (on stem branches; `1` elsewhere). -/
def stemBW (LG : LayeredGarden w) (J : Finset (Fin w)) (rad : GBranch LG.garden.tree → List ℝ)
    (k : GNode LG.garden.tree → Mom d) (b : GBranch LG.garden.tree) : ℂ :=
  if ∃ j, b ∈ stemSetCap LG J j then (radProd (rad b) (omegaNode LG.garden k b) : ℂ) else 1

/-- The generic stem filter weight is the product of its node weights over all nodes. -/
theorem stemFiltG_eq_prod (LG : LayeredGarden w) (J : Finset (Fin w)) (rad : GBranch LG.garden.tree → List ℝ)
    (k : GNode LG.garden.tree → Mom d) :
    (stemFiltG LG J rad k : ℂ) = ∏ z, brExt (stemBW LG J rad k) z := by
  rw [prod_brExt]
  unfold stemFiltG stemBW
  push_cast
  have hdisj : ((univ : Finset (Fin w)) : Set (Fin w)).PairwiseDisjoint (fun j => stemSetCap LG J j) := by
    intro j _ j' _ hne
    refine Finset.disjoint_left.mpr fun b hb hb' => hne ?_
    exact (Finset.mem_filter.mp hb).2.1.symm.trans (Finset.mem_filter.mp hb').2.1
  rw [← Finset.prod_biUnion hdisj]
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun b _ => rfl
  ext b
  simp

/-! ## The partition over the three kinds -/

section Split
variable {S Gsb : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) {ι : Type} [Fintype ι] [DecidableEq ι]
  {blk : ι → CLBlock S} (Φ : SpliceShape blk Gsb)

/-- A node of the reconstruction is a core node. -/
def IsCore (z : GNode (D.forest hS)) : Prop := ∃ β : GBranch S.tree, z = (D.coreBranch hS β).toNode

/-- **The slot factor** of a node weight `G`: the product over the non-core native nodes of the slot `s`. -/
def slotFac (G : GNode (D.forest hS) → ℂ) (s : ReplacementSlot S) : ℂ :=
  ∏ a : NativeNode D s, if IsCore D hS (nativeNodeAt D hS s a) then 1 else G (nativeNodeAt D hS s a)

/-- The slot factor only reads the native nodes of the slot. -/
theorem slotFac_congr (G G' : GNode (D.forest hS) → ℂ) (s : ReplacementSlot S)
    (h : ∀ a : NativeNode D s, G (nativeNodeAt D hS s a) = G' (nativeNodeAt D hS s a)) :
    slotFac D hS G s = slotFac D hS G' s :=
  Finset.prod_congr rfl fun a _ => by rw [h a]

/-- Nodes = core nodes ⊔ non-core native nodes of the slots. -/
theorem prod_node_split (G : GNode (D.forest hS) → ℂ) :
    ∏ z, G z = (∏ β : GBranch S.tree, G (D.coreBranch hS β).toNode) * ∏ s, slotFac D hS G s := by
  have h1 : ∏ z, G z = (∏ z, if IsCore D hS z then G z else 1) * ∏ z, if IsCore D hS z then 1 else G z := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun z _ => ?_
    split_ifs <;> simp
  have h2 : (∏ z, if IsCore D hS z then G z else 1) = ∏ β : GBranch S.tree, G (D.coreBranch hS β).toNode := by
    rw [← Finset.prod_filter]
    have he : univ.filter (IsCore D hS) = Finset.univ.image (fun β : GBranch S.tree => (D.coreBranch hS β).toNode) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, IsCore]
      constructor
      · rintro ⟨β, hβ⟩; exact ⟨β, hβ.symm⟩
      · rintro ⟨β, hβ⟩; exact ⟨β, hβ.symm⟩
    rw [he, Finset.prod_image fun β _ β' _ h =>
      MkSlots.IntRest.coreBranch_injective D hS (Mole.branch_toNode_injective h)]
  have h3 : (∏ z, if IsCore D hS z then 1 else G z) = ∏ s, slotFac D hS G s := by
    unfold slotFac
    exact (Fintype.prod_equiv (nativeNodeEquiv D hS)
      (fun x => if IsCore D hS (nativeNodeAt D hS x.1 x.2) then 1 else G (nativeNodeAt D hS x.1 x.2)) _
      fun x => rfl).symm.trans (Fintype.prod_sigma _)
  rw [h1, h2, h3]

omit [Fintype ι] [DecidableEq ι] in
/-- Cores of the retained branches are the cores of the `G_sb` branches. -/
theorem prod_core_split (G : GNode (D.forest hS) → ℂ) :
    ∏ β : GBranch S.tree, G (D.coreBranch hS β).toNode =
      (∏ c : GBranch Gsb.tree, G (D.coreBranch hS (Φ.br c)).toNode) *
        ∏ β ∈ univ.filter (fun β : GBranch S.tree => ¬ Ret blk β.toNode), G (D.coreBranch hS β).toNode := by
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun β : GBranch S.tree => Ret blk β.toNode)]
  congr 1
  have he : univ.filter (fun β : GBranch S.tree => Ret blk β.toNode) = Finset.univ.image Φ.br := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact Φ.exists_br h
    · rintro ⟨c, rfl⟩; exact Φ.ret_br c
  rw [he, Finset.prod_image fun c _ c' _ h => Φ.br_inj h]

/-- `G_sb` branches = non-hinges ⊔ hinges (one per unit). -/
theorem prod_gsb_split (hd : Disj blk) (F : GBranch Gsb.tree → ℂ) :
    ∏ c, F c = (∏ c ∈ univ.filter (fun c => c ∉ Φ.hinges hd), F c) * ∏ j, F (Φ.hinge hd j) := by
  rw [← Finset.prod_filter_mul_prod_filter_not univ (fun c => c ∉ Φ.hinges hd), mul_comm, mul_comm _ (∏ j, _)]
  congr 1
  have he : univ.filter (fun c => ¬ c ∉ Φ.hinges hd) = Φ.hinges hd := by
    ext c; simp
  rw [he]
  unfold VineB.SpliceShape.hinges
  rw [Finset.prod_image fun j _ j' _ h => Φ.hinge_inj hd h]

variable {LG : LayeredGarden w} {J : Finset (Fin w)}

/-- **T4 (the partition).** For a node weight `G` that is `1` off the capped stem, under `StemRet`: the product over
all nodes is the atom part times the top part times the slot part. -/
theorem stem_split (hd : Disj blk) (hR : StemRet S D.tree blk LG J) (G : GNode (D.forest hS) → ℂ)
    (hG : ∀ z, ¬ OnStemAddr LG J z.1 → G z = 1) :
    ∏ z, G z = (∏ c ∈ univ.filter (fun c => c ∉ Φ.hinges hd), G (D.coreBranch hS (Φ.br c)).toNode) *
      (∏ j, G (D.coreBranch hS (blk j).upper).toNode) * ∏ s, slotFac D hS G s := by
  rw [prod_node_split D hS G, prod_core_split D hS Φ G, prod_gsb_split Φ hd]
  have hnr : ∏ β ∈ univ.filter (fun β : GBranch S.tree => ¬ Ret blk β.toNode), G (D.coreBranch hS β).toNode = 1 := by
    refine Finset.prod_eq_one fun β hβ => hG _ fun hz => ?_
    exact (Finset.mem_filter.mp hβ).2 (ret_core_of_stem D hS hR hz)
  rw [hnr, mul_one]
  congr 2
  exact Finset.prod_congr rfl fun j _ => by rw [Φ.br_hinge hd j]

/-- A slot that is not retained carries no capped-stem node, so its factor is `1`. -/
theorem slotFac_eq_one_of_not_slotRet (hR : StemRet S D.tree blk LG J) (G : GNode (D.forest hS) → ℂ)
    (hG : ∀ z, ¬ OnStemAddr LG J z.1 → G z = 1) (s : ReplacementSlot S) (hs : ¬ SlotRet hS (blk := blk) s) :
    slotFac D hS G s = 1 := by
  refine Finset.prod_eq_one fun a _ => ?_
  split_ifs with hc
  · rfl
  · refine hG _ fun hz => hs ?_
    have := slotRet_of_stem D hS hR hz
    rwa [MkSlots.slotOf_nativeNodeAt] at this

end Split

/-! ## The interface identities -/

section Omega
variable {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)

/-- **The resonance factor at a core node is the skeleton resonance factor on the collapsed decoration.** -/
theorem omegaNode_core_collapse {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (L : ℝ) (base : Mom d) (β : GBranch S.tree) :
    omegaNode (D.garden hS) (cosetDecoration (D.garden hS) L base κ.1) (D.coreBranch hS β) =
      omegaNode S (cosetDecoration S L base (collapseGenDecoration D hS κ).1) β := by
  have hc : ∀ i : Fin 3, κ.1 ((D.coreBranch hS β).child i) = (collapseGenDecoration D hS κ).1 (β.child i) := by
    intro i
    show κ.1 ((D.coreBranch hS β).child i) = κ.1 (attachedNode D hS (β.child i))
    rw [attachedNode_child]
  have hb : κ.1 (D.coreBranch hS β).toNode = (collapseGenDecoration D hS κ).1 β.toNode := by
    show κ.1 (D.coreBranch hS β).toNode = κ.1 (attachedNode D hS β.toNode)
    exact (chain_attachment_momentum D hS κ.1 κ.2.1 β).symm
  unfold omegaNode cosetDecoration
  erw [hc 0, hc 1, hc 2, hb]

/-- **The top part is B3-2's unit top filter** on the collapsed decoration. -/
theorem radProd_core_eq_nodeWeight {n : Fin w → (Fin d → ℤ)} {nfl : Fin d → ℤ}
    (κ : GenDecoration (D.garden hS) d n nfl) (L : ℝ) (base : Mom d) (β : GBranch S.tree) (rs : List ℝ) :
    (radProd rs (omegaNode (D.garden hS) (cosetDecoration (D.garden hS) L base κ.1) (D.coreBranch hS β)) : ℂ) =
      VineSpaceK.nodeWeight (V5W2L.topFilterWeightL rs) L base β (collapseGenDecoration D hS κ).1 := by
  rw [omegaNode_core_collapse D hS κ L base β]
  rfl

end Omega

/-- **The atom part through a splice shape**: at a non-hinge `G_sb` atom, the `G_sb` resonance factor is the
skeleton resonance factor at `Φ.br c` for momentum assignments that agree through `Φ.node`. -/
theorem omegaNode_shape {S Gsb : Garden w} {ι : Type} {blk : ι → CLBlock S} (Φ : SpliceShape blk Gsb)
    (kS : GNode S.tree → Mom d) (kG : GNode Gsb.tree → Mom d) (hk : ∀ y, kS (Φ.node y) = kG y)
    (c : GBranch Gsb.tree) (hc : ∀ j, Φ.br c ≠ (blk j).upper) :
    omegaNode Gsb kG c = omegaNode S kS (Φ.br c) := by
  unfold omegaNode
  have hch : ∀ i, kG (c.child i) = kS ((Φ.br c).child i) := fun i => by
    rw [← hk, Φ.child c i hc]
  rw [hch 0, hch 1, hch 2, ← hk, ← Φ.br_node]

end WaveTurbulence.Flower.MkSlotsT
