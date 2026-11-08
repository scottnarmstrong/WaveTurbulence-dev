/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.Stage1MKGate.Hyp

/-! # B3s MK-SLOTS: the protected data of a class piece on `G_sb`

For a prescribed point `a` and a fine marking `mkF`, the piece of B4's `classPiece` lives on
`G_sb = (stSt a.prime.skeleton a.totalSigma (classMk mkF a)).G`. A branch `c` of `G_sb` has an old name
`M.ob c` (a skeleton branch) and that skeleton branch has a core branch in the layered garden `a.layered`
(`decodedCoreBranch`). Through this injective map `coreOf`:

* `protOf`: the protected atoms `Π_sb` (core node in `Π = protI`), with `card ≤ |Π|`;
* `fixOf`: the pins of `G_sb` (the intrinsic pins `fixCap` of the core branch), all protected;
* `sibIndOf`: the dagger sibling indicator at the `G_sb` atoms whose core branch is a capped flower parent, a
  `[0,1]`-valued function of the momenta at protected atoms and their children;
* `pieceRest_of`: the six B3s fields of `MkPieceRest` (`PieceRestB3s`) for `classPiece`, given the pinned layers and
  the filter facts. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Set Finset
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice (Prescription stSt vinesV0)

namespace WaveTurbulence.Flower.MkSlots

variable {w : ℕ}

/-- The splice state of the piece of `a` at the fine marking `mkF` (marked set `classMk mkF a`). -/
abbrev stA (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :=
  stSt a.prime.skeleton a.totalSigma (classMk mkF a)

/-- The core branch, in the layered garden of `a`, of a branch of `G_sb`. -/
def coreOf (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) (c : GBranch (stA mkF a).G.tree) :
    GBranch a.layered.garden.tree :=
  a.prime.data.decodedCoreBranch a.prime.prime.1 a.prime.decodes ((stA mkF a).M.ob c)

theorem coreOf_injective (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    Function.Injective (coreOf mkF a) :=
  (a.prime.data.decodedCoreEmbedding a.prime.prime.1 a.prime.decodes).injective.comp (stA mkF a).M.ob_inj

theorem coreOf_toNode_injective (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    Function.Injective fun c => (coreOf mkF a c).toNode :=
  fun _ _ h => coreOf_injective mkF a (Mole.branch_toNode_injective h)

/-- The protected atoms `Π_sb` of the piece: atoms whose core node is protected. -/
def protOf (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) : Finset (GBranch (stA mkF a).G.tree) :=
  univ.filter fun c => (coreOf mkF a c).toNode ∈ protI a.layered J pat t s kSel

/-- The pins of the piece: the intrinsic pins of the core branch. -/
def fixOf (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (mkF : Stage1Mk.MarkFn w)
    (a : PrescribedPrimeGarden w) (c : GBranch (stA mkF a).G.tree) : Option ℝ :=
  fixCap a.layered J pat t s (coreOf mkF a c)

theorem card_protOf_le (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ) (kSel : Fin w → Option ℕ)
    (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w) :
    (protOf J pat t s kSel mkF a).card ≤ (protI a.layered J pat t s kSel).card := by
  refine Finset.card_le_card_of_injOn (fun c => (coreOf mkF a c).toNode) (fun c hc => ?_)
    (fun c _ c' _ h => coreOf_toNode_injective mkF a h)
  exact (Finset.mem_filter.1 hc).2

/-- A pinned branch is protected (it is a seed of `Π`). -/
theorem mem_protI_of_fixCap {LG : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ}
    {kSel : Fin w → Option ℕ} {b : GBranch LG.garden.tree} (h : (fixCap LG J pat t s b).isSome) :
    b.toNode ∈ protI LG J pat t s kSel := by
  unfold protI protectedSet
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, b.toNode, ⟨rfl, Or.inl rfl⟩, Or.inr ⟨b, rfl, Or.inl h⟩⟩

theorem fixOf_prot {J : Finset (Fin w)} {pat : Fin w → FixPat} {t s : ℝ} {kSel : Fin w → Option ℕ}
    {mkF : Stage1Mk.MarkFn w} {a : PrescribedPrimeGarden w} (c : GBranch (stA mkF a).G.tree)
    (h : (fixOf J pat t s mkF a c).isSome) : c ∈ protOf J pat t s kSel mkF a :=
  Finset.mem_filter.2 ⟨Finset.mem_univ _, mem_protI_of_fixCap h⟩

/-- A capped flower parent lies on the capped stem, hence in layer `p` (`CapGeo.stem_layer`). -/
theorem layer_capFlowerParent {LG : LayeredGarden w} {J : Finset (Fin w)} {p : ℕ} (hG : CapGeo LG J p)
    {b : GBranch LG.garden.tree} (hb : IsCapFlowerParent LG J b) : LG.layer b.toNode = p := by
  obtain ⟨ℓ, hℓ, hpar⟩ := hb
  refine hG.stem_layer _ ⟨ℓ, hℓ, ?_⟩
  obtain ⟨htree, i, hpath⟩ := hpar
  exact ⟨htree.symm, ⟨[i], hpath.symm⟩⟩

/-- The dagger sibling indicator of the piece: at every atom whose core branch is a capped flower parent, the
children that are not the capped flower carry the prescribed momenta `cc`. -/
def sibIndOf {d : ℕ} (J : Finset (Fin w)) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w)
    (dag : Option (Fin w → Fin 3 → Mom d)) (flw : GBranch (stA mkF a).G.tree → Fin 3 → Prop)
    (k : GNode (stA mkF a).G.tree → Mom d) : ℝ :=
  dag.elim 1 fun cc => ∏ c : GBranch (stA mkF a).G.tree,
    if IsCapFlowerParent a.layered J (coreOf mkF a c) then
      ∏ i : Fin 3, (if flw c i then 1 else if k (c.child i) = cc c.1.1 i then 1 else 0) else 1

theorem sibIndOf_mem {d : ℕ} (J : Finset (Fin w)) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w)
    (dag : Option (Fin w → Fin 3 → Mom d)) (flw : GBranch (stA mkF a).G.tree → Fin 3 → Prop)
    (k : GNode (stA mkF a).G.tree → Mom d) :
    0 ≤ sibIndOf J mkF a dag flw k ∧ sibIndOf J mkF a dag flw k ≤ 1 := by
  unfold sibIndOf
  cases dag with
  | none => simp
  | some cc =>
    simp only [Option.elim]
    constructor
    · refine Finset.prod_nonneg fun c _ => ?_
      split_ifs
      · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
      · norm_num
    · refine Finset.prod_le_one₀ (fun c _ => ?_) fun c _ => ?_
      · split_ifs
        · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num
        · norm_num
      · split_ifs
        · exact Finset.prod_le_one₀ (fun i _ => by split_ifs <;> norm_num) fun i _ => by split_ifs <;> norm_num
        · exact le_rfl

/-- The indicator reads only the momenta at the children of protected atoms (capped flower parents are seeds). -/
theorem sibIndOf_local {d : ℕ} (J : Finset (Fin w)) (pat : Fin w → FixPat) (t s : ℝ)
    (kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w)
    (dag : Option (Fin w → Fin 3 → Mom d)) (flw : GBranch (stA mkF a).G.tree → Fin 3 → Prop)
    (k k' : GNode (stA mkF a).G.tree → Mom d)
    (h : ∀ c ∈ protOf J pat t s kSel mkF a, ∀ i : Fin 3, k (c.child i) = k' (c.child i)) :
    sibIndOf J mkF a dag flw k = sibIndOf J mkF a dag flw k' := by
  unfold sibIndOf
  cases dag with
  | none => rfl
  | some cc =>
    simp only [Option.elim]
    refine Finset.prod_congr rfl fun c _ => ?_
    by_cases hc : IsCapFlowerParent a.layered J (coreOf mkF a c)
    · have hp : c ∈ protOf J pat t s kSel mkF a := fixOf_prot c (by
        simp [fixOf, fixCap, hc])
      simp only [hc, ite_true]
      exact Finset.prod_congr rfl fun i _ => by rw [h c hp i]
    · simp only [hc, ite_false]

end WaveTurbulence.Flower.MkSlots
