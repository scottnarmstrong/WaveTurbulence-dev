/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Typed.Defs
public import WaveTurbulence.Foundations.Flower.Cases.Defs
public import WaveTurbulence.Foundations.Flower.Fam.Defs

/-! # A1 MK-DEFS: the marked layer's definitions (copied by source from the S-MARKED probe, sections 2 and 3,
see COPIED-SHA256SUMS). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory

namespace WaveTurbulence.Flower.MkDefs

/-! ## §2 Capped components, the protected set, and the marked weight class. -/

variable {w : ℕ}

/-- In a capped garden with cap trees `J`, a (capped) flower is a non-cap leaf paired with a cap root. -/
def IsCapFlower (LG : LayeredGarden w) (J : Finset (Fin w)) (ℓ : GLeaf LG.garden.tree) : Prop :=
  ℓ.1.1 ∉ J ∧ (LG.garden.pair ℓ).1.1 ∈ J

/-- The parent of a capped flower (the frozen pin at `s`). -/
def IsCapFlowerParent (LG : LayeredGarden w) (J : Finset (Fin w)) (b : GBranch LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ b.IsParentOf ℓ

/-- Capped stem: ancestors of a capped flower. -/
def OnCapStem (LG : LayeredGarden w) (J : Finset (Fin w)) (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ a.IsDesc ℓ.toNode

/-- The capped stem set of tree `j` (flower parent omitted), as in `Flower.Cases.stemSet`. -/
noncomputable def stemSetCap (LG : LayeredGarden w) (J : Finset (Fin w)) (j : Fin w) : Finset (GBranch LG.garden.tree) :=
  Finset.univ.filter fun b : GBranch LG.garden.tree =>
    b.1.1 = j ∧ OnCapStem LG J b.toNode ∧ ¬ IsCapFlowerParent LG J b

/-- Capped stem filters (the transport of `Flower.Cases.stemFilter`). -/
noncomputable def stemFilterCap {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (L : ℝ)
    (σ : Fin w → Option ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, (σ j).elim 1 fun i =>
    prodDyadicCut (2 ^ i * L) 0 (stemSetCap LG J j) (fun b => |omegaNode LG.garden k b|)

/-- One node `a` is within distance one of a seed `s` (same node, its parent, or a child). -/
def NearNode {tree : Fin w → TTree} (a s : GNode tree) : Prop :=
  a.1.1 = s.1.1 ∧ (a.1.2 = s.1.2 ∨ (s.1.2 ≠ [] ∧ a.1.2 = s.1.2.dropLast) ∨
    (a.1.2 ≠ [] ∧ a.1.2.dropLast = s.1.2))

/-- **The protected set Π** (o75 §2.2, (Π1)+(Π2), and o104's pattern vertices): the closed unit neighbourhood of
the seeds — roots of non-cap trees, pinned branches (flower parents at `s`, pattern pins), selected vertices. It
contains the flower and its siblings (children of the pinned parent). `|Π| ≤ 5·#seeds ≤ 20` per original tree. -/
noncomputable def protectedSet (LG : LayeredGarden w) (J : Finset (Fin w))
    (fix : GBranch LG.garden.tree → Option ℝ) (sel : Finset (GBranch LG.garden.tree)) :
    Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun a => ∃ s : GNode LG.garden.tree, NearNode a s ∧
    ((s.1.1 ∉ J ∧ s.1.2 = []) ∨ ∃ b : GBranch LG.garden.tree, b.toNode = s ∧ ((fix b).isSome ∨ b ∈ sel))

/-- Card bound of Π (CAPS-MARK export). -/
def ProtectedCardBound : Prop :=
  ∀ {w : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (fix : GBranch LG.garden.tree → Option ℝ)
    (sel : Finset (GBranch LG.garden.tree)),
    (protectedSet LG J fix sel).card ≤
      5 * ((Finset.univ.filter fun j : Fin w => j ∉ J).card +
        (Finset.univ.filter fun b : GBranch LG.garden.tree => (fix b).isSome).card + sel.card)

/-- The anchored pair-type profile product: pairs meeting a cap tree have profile `1`. -/
noncomputable def leafProdCap {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (h : ℕ → Fin w → Fin w → Mom d → ℝ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ ℓ ∈ inputLeaves LG.garden,
    if ℓ.1.1 ∈ J ∨ (LG.garden.pair ℓ).1.1 ∈ J then 1 else LGSpine.typeProfiles LG h ℓ.1 (k ℓ.toNode)

/-- Dagger sibling indicators at capped flower parents (transport of `sibWeight`). -/
noncomputable def sibWeightCap {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (c : Fin w → Fin 3 → Mom d)
    (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ b : GBranch LG.garden.tree, if IsCapFlowerParent LG J b then
    ∏ i : Fin 3, (if (∃ ℓ : GLeaf LG.garden.tree, IsCapFlower LG J ℓ ∧ ℓ.toNode = b.child i) then 1 else
      if k (b.child i) = c b.1.1 i then 1 else 0) else 1

/-- The selected-face weight of Core-G after FL-SHELL: in tree `j` the selected vertex `v j` carries
`R⁻¹·chiD(|Ω|/R)`, the other stem vertices `chi0(|Ω|/R)` (scales `Rs j`). -/
noncomputable def chiD (u : ℝ) : ℝ := -u * deriv chi0 u

noncomputable def selWeightCap {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w))
    (v : Fin w → Option (GBranch LG.garden.tree)) (Rs : Fin w → ℝ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, (v j).elim 1 fun vj =>
    (Rs j)⁻¹ * chiD (|omegaNode LG.garden k vj| / Rs j) *
      ∏ b ∈ (stemSetCap LG J j).erase vj, chi0 (|omegaNode LG.garden k b| / Rs j)

/-- The marked weight on a capped component: frontier cutoffs × capped stem filters × selected-face weights
× anchored pair-type profiles × dagger indicators. -/
noncomputable def markedWeight {d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ) (L : ℝ)
    (Rf : Fin w → Option ℝ) (σ : Fin w → Option ℕ) (v : Fin w → Option (GBranch LG.garden.tree))
    (Rs : Fin w → ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ) (dag : Option (Fin w → Fin 3 → Mom d))
    (k : GNode LG.garden.tree → Mom d) : ℝ :=
  Typed.frontierW LG p Rf k * stemFilterCap LG J L σ k * selWeightCap LG J v Rs k * leafProdCap LG J h k *
    dag.elim 1 (fun c => sibWeightCap LG J c k)

/-- A capped component's value: the frozen kernel with `F ≡ 1`, pins `fix`, removed phases `off`, upper time `t`,
roots `roots` (original roots `n`, cap roots `n'`), no flowers. -/
noncomputable def compValue (P : WTParams) {R : ℕ} (LG : LayeredGarden (2 * R))
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom P.d) → ℝ) (t : ℝ) (roots : Fin (2 * R) → (Fin P.d → ℤ)) : ℂ :=
  kernelKgen P.L P.γ P.δ (fun _ _ => 1) LG fix off wt (fun _ => t) 0 roots 0

/-! ## §3 The marked twist closure and the marked component bound (the per-component target). -/

/-- The type of a marking rule: from cap trees, pins and selected vertices of each garden, which skeleton branches of
a twist reconstruction are protected (the branch, or a regular object inflated at it, contains a protected vertex).
S-STAGE1MK defines the concrete rule `protSkOf` (via `inflatedPosition`, o75 Def. 2.3); the targets below are claimed
**only** at that rule (a too-large rule makes the twist closure vacuous and the bound false). -/
abbrev MarkRule (R : ℕ) : Type 1 :=
  ∀ (_J : Finset (Fin (2 * R))) (_fix : ∀ LG : LayeredGarden (2 * R), GBranch LG.garden.tree → Option ℝ)
    (_sel : ∀ LG : LayeredGarden (2 * R), Finset (GBranch LG.garden.tree))
    {ι : Type} (B : LFTwist.FamilyReconstruction (2 * R) ι), GBranch B.skeleton.tree → Prop

/-- Closure under twists at UNMARKED core vines only (o75 Lemma 2). `protSk B b`: the skeleton branch `b` (or its
inflated regular object) contains a protected vertex of `B.layered`; S-STAGE1MK fixes it via `inflatedPosition`. -/
def MarkedTwistClosed (p : ℕ) (A : Finset (LayeredGarden w))
    (protSk : ∀ {ι : Type} (B : LFTwist.FamilyReconstruction w ι), GBranch B.skeleton.tree → Prop) : Prop :=
  ∀ (kind : Bool) (ι : Type) (B : LFTwist.FamilyReconstruction w ι) (Lst : List ι),
    Reg.Skeleton.IsPrimeGarden B.skeleton → LFTwist.CanonicalObject p kind B.layered → B.layered ∈ A →
    (∀ i, ∀ b ∈ B.family.atoms i, b ≠ B.family.upper i → ¬ protSk B b) →
    ∀ LH ∈ B.outputs p kind Lst, LH ∈ A

/-! The capped geometry of a component (ruling R163; moved verbatim from D2b PROT-GEO `ProtGeo/Geo.lean`
lines 33–46, sha256 `5453a5c6…375f`). -/

/-- **Standing geometry of a capped component** (supplement Lemma 2.1; o73 Prop 3.1 uses T2261): cap trees are
single leaves, layers are at most `p`, capped stem nodes are in layer `p`, at most one capped flower per tree. -/
structure CapGeo (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ) : Prop where
  cap_leaf : ∀ j ∈ J, LG.garden.tree j = TTree.leaf
  layer_le : ∀ a, LG.layer a ≤ p
  stem_layer : ∀ a, OnCapStem LG J a → LG.layer a = p
  one_flower : ∀ ℓ ℓ' : GLeaf LG.garden.tree, IsCapFlower LG J ℓ → IsCapFlower LG J ℓ' → ℓ.1.1 = ℓ'.1.1 → ℓ = ℓ'

/-- The capped transport of the frozen `PatValid` clause for `dChild` (T L2331, F68): a branching child of a capped
flower parent pinned by a `dChild` pattern is in layer `p`. -/
def CapPatValid (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (p : ℕ) : Prop :=
  ∀ (b c : GBranch LG.garden.tree) (i : Fin 3), IsCapFlowerParent LG J c → pat c.1.1 = FixPat.dChild i →
    b.1 = (c.1.1, c.1.2 ++ [i]) → LG.layer b.toNode = p


/-- **MkCarries** (ruling R156 (1), F-7): the carrier predicate of a capped component. Main's `Stage1Carries` with
the flower-modified top truncation `N_{p+1}^4` (TARGET L2297; supplement Lemma 2.1(4), Prop 10.3′) in place of
`N_{p+1}`, and WITHOUT the regular-couple exclusion (R156 (2), F-4: width-2 regular capped components are ordinary
components here, bounded downstream by D6). The flower kinds `Y`, `W` stay as per-tree labels inside the class. -/
def MkCarries (P : WTParams) (p n : ℕ) {w : ℕ} (LG : LayeredGarden w) : Prop :=
  IsCanonGC (p + 1) LG ∧ LG.IsTrunc (p + 1 - 1) (P.N (p + 1) ^ 4) (P.N (p + 1 - 1)) ∧
    LG.garden.order = n ∧ IsBalancedSig LG.garden.sig

/-- Layers of a `MkCarries` garden are at most `p`. -/
theorem layer_le_of_mkCarries {P : WTParams} {p n : ℕ} {LG : LayeredGarden w} (h : MkCarries P p n LG)
    (a : GNode LG.garden.tree) : LG.layer a ≤ p :=
  Canon.layer_le_of_isCanonGC h.1 a

/- (A2-R) S-MARKED's `MarkedComponentBoundAt` (arbitrary `fix/off/v : ∀ LG, …`) is deleted: it is not provable
(B0 finding F-B0-1). The per-component target is `MarkedComponentBoundAtI` in `MkDefs.Stage1MK`. -/


end WaveTurbulence.Flower.MkDefs
