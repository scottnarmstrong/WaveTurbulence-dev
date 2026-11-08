/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsComp.Struct
public import WaveTurbulence.Foundations.Flower.MkAsm.Comp
public import WaveTurbulence.Foundations.Spine.TwistClosedNR
/-! # A3b CAPS-COMP: the component classes and their twist closure

The class of component `c` of a structure is the set of layered gardens `G` of width `2R_c` with
* `CompBase`: `MkCarries` at the component order, and the prescribed signature (originals `(-1)^j`, caps
  `-ζ(-1)^j`);
* `CompLabels`: the caps are trivial trees, each cap is paired into its original tree (`matchOK`), and every
  original tree satisfies the capped stem, kind and pattern conditions.

**Twist closure.** `CompBase` is preserved by every LF batch (main: canonicity, order, top orders, signature;
`compBase_output`). The labels involve only protected vertices (roots, root children, flower, flower parent and its
neighbours; supplement Lemma 2.1(4), R156). Their invariance under batches at unprotected vines is o75 Lemma 2⁺(b)
(B0 SCOPE §5.1(a): "In Lean that is the `MarkedTwistClosed` hypothesis, supplied by A2/A3b"). Main has no node map
across an LF twist (B0 §8). This file states that invariance as the distinctly named Prop `CapsTwistStable` and
derives the closure of the classes from it (`markedTwistClosed_of_stable`). -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsComp
open TTree Finset WaveTurbulence.FlowerP7 WaveTurbulence.Flower.CapsGlue WaveTurbulence.Flower.CapsId
open WaveTurbulence.Flower.MkDefs WaveTurbulence.LGSpine

/-! ## Canonical objects are `IsCanonGC`; width-2 plain gardens are irreducible -/

theorem isCanonGC_of_canonicalObject {p w : ℕ} {kind : Bool} {LG : LayeredGarden w}
    (h : LFTwist.CanonicalObject p kind LG) : IsCanonGC (p + 1) LG := by
  cases h with
  | garden hc => exact ⟨hc.2.1, Or.inl ⟨hc.1, hc.2.2.1⟩, hc.2.2.2⟩
  | couple hc =>
    refine ⟨hc.1.1, Or.inr ⟨rfl, fun j => ?_⟩, hc.2⟩
    rw [hc.1.2]
    fin_cases j <;> simp

theorem irreducible_of_isCanonGC {p w : ℕ} {LG : LayeredGarden w} (h : IsCanonGC (p + 1) LG) :
    LG.garden.Irreducible := by
  obtain ⟨hpl, hcase, -⟩ := h
  rcases hcase with ⟨-, hirr⟩ | ⟨rfl, -⟩
  · exact hirr
  · intro A hA hne hcp
    obtain ⟨j, hj⟩ := hA
    have hA1 : A = {j} := by
      ext i
      simp only [mem_singleton]
      constructor
      · intro hi
        by_contra hij
        apply hne
        ext k
        simp only [mem_univ, iff_true]
        fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
      · rintro rfl; exact hj
    subst hA1
    have e : LG.garden.leavesOf {j} = (GNode.root LG.garden.tree j).leavesBelow := by
      ext ℓ
      rw [mem_leavesOf]
      simp only [GNode.leavesBelow, mem_filter, mem_univ, true_and, mem_singleton]
      show ℓ.1.1 = j ↔ (j = ℓ.1.1 ∧ [] <+: ℓ.1.2)
      exact ⟨fun h => ⟨h.symm, List.nil_prefix⟩, fun h => h.1.symm⟩
    rw [e] at hcp
    have he := Canon.even_card_of_completelyPaired LG.garden _ _ rfl hcp
    exact (Nat.not_even_iff_odd.2 (Canon.odd_card_leavesBelow _)) he

/-! ## The class predicates -/

/-- The prescribed signature of the capped trees: originals `(-1)^j`, caps `-ζ (-1)^j`. -/
def capSgn {w : ℕ} (ζ : ℤˣ) (i : Fin (2 * w)) : ℤˣ :=
  Sum.elim (fun j : Fin w => (-1 : ℤˣ) ^ (j : ℕ)) (fun j : Fin w => -(ζ * (-1) ^ (j : ℕ))) ((capσ w).symm i)

@[simp] theorem capSgn_inl {w : ℕ} (ζ : ℤˣ) (j : Fin w) : capSgn ζ (capσ w (.inl j)) = (-1) ^ (j : ℕ) := by
  simp [capSgn]

@[simp] theorem capSgn_inr {w : ℕ} (ζ : ℤˣ) (j : Fin w) : capSgn ζ (capσ w (.inr j)) = -(ζ * (-1) ^ (j : ℕ)) := by
  simp [capSgn]

/-- The twist-invariant part of a component class. -/
def CompBase (P : WTParams) (p n : ℕ) {W : ℕ} (sg : Fin W → ℤˣ) (G : LayeredGarden W) : Prop :=
  MkCarries P p n G ∧ G.garden.sig = sg

/-- The labels of a component (caps `J`, partner rule `matchOK`, pattern `pat`). -/
def CompLabels {W : ℕ} (p Ntr : ℕ) (kind : FlowerKind) (J : Finset (Fin W)) (matchOK : Fin W → Fin W → Prop)
    (pat : Fin W → FixPat) (G : LayeredGarden W) : Prop :=
  (∀ i ∈ J, G.garden.tree i = TTree.leaf) ∧
    (∀ ℓ : GLeaf G.garden.tree, ℓ.1.1 ∈ J → matchOK ℓ.1.1 (G.garden.pair ℓ).1.1) ∧
    ∀ i, i ∉ J → CapStem G J p i ∧ CapKindOK G J p Ntr i kind ∧ CapPatExist G J p i (pat i)

/-- Invariance of `Lab` under the outputs of LF batches at unprotected core vines, from gardens satisfying `Pre`. -/
def LabelTwistStable (p : ℕ) {W : ℕ} (Pre Lab : LayeredGarden W → Prop)
    (protSk : ∀ {ι : Type} (B : LFTwist.FamilyReconstruction W ι), GBranch B.skeleton.tree → Prop) : Prop :=
  ∀ (kind : Bool) (ι : Type) (B : LFTwist.FamilyReconstruction W ι) (Lst : List ι),
    Reg.Skeleton.IsPrimeGarden B.skeleton → LFTwist.CanonicalObject p kind B.layered → Pre B.layered →
    (∀ i, ∀ b ∈ B.family.atoms i, b ≠ B.family.upper i → ¬ protSk B b) →
    ∀ LH ∈ B.outputs p kind Lst, Lab LH

/-- **The twist stability of the capped labels** (o75 Lemma 2⁺(b) for the labels of supplement Lemma 2.1(4); a
distinctly named input, see the module docstring). -/
def CapsTwistStable : Prop :=
  ∀ (P : WTParams) (p n R Ntr : ℕ) (kind : FlowerKind) (J : Finset (Fin (2 * R)))
    (matchOK : Fin (2 * R) → Fin (2 * R) → Prop) (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ)
    (t s : ℝ) (sg : Fin (2 * R) → ℤˣ),
    LabelTwistStable p (fun G => CompBase P p n sg G ∧ CompLabels p Ntr kind J matchOK pat G)
      (CompLabels p Ntr kind J matchOK pat)
      (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel))

/-- `CompBase` is preserved by every LF batch output. -/
theorem compBase_output (P : WTParams) {p n W : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    {sg : Fin W → ℤˣ} {kind : Bool} {ι : Type} (B : LFTwist.FamilyReconstruction W ι) (Lst : List ι)
    (hcan : LFTwist.CanonicalObject p kind B.layered) (hB : CompBase P p n sg B.layered)
    {LH : LayeredGarden W} (hLH : LH ∈ B.outputs p kind Lst) : CompBase P p n sg LH := by
  obtain ⟨⟨_, htr, hord, hbal⟩, hsg⟩ := hB
  obtain ⟨M', B', _, hbatch, rfl⟩ := hLH
  have hord' : B'.layered.garden.order = n := hbatch.order.trans hord
  have hsig' : B'.layered.garden.sig = sg := hbatch.layered_sig.trans hsg
  have hnN : B.layered.garden.order ≤ P.N p := by rw [hord]; exact hn.trans (N_fourth_le_N P hp)
  refine ⟨⟨isCanonGC_of_canonicalObject (hbatch.canonical hcan), ?_, hord', ?_⟩, hsig'⟩
  · show B'.layered.IsTrunc p (P.N (p + 1) ^ 4) (P.N p)
    exact (hbatch.isTrunc _ _ hnN).2 htr
  · unfold IsBalancedSig at hbal ⊢
    rw [hbatch.layered_sig]; exact hbal

/-- The finite class of a predicate at fixed order (layers `≤ p` by canonicity). -/
theorem finite_compBase (P : WTParams) (p n W : ℕ) (sg : Fin W → ℤˣ) (Q : LayeredGarden W → Prop) :
    {G : LayeredGarden W | CompBase P p n sg G ∧ Q G}.Finite :=
  (Canon.finite_layeredGardens W n p).subset fun _ hG =>
    ⟨hG.1.1.2.2.1.le, Canon.layer_le_of_isCanonGC hG.1.1.1⟩

/-- The class as a finset. -/
def classOf (P : WTParams) (p n Ntr : ℕ) (kind : FlowerKind) {W : ℕ} (sg : Fin W → ℤˣ) (J : Finset (Fin W))
    (matchOK : Fin W → Fin W → Prop) (pat : Fin W → FixPat) : Finset (LayeredGarden W) :=
  (finite_compBase P p n W sg (CompLabels p Ntr kind J matchOK pat)).toFinset

theorem mem_classOf {P : WTParams} {p n Ntr : ℕ} {kind : FlowerKind} {W : ℕ} {sg : Fin W → ℤˣ}
    {J : Finset (Fin W)} {matchOK : Fin W → Fin W → Prop} {pat : Fin W → FixPat} {G : LayeredGarden W} :
    G ∈ classOf P p n Ntr kind sg J matchOK pat ↔ CompBase P p n sg G ∧ CompLabels p Ntr kind J matchOK pat G := by
  unfold classOf; rw [Set.Finite.mem_toFinset]; rfl

/-- **Twist closure of the classes**, from the label stability. -/
theorem markedTwistClosed_of_stable (hst : CapsTwistStable) (P : WTParams) {p n R Ntr : ℕ} (hp : p < P.D)
    (hn : n ≤ P.N (p + 1) ^ 4) (kind : FlowerKind) (sg : Fin (2 * R) → ℤˣ) (J : Finset (Fin (2 * R)))
    (matchOK : Fin (2 * R) → Fin (2 * R) → Prop) (pat : Fin (2 * R) → FixPat) (kSel : Fin (2 * R) → Option ℕ)
    (t s : ℝ) :
    MarkedTwistClosed p (classOf P p n Ntr kind sg J matchOK pat)
      (protSkOf R J (fun LG => fixCap LG J pat t s) (fun LG => selSetCap LG J kSel)) := by
  intro kk ι B Lst hprime hcan hmem hun LH hLH
  rw [mem_classOf] at hmem ⊢
  exact ⟨compBase_output P hp hn B Lst hcan hmem.1 hLH,
    hst P p n R Ntr kind J matchOK pat kSel t s sg kk ι B Lst hprime hcan hmem hun LH hLH⟩

end WaveTurbulence.Flower.CapsComp
