/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CapsStable.Path
public import WaveTurbulence.Foundations.Flower.CapsComp.Classes
public import WaveTurbulence.Foundations.Flower.FlSep.Sep

/-! # CAPS-STABLE: the capped component labels across one layered correspondence

`compLabels_step`: let `T : StepIso LG LG'` be a layered correspondence off good regions (B2b's `OutIso` pair with
the layer transport), and let the protected set `Π₀(LG)` avoid the region `R`. If the outputs' layers are at most
`p`, the top orders agree, and the layer-`p` counts below `Π₀` vertices are transported, then the labels
`CompLabels` (caps are leaves; caps paired by `matchOK`; per original tree: capped stem in layer `p`, kind counts,
pattern clauses) pass from `LG` to `LG'`. Every vertex the labels read is in `Π₀` (o75 Lemma 2 (b), (c), (e)):
* caps are roots of cap trees, never in a region;
* capped flowers are children of seeds; the stem layer follows from the flower's layer (T2298: stem nodes are
  ancestors of the flower, layers are monotone and at most `p`);
* root children, flower siblings, the flower parent and the pattern pins are seeds or their neighbours. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Links WaveTurbulence.Flower.CapsComp

namespace WaveTurbulence.Flower.CapsStable

variable {w : ℕ}

theorem eq_leaf_of_nil_mem_leaves {t : TTree} (h : ([] : TTree.Path) ∈ t.leaves) : t = TTree.leaf := by
  cases t with
  | leaf => rfl
  | node l m r => simp [TTree.leaves, TTree.pre] at h

/-! ## Protected vertices on addresses -/

section Prot
variable {L : LayeredGarden w} {J : Finset (Fin w)} {pat : Fin w → FixPat}

theorem isCapFlower_iff (ℓ : GLeaf L.garden.tree) : IsCapFlower L J ℓ ↔ CapFlowerAt L J ℓ.1 :=
  ⟨fun h => ⟨ℓ.2, h.1, h.2⟩, fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩⟩

theorem isCapFlowerNode_iff (a : GNode L.garden.tree) : IsCapFlowerNode L J a ↔ CapFlowerAt L J a.1 := by
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact (isCapFlower_iff ℓ).mp hℓ
  · rintro ⟨h, h1, h2⟩
    exact ⟨⟨a.1, h⟩, ⟨h1, h2⟩, rfl⟩

theorem protAt_child_seed {σ : Address w} (hs : SeedAt L J pat σ) {k : Fin 3} (hn : NodeAt L (addrExt σ [k])) :
    ProtAt L J pat (addrExt σ [k]) :=
  ⟨hn, σ, nearAt_child_parent σ k, hs⟩

theorem protAt_parent_seed {y : Address w} {k : Fin 3} (hs : SeedAt L J pat (addrExt y [k])) (hn : NodeAt L y) :
    ProtAt L J pat y :=
  ⟨hn, _, nearAt_parent_child y k, hs⟩

theorem rootSeed {i : Fin w} (hi : i ∉ J) : SeedAt L J pat (i, []) :=
  ⟨TTree.nil_mem_nodes _, Or.inl ⟨hi, rfl⟩⟩

theorem protAt_capParent {z : Address w} (h : CapParentAt L J z) : ProtAt L J pat z :=
  seed_protAt (capParent_seed h)

/-- A capped flower is protected (it is a non-cap root, or a child of its pinned parent). -/
theorem protAt_capFlower {z : Address w} (hc : CapFlowerAt L J z) : ProtAt L J pat z := by
  have hn : NodeAt L z := nodeAt_of_leafAt hc.1
  by_cases hz0 : z.2 = []
  · exact seed_protAt ⟨hn, Or.inl ⟨hc.2.1, hz0⟩⟩
  · have hz := addrExt_parent hz0
    have hcp : CapParentAt L J (z.1, z.2.dropLast) :=
      ⟨branchAt_of_child (i := z.2.getLast hz0) (by rw [← hz]; exact hn), z.2.getLast hz0, by rw [← hz]; exact hc⟩
    rw [hz]
    exact protAt_child_seed (capParent_seed hcp) (by rw [← hz]; exact hn)

end Prot

/-! ## The label transport -/

section Step
variable {LG LG' : LayeredGarden w} (T : StepIso LG LG') {J : Finset (Fin w)} {pat : Fin w → FixPat}

/-- Pulling back a protected vertex of the output. -/
theorem back_prot (hp : NoProtIn LG J pat T.R) {z' : Address w} (hz' : ProtAt LG' J pat z') :
    z' ∉ T.R' ∧ NodeAt LG (T.I'.f z') ∧ T.I'.f z' ∉ T.R ∧ T.I.f (T.I'.f z') = z' ∧ ProtAt LG J pat (T.I'.f z') := by
  obtain ⟨hp', hiff⟩ := prot_transport T.I T.I' T.hinv T.hinv' T.hR T.hR' hp
  have hR' : z' ∉ T.R' := fun h => hp' _ h hz'
  obtain ⟨hn, hR⟩ := T.I'.node z' hz'.1 hR'
  have e := T.hinv z' hz'.1 hR'
  exact ⟨hR', hn, hR, e, (hiff _ hn hR).mp (by rw [e]; exact hz')⟩

theorem fwd_branchAt {b : GBranch LG.garden.tree} (hR : b.1 ∉ T.R) : BranchAt LG' (T.I.f b.1) :=
  (T.I.branch (nodeAt_of_branchAt b.2) hR).mpr b.2

theorem back_branchAt {b' : GBranch LG'.garden.tree} (hR : b'.1 ∉ T.R') : BranchAt LG (T.I'.f b'.1) :=
  (T.I'.branch (nodeAt_of_branchAt b'.2) hR).mpr b'.2

theorem layer_fwd {z : Address w} (hn : NodeAt LG z) (hR : z ∉ T.R) (hn' : NodeAt LG' (T.I.f z)) :
    LG'.layer ⟨T.I.f z, hn'⟩ = LG.layer ⟨z, hn⟩ :=
  ((layerAt_node LG' ⟨T.I.f z, hn'⟩).symm.trans (T.hlay z hn hR)).trans (layerAt_node LG ⟨z, hn⟩)

/-- A root is fixed. -/
theorem fwd_root (i : Fin w) : T.I.f (i, []) = (i, []) := by
  have hn : NodeAt LG (i, []) := TTree.nil_mem_nodes _
  have hR : (i, ([] : TTree.Path)) ∉ T.R := fun h => T.hR.root _ h hn rfl
  exact Prod.ext (T.I.tree _ hn hR) ((T.I.root _ hn hR).mpr rfl)

theorem back_root (i : Fin w) : T.I'.f (i, []) = (i, []) := by
  have hn : NodeAt LG' (i, []) := TTree.nil_mem_nodes _
  have hR : (i, ([] : TTree.Path)) ∉ T.R' := fun h => T.hR'.root _ h hn rfl
  exact Prod.ext (T.I'.tree _ hn hR) ((T.I'.root _ hn hR).mpr rfl)

variable {p Ntr : ℕ} {kind : FlowerKind} {matchOK : Fin w → Fin w → Prop}

/-- **The labels pass along one layered correspondence.** -/
theorem compLabels_step (hp : NoProtIn LG J pat T.R) (hcan : ∀ a : GNode LG'.garden.tree, LG'.layer a ≤ p)
    (htop : ∀ j, LG'.topOrder p j = LG.topOrder p j)
    (hcount : ∀ z : GNode LG.garden.tree, ProtAt LG J pat z.1 → ∀ z' : GNode LG'.garden.tree,
      z'.1 = T.I.f z.1 → LG'.topCountBelow p z' = LG.topCountBelow p z)
    (hL : CompLabels p Ntr kind J matchOK pat LG) : CompLabels p Ntr kind J matchOK pat LG' := by
  obtain ⟨hcap, hmatch, htree⟩ := hL
  obtain ⟨hp', hiff⟩ := prot_transport T.I T.I' T.hinv T.hinv' T.hR T.hR' hp
  have hcap' : ∀ i ∈ J, LG'.garden.tree i = TTree.leaf := by
    intro i hi
    have hn' : NodeAt LG' (i, []) := TTree.nil_mem_nodes _
    have hR' : (i, ([] : TTree.Path)) ∉ T.R' := fun h => T.hR'.root _ h hn' rfl
    have hl : LeafAt LG (T.I'.f (i, [])) := by
      rw [back_root T i]
      show [] ∈ (LG.garden.tree i).leaves
      rw [hcap i hi]
      simp [TTree.leaves]
    exact eq_leaf_of_nil_mem_leaves ((T.I'.leaf _ hn' hR').mp hl)
  refine ⟨hcap', ?_, ?_⟩
  · -- caps are paired by `matchOK`
    intro ℓ hℓ
    have h0 : ℓ.1.2 = [] := by
      have h := ℓ.2
      rw [hcap' _ hℓ] at h
      simpa [TTree.leaves] using h
    have hR' : ℓ.1 ∉ T.R' := fun h => T.hR'.root _ h (nodeAt_of_leafAt ℓ.2) h0
    have hl : LeafAt LG (T.I'.f ℓ.1) := (T.I'.leaf _ (nodeAt_of_leafAt ℓ.2) hR').mpr ℓ.2
    have ht := T.I'.tree _ (nodeAt_of_leafAt ℓ.2) hR'
    have hpt := T.I'.pairTree ℓ.1 ℓ.2 hl hR'
    have hm := hmatch ⟨T.I'.f ℓ.1, hl⟩ (by show (T.I'.f ℓ.1).1 ∈ J; rw [ht]; exact hℓ)
    have e : (LG'.garden.pair ℓ).1.1 = (LG.garden.pair ⟨T.I'.f ℓ.1, hl⟩).1.1 := hpt.symm
    rw [e]
    have ht' : (⟨T.I'.f ℓ.1, hl⟩ : GLeaf LG.garden.tree).1.1 = ℓ.1.1 := ht
    rw [← ht']
    exact hm
  · intro i hi
    obtain ⟨hstem, hkind, hpat⟩ := htree i hi
    refine ⟨?_, ?_, ?_⟩
    · -- the capped stem lies in layer `p`
      rintro a' ha' ⟨ℓ', hfl', hdesc⟩
      have hcf' : CapFlowerAt LG' J ℓ'.1 := (isCapFlower_iff ℓ').mp hfl'
      obtain ⟨_, hzn, hzR, e, -⟩ := back_prot T hp (protAt_capFlower (pat := pat) hcf')
      have hcf : CapFlowerAt LG J (T.I'.f ℓ'.1) := (T.I.capFlower hzn hzR).mp (by rw [e]; exact hcf')
      let ℓ : GLeaf LG.garden.tree := ⟨T.I'.f ℓ'.1, hcf.1⟩
      have hti : ℓ.1.1 = i := by
        show (T.I'.f ℓ'.1).1 = i
        rw [T.I'.tree _ (nodeAt_of_leafAt ℓ'.2) (fun h => hp' _ h (protAt_capFlower (pat := pat) hcf'))]
        exact hdesc.1.symm.trans ha'
      have hlay : LG.layer ℓ.toNode = p :=
        hstem ℓ.toNode hti ⟨ℓ, (isCapFlower_iff ℓ).mpr hcf, ⟨rfl, List.prefix_refl _⟩⟩
      have hlay' : LG'.layer ℓ'.toNode = p := by
        have h1 := T.hlay _ hzn hzR
        rw [e] at h1
        rw [← hlay, ← layerAt_node LG' ℓ'.toNode, ← layerAt_node LG ℓ.toNode]
        exact h1
      have h2 := FlSep.layer_le_of_isDesc LG' hdesc
      have h3 := hcan a'
      omega
    · -- the kind counts
      cases kind with
      | X =>
        obtain ⟨h1, h2⟩ := hkind
        exact ⟨by rw [htop]; exact h1, by rw [htop]; exact h2⟩
      | Y =>
        obtain ⟨hlt, hch⟩ := hkind
        refine ⟨by rw [htop]; exact hlt, fun b' hb' k => ?_⟩
        have hs' : SeedAt LG' J pat b'.1 := by rw [hb']; exact rootSeed hi
        have hpr' : ProtAt LG' J pat (b'.child k).1 := protAt_child_seed hs' (b'.child k).2
        obtain ⟨hcR', hzn, hzR, e, hpr⟩ := back_prot T hp hpr'
        have hbR' : b'.1 ∉ T.R' := fun h => hp' _ h (seed_protAt hs')
        let b : GBranch LG.garden.tree := ⟨T.I'.f b'.1, back_branchAt T hbR'⟩
        have hb : b.1 = (i, []) := by show T.I'.f b'.1 = _; rw [hb', back_root]
        have hc : T.I'.f (b'.child k).1 = (b.child k).1 :=
          T.I'.child b'.1 k (nodeAt_of_branchAt b'.2) hbR' (b'.child k).2 hcR'
        have := hcount (b.child k) (by rw [← hc]; exact hpr) (b'.child k) (by rw [← hc, e])
        rw [this]
        exact hch b hb k
      | W =>
        obtain ⟨hlt, hcp⟩ := hkind
        refine ⟨by rw [htop]; exact hlt, fun b' hb'i hb'cp => ?_⟩
        have hcpa' : CapParentAt LG' J b'.1 := (isCapFlowerParent_iff b').mp hb'cp
        have hpb' : ProtAt LG' J pat b'.1 := protAt_capParent hcpa'
        obtain ⟨hbR', hbn, hbR, eb, hpb⟩ := back_prot T hp hpb'
        let b : GBranch LG.garden.tree := ⟨T.I'.f b'.1, back_branchAt T hbR'⟩
        have hcpa : CapParentAt LG J b.1 := (T.I.capParent T.hR T.hR' hbn hbR).mp (by rw [eb]; exact hcpa')
        have hbi : b.1.1 = i := by
          show (T.I'.f b'.1).1 = i
          rw [T.I'.tree _ (nodeAt_of_branchAt b'.2) hbR']; exact hb'i
        obtain ⟨hch, hcnt⟩ := hcp b hbi ((isCapFlowerParent_iff b).mpr hcpa)
        refine ⟨fun k hk' => ?_, ?_⟩
        · have hpr' : ProtAt LG' J pat (b'.child k).1 :=
            protAt_child_seed (capParent_seed hcpa') (b'.child k).2
          obtain ⟨hcR', hzn, hzR, e, hpr⟩ := back_prot T hp hpr'
          have hc : T.I'.f (b'.child k).1 = (b.child k).1 :=
            T.I'.child b'.1 k (nodeAt_of_branchAt b'.2) hbR' (b'.child k).2 hcR'
          have hk : ¬ IsCapFlowerNode LG J (b.child k) := by
            intro hcf
            apply hk'
            rw [isCapFlowerNode_iff] at hcf ⊢
            rw [← hc] at hcf
            have := (T.I.capFlower hzn hzR).mpr hcf
            rwa [e] at this
          have := hcount (b.child k) (by rw [← hc]; exact hpr) (b'.child k) (by rw [← hc, e])
          rw [this]
          exact hch k hk
        · have := hcount b.toNode hpb b'.toNode eb.symm
          rw [this, htop]
          exact hcnt
    · -- the pattern clauses
      revert hpat
      cases pat i with
      | plain => exact fun _ => trivial
      | dRoot =>
        rintro ⟨b, hb, hncp⟩
        have hbR : b.1 ∉ T.R := fun h => T.hR.root _ h (nodeAt_of_branchAt b.2) (by rw [hb])
        refine ⟨⟨T.I.f b.1, fwd_branchAt T hbR⟩, ?_, ?_⟩
        · show T.I.f b.1 = _
          rw [hb, fwd_root]
        · intro hcp'
          exact hncp ((isCapFlowerParent_iff b).mpr
            ((T.I.capParent T.hR T.hR' (nodeAt_of_branchAt b.2) hbR).mp ((isCapFlowerParent_iff _).mp hcp')))
      | dParent =>
        rintro ⟨b, c, hccp, hci, hcb⟩
        have hcpa : CapParentAt LG J c.1 := (isCapFlowerParent_iff c).mp hccp
        obtain ⟨hcbt, k, hck⟩ := hcb
        have hce : c.1 = addrExt b.1 [k] := Prod.ext hcbt hck
        have hcR : c.1 ∉ T.R := fun h => hp _ h (protAt_capParent hcpa)
        have hbR : b.1 ∉ T.R := fun h => hp _ h
          (protAt_parent_seed (k := k) (by rw [← hce]; exact capParent_seed hcpa) (nodeAt_of_branchAt b.2))
        have hfc : T.I.f c.1 = addrExt (T.I.f b.1) [k] := by
          rw [hce]
          exact T.I.child b.1 k (nodeAt_of_branchAt b.2) hbR (by rw [← hce]; exact nodeAt_of_branchAt c.2)
            (by rw [← hce]; exact hcR)
        refine ⟨⟨T.I.f b.1, fwd_branchAt T hbR⟩, ⟨T.I.f c.1, fwd_branchAt T hcR⟩, ?_, ?_, ?_⟩
        · exact (isCapFlowerParent_iff _).mpr ((T.I.capParent T.hR T.hR' (nodeAt_of_branchAt c.2) hcR).mpr hcpa)
        · show (T.I.f c.1).1 = i
          rw [T.I.tree _ (nodeAt_of_branchAt c.2) hcR]; exact hci
        · refine ⟨?_, k, ?_⟩
          · show (T.I.f c.1).1 = (T.I.f b.1).1
            rw [hfc]; rfl
          · show (T.I.f c.1).2 = (T.I.f b.1).2 ++ [k]
            rw [hfc]; rfl
      | dChild k =>
        rintro ⟨b, c, hccp, hci, hbi, hbc, hlay⟩
        have hcpa : CapParentAt LG J c.1 := (isCapFlowerParent_iff c).mp hccp
        have hbe : b.1 = addrExt c.1 [k] := Prod.ext (hbi.trans hci.symm) hbc
        have hcR : c.1 ∉ T.R := fun h => hp _ h (protAt_capParent hcpa)
        have hbR : b.1 ∉ T.R := fun h => hp _ h (by
          rw [hbe]; exact protAt_child_seed (capParent_seed hcpa) (by rw [← hbe]; exact nodeAt_of_branchAt b.2))
        have hfb : T.I.f b.1 = addrExt (T.I.f c.1) [k] := by
          rw [hbe]
          exact T.I.child c.1 k (nodeAt_of_branchAt c.2) hcR (by rw [← hbe]; exact nodeAt_of_branchAt b.2)
            (by rw [← hbe]; exact hbR)
        refine ⟨⟨T.I.f b.1, fwd_branchAt T hbR⟩, ⟨T.I.f c.1, fwd_branchAt T hcR⟩, ?_, ?_, ?_, ?_, ?_⟩
        · exact (isCapFlowerParent_iff _).mpr ((T.I.capParent T.hR T.hR' (nodeAt_of_branchAt c.2) hcR).mpr hcpa)
        · show (T.I.f c.1).1 = i
          rw [T.I.tree _ (nodeAt_of_branchAt c.2) hcR]; exact hci
        · show (T.I.f b.1).1 = i
          rw [T.I.tree _ (nodeAt_of_branchAt b.2) hbR]; exact hbi
        · show (T.I.f b.1).2 = (T.I.f c.1).2 ++ [k]
          rw [hfb]; rfl
        · rw [← hlay]
          exact layer_fwd T (nodeAt_of_branchAt b.2) hbR _

end Step

end WaveTurbulence.Flower.CapsStable
