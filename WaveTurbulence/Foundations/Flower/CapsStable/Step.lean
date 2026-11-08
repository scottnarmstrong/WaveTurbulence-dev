/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.CapsStable.Labels
public import WaveTurbulence.Foundations.Flower.CapsStable.Layer
public import WaveTurbulence.Foundations.Flower.MkMark.Batch

/-! # CAPS-STABLE: one LF operation at a Π₀-unmarked member

`construction_labels`: an LF construction at a source whose non-upper atoms are Π₀-unmarked (no vertex of
`Π₀ = protI0` in their near regions) carries `CompLabels` to its output. The count hypothesis of
`compLabels_step` comes from the dichotomy of `Geo.lean` (a Π₀ vertex lies above all of the replaced region or above
none of it) with `count_full`/`count_free`.

`op_famUnm`: the operation keeps every family member Π₀-unmarked (B2b's `markedBranch_transport`, branch by branch,
with the family's atoms and upper joints carried by `chosenBranchEquiv`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkMark WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links
  WaveTurbulence.Flower.CapsComp

namespace WaveTurbulence.Flower.CapsStable

variable {w : ℕ}

/-- Every family member is Π₀-unmarked at its non-upper atoms. -/
def FamUnm (J : Finset (Fin w)) (pat : Fin w → FixPat) (tt ss : ℝ) {ι : Type*} (A : FamilyReconstruction w ι) :
    Prop :=
  ∀ j, ∀ b ∈ A.family.atoms j, b ≠ A.family.upper j →
    ¬ MarkedBranch A.skeleton A.data.tree (protI0 A.layered J pat tt ss) b

section Choice
variable {S : Garden w} (hS : S.IsPlain) (P : CorePlacement S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)
  (hsame : (S.pair P.retained).1.1 = P.lower.1.1)

theorem choice_nearRel (ε : Bool) :
    ∀ o, o ∉ (choiceCoord hS P D X Q hX hQ hsame ε).Rsk → ∀ b, NearRel S o b ↔
      NearRel (chosenSkeleton S P ε) ((choiceCoord hS P D X Q hX hQ hsame ε).ν o) (chosenBranchEquiv S P ε b) := by
  cases ε
  · intro o _ b; exact Iff.rfl
  · exact twist_nearRel hS P D X Q hX hQ hsame

end Choice

theorem nextFamily_atoms' {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (ε : Bool) (j : ι) :
    (A.nextFamily i ε).atoms j = (A.family.atoms j).image (chosenBranchEquiv A.skeleton (A.family.placement i) ε) := by
  rw [nextFamily_atoms]
  cases ε <;> rfl

theorem nextFamily_upper {ι : Type*} (A : FamilyReconstruction w ι) (i : ι) (ε : Bool) (j : ι) :
    (A.nextFamily i ε).upper j = chosenBranchEquiv A.skeleton (A.family.placement i) ε (A.family.upper j) := by
  cases ε <;> rfl

section Construction
variable {p : ℕ} {kind : Bool} {LG : LayeredGarden w} (src : LFSource p kind LG) {ε : Bool}
  (h : LFConstruction src ε) {J : Finset (Fin w)} {pat : Fin w → FixPat} (tt ss : ℝ)

theorem src_hsame : (src.skeleton.pair src.placement.retained).1.1 = src.placement.lower.1.1 :=
  pair_retained_tree src.placement src.core src.selected

/-- Π₀ avoids the replaced region when the lower joint is unmarked. -/
theorem src_noProt (hU : ∀ c ∈ src.support, c ≠ src.upper →
      ¬ MarkedBranch src.skeleton src.data.tree (protI0 LG J pat tt ss) c) :
    NoProtIn LG J pat (stepIso src h (src_hsame src)).R := by
  rw [stepIso_R]
  refine noProt_of_near src.plain src.placement src.data src.decodes tt ss fun a ha hna => ?_
  exact hU _ src.core.1.1.2.2.1 (fun e => src.core.1.1.2.2.2.1 e.symm) ⟨a, ha, hna⟩

variable {Ntr : ℕ} {kd : FlowerKind} {matchOK : Fin w → Fin w → Prop}

/-- **One LF construction at a Π₀-unmarked member keeps the labels.** -/
theorem construction_labels (hU : ∀ c ∈ src.support, c ≠ src.upper →
      ¬ MarkedBranch src.skeleton src.data.tree (protI0 LG J pat tt ss) c)
    (hL : CompLabels p Ntr kd J matchOK pat LG) : CompLabels p Ntr kd J matchOK pat h.output := by
  have hsame := src_hsame src
  have hTR : (stepIso src h hsame).R = ownedBy src.skeleton src.data.tree (replacedNodes src.placement) :=
    stepIso_R src h hsame
  have hp := src_noProt src h tt ss hU
  refine compLabels_step (stepIso src h hsame) hp
    (fun a => Canon.layer_le_of_isCanonGC (isCanonGC_of_canonicalObject h.canonical) a) (fun j => h.topOrder j)
    ?_ hL
  intro z hz z' hz'
  have hzR : z.1 ∉ (stepIso src h hsame).R := fun h' => hp _ h' hz
  have hzR0 : owner src.skeleton src.data.tree z.1 ∉ replacedNodes src.placement := by
    rw [hTR] at hzR; exact hzR
  have hzU : ∀ c ∈ src.support, c ≠ src.upper → owner src.skeleton src.data.tree z.1 ≠ c.toNode := by
    intro c hc hcu he
    apply hU c hc hcu
    refine ⟨z, (mem_protI0_iff_protAt pat tt ss z).mpr hz, ?_⟩
    rw [mem_nearRegion_iff']
    exact Or.inl he
  rcases dichotomy src.data.tree src.placement src.core src.selected hzR0 hzU with ⟨-, hall⟩ | hnone
  · exact count_full (stepIso src h hsame).I (stepIso src h hsame).I' (stepIso src h hsame).hinv
      (stepIso src h hsame).hinv' (stepIso src h hsame).hlay (stepIso src h hsame).hR' p z hzR
      (fun y _ _ hy => (hall y (by rw [← hTR]; exact hy)).2) (h.topOrder _) z' hz'
  · exact count_free (stepIso src h hsame).I (stepIso src h hsame).I' (stepIso src h hsame).hinv
      (stepIso src h hsame).hinv' (stepIso src h hsame).hlay p z hzR
      (fun q _ hq => hnone _ (by rw [← hTR]; exact hq) (addrBelow_addrExt' _ _)) z' hz'

/-- **Marked branches are transported by one LF construction** (at a Π₀-unmarked member). -/
theorem construction_markedBranch (hU : ∀ c ∈ src.support, c ≠ src.upper →
      ¬ MarkedBranch src.skeleton src.data.tree (protI0 LG J pat tt ss) c) (b : GBranch src.skeleton.tree) :
    MarkedBranch src.skeleton src.data.tree (protI0 LG J pat tt ss) b ↔
      MarkedBranch (src.chosen ε) h.data.tree (protI0 h.output J pat tt ss) (chosenBranchEquiv _ _ ε b) := by
  have hsame := src_hsame src
  have hp := src_noProt src h tt ss hU
  obtain ⟨hp', hiff⟩ := prot_transport (stepIso src h hsame).I (stepIso src h hsame).I'
    (stepIso src h hsame).hinv (stepIso src h hsame).hinv' (stepIso src h hsame).hR (stepIso src h hsame).hR' hp
  rw [data_eq_choice src h]
  exact (choiceCoord src.plain src.placement src.data h.newTree h.newCouple h.tree_wf h.couple_wf hsame
    ε).markedBranch_transport src.decodes (decodes_choice src h) tt ss (chosenBranchEquiv _ _ ε)
    (choice_nearRel _ _ _ _ _ _ _ hsame ε) hp hp' hiff b

end Construction

section Op
variable {p : ℕ} {kind : Bool} {ι : Type*} {A : FamilyReconstruction w ι} {i : ι}
  (op : FamilyOperation (p := p) (kind := kind) A i) {J : Finset (Fin w)} {pat : Fin w → FixPat} (tt ss : ℝ)

theorem op_src_unm (hF : FamUnm J pat tt ss A) :
    ∀ c ∈ (A.source i op.canonical op.eligible op.treeCoherent op.coupleCoherent).support,
      c ≠ (A.source i op.canonical op.eligible op.treeCoherent op.coupleCoherent).upper →
      ¬ MarkedBranch A.skeleton A.data.tree (protI0 A.layered J pat tt ss) c :=
  hF i

/-- **One LF operation keeps every member Π₀-unmarked.** -/
theorem op_famUnm (hF : FamUnm J pat tt ss A) : FamUnm J pat tt ss op.output := by
  intro j b' hb' hbu' hm'
  have hb'' : b' ∈ (A.family.atoms j).image (chosenBranchEquiv A.skeleton (A.family.placement i) op.choice) := by
    rw [← nextFamily_atoms']; exact hb'
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hb''
  have hbu : b ≠ A.family.upper j := fun e => hbu' (by
    show _ = (A.nextFamily i op.choice).upper j
    rw [nextFamily_upper, e])
  exact hF j b hb hbu ((construction_markedBranch _ op.construction tt ss (op_src_unm op tt ss hF) b).mpr hm')

variable {Ntr : ℕ} {kd : FlowerKind} {matchOK : Fin w → Fin w → Prop}

/-- **One LF operation keeps the labels.** -/
theorem op_labels (hF : FamUnm J pat tt ss A) (hL : CompLabels p Ntr kd J matchOK pat A.layered) :
    CompLabels p Ntr kd J matchOK pat op.output.layered :=
  construction_labels _ op.construction tt ss (op_src_unm op tt ss hF) hL

end Op

end WaveTurbulence.Flower.CapsStable
