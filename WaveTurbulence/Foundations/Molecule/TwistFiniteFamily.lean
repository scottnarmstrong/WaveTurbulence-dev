/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistPairCommutation

/-! # Finite families of source core CL vines

TARGET Definition twist. This keeps only the core members of the source
collection. The source common-joint condition implies the at-most-one
common atom condition used here. No invariance is included as input data.
-/

public section
namespace WaveTurbulence.Twist
open TTree

/-- A source collection of designated core CL vines. -/
structure CoreFamily {w : ℕ} (G : Garden w) (ι : Type*) where
  kind : ι → VineType
  atoms : ι → Finset (GBranch G.tree)
  upper : ι → GBranch G.tree
  placement : ι → CorePlacement G
  core : ∀ i, IsCoreCLVine G (kind i) (atoms i) (upper i) (placement i).lower
  designated : ∀ i, IsPlacementAt G (atoms i) (placement i).lower (placement i)
  separated : ∀ i j, i ≠ j → SeparatedGroups (atoms i) (atoms j)

variable {w : ℕ} {G : Garden w} {ι : Type*}

/-- Two distinct source family members supply the proved pair commutation data. -/
@[expose] def CoreFamily.pairData (F : CoreFamily G ι) (i j : ι) (hij : i ≠ j) :
    CorePairData G (F.placement i) (F.placement j) where
  left := F.atoms i
  right := F.atoms j
  upperLeft := F.upper i
  upperRight := F.upper j
  blockLeft := (F.core i).1.1
  clLeft := (F.core i).2.1
  atLeft := F.designated i
  blockRight := (F.core j).1.1
  clRight := (F.core j).2.1
  atRight := F.designated j
  separated := F.separated i j hij

/-- Distinct source members have distinct lower joints. -/
theorem CoreFamily.lower_injective (F : CoreFamily G ι) : Function.Injective (fun i => (F.placement i).lower) := by
  intro i j he
  by_contra hij
  exact (F.pairData i j hij).lower_ne he

/-- The actual placement after twisting one member, including the reverse placement at that member. -/
@[expose] noncomputable def CoreFamily.nextPlacement (F : CoreFamily G ι) (i j : ι) :
    CorePlacement (unitTwistGarden G (F.placement i)) := by
  classical
  exact if h : j = i then reversePlacement G (F.placement i) else (F.pairData i j (Ne.symm h)).next

/-- Every lower atom follows the same actual branch bijection. -/
theorem CoreFamily.nextPlacement_lower (F : CoreFamily G ι) (i j : ι) :
    (F.nextPlacement i j).lower = coreBranchEquiv G (F.placement i) (F.placement j).lower := by
  classical
  by_cases h : j = i
  · subst j
    simp only [nextPlacement,dite_eq_left rfl,reversePlacement]
    all_goals rfl
  · simp only [nextPlacement,dite_eq_right h,CorePairData.next,otherPlacement]
    all_goals rfl

/-- Every designated retained leaf follows the same actual leaf bijection. -/
theorem CoreFamily.nextPlacement_retained (F : CoreFamily G ι) (i j : ι) :
    (F.nextPlacement i j).retained = coreLeafEquiv G (F.placement i) (F.placement j).retained := by
  classical
  by_cases h : j = i
  · subst j
    simp only [nextPlacement,dite_eq_left rfl,reversePlacement]
    all_goals rfl
  · simp only [nextPlacement,dite_eq_right h,CorePairData.next,otherPlacement]
    all_goals rfl

/-- Every designated outer slot has the same code after a family twist. -/
theorem CoreFamily.nextPlacement_keep (F : CoreFamily G ι) (i j : ι) :
    (F.nextPlacement i j).keep = (F.placement j).keep := by
  classical
  by_cases h : j = i
  · subst j
    simp only [nextPlacement,dite_eq_left rfl,reversePlacement]
  · simp only [nextPlacement,dite_eq_right h,CorePairData.next,otherPlacement]

/-- Separation is preserved by the actual injective branch transport. -/
theorem separatedGroups_twisted {P : CorePlacement G} {S T : Finset (GBranch G.tree)}
    (h : SeparatedGroups S T) : SeparatedGroups (twistedAtoms G P S) (twistedAtoms G P T) := by
  intro x hx ht y hy hu
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
  have hat := (mem_twistedAtoms G P T a).mp ht
  have hbt := (mem_twistedAtoms G P T b).mp hu
  exact congrArg (coreBranchEquiv G P) (h a ha hat b hb hbt)

/-- Performing an actual unit twist transports the entire source family. -/
@[expose] noncomputable def CoreFamily.twist (F : CoreFamily G ι) (i : ι) :
    CoreFamily (unitTwistGarden G (F.placement i)) ι where
  kind := F.kind
  atoms j := twistedAtoms G (F.placement i) (F.atoms j)
  upper j := coreBranchEquiv G (F.placement i) (F.upper j)
  placement := F.nextPlacement i
  core j := by
    classical
    by_cases h : j = i
    · subst j
      have hc := isCoreCLVine_twistedAtoms G (F.placement i) (F.core i) (F.designated i)
      exact (F.nextPlacement_lower i i).symm ▸ hc
    · have hc := (F.pairData i j (Ne.symm h)).core_preserved (F.core j)
      exact (F.nextPlacement_lower i j).symm ▸ hc
  designated j := by
    classical
    by_cases h : j = i
    · subst j
      have ha := reversePlacement_at_twistedAtoms G (F.placement i) (F.core i).1.1 (F.core i).2.1 (F.designated i)
      have he : F.nextPlacement i i = reversePlacement G (F.placement i) := by
        unfold nextPlacement
        exact dite_eq_left rfl
      exact he.symm ▸ ha
    · have ha := otherPlacement_at G (F.placement i) (F.placement j)
        (F.core i).1.1 (F.core i).2.1 (F.designated i) (F.core j).1.1 (F.core j).2.1 (F.designated j) (F.separated i j (Ne.symm h))
      have he : F.nextPlacement i j = (F.pairData i j (Ne.symm h)).next := by
        unfold nextPlacement
        exact dite_eq_right h
      exact he.symm ▸ ha
  separated j k hjk := separatedGroups_twisted (F.separated j k hjk)

end WaveTurbulence.Twist
