/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistFiniteFamily

/-! # Extensionality and reverse branch transport for source twist families -/

public section
namespace WaveTurbulence.Twist
open TTree

/-- A placement is determined by its three actual data fields. -/
theorem CorePlacement.ext_data {w : ℕ} {G : Garden w} {P Q : CorePlacement G}
    (hb : P.lower = Q.lower) (hl : P.retained = Q.retained) (hk : P.keep = Q.keep) : P = Q := by
  cases P
  cases Q
  cases hb
  cases hl
  cases hk
  rfl

/-- A source core family is determined by its actual combinatorial data. -/
theorem CoreFamily.ext_data {w : ℕ} {G : Garden w} {ι : Type*} {F H : CoreFamily G ι}
    (hx : F.kind = H.kind) (hs : F.atoms = H.atoms) (ha : F.upper = H.upper)
    (hp : F.placement = H.placement) : F = H := by
  cases F
  cases H
  cases hx
  cases hs
  cases ha
  cases hp
  rfl

/-- The reverse actual branch bijection restores every branch address. -/
theorem coreBranchEquiv_twice_val {w : ℕ} (G : Garden w) (P : CorePlacement G) (b : GBranch G.tree) :
    (coreBranchEquiv (unitTwistGarden G P) (reversePlacement G P) (coreBranchEquiv G P b)).1 = b.1 := by
  rw [coreBranchEquiv_address (unitTwistGarden G P) (reversePlacement G P) (coreBranchEquiv G P b)]
  change exchangeAddress (coreBranchEquiv G P P.lower).1
    ((unitTwistGarden G P).pair (coreLeafEquiv G P P.retained)).1 P.keep (coreBranchEquiv G P b).1 = b.1
  rw [unitTwistGarden_pair,coreBranchEquiv_lower_val,coreLeafEquiv_paired_val,coreBranchEquiv_address]
  by_cases hd : b.1.1 = P.lower.1.1 ∧ P.lower.1.2 <+: b.1.2
  · obtain ⟨q,hq⟩ := hd.2
    have hv : b.1 = (P.lower.1.1,P.lower.1.2 ++ q) := Prod.ext hd.1 hq.symm
    rw [hv]
    simp [exchangeAddress,switchPath_involutive P.keep q]
  · have hp : ¬ (b.1.1 = (G.pair P.retained).1.1 ∧ (G.pair P.retained).1.2 <+: b.1.2) := by
      rintro ⟨hi,hpre⟩
      exact leaf_not_prefix_branch (G.pair P.retained).2 (hi ▸ b.2) hpre
    have he : b.1 ≠ (G.pair P.retained).1 := branch_ne_paired_address G P b
    have hb : b.1 ≠ P.lower.1 := fun he => hd ⟨congrArg Prod.fst he,by rw [he]⟩
    simp only [exchangeAddress,hd,hp,he,hb,ite_false]

/-- A garden together with the transported source family. -/
abbrev FamilyState (w : ℕ) (ι : Type*) := Σ G : Garden w, CoreFamily G ι

/-- Perform a source unit twist, carrying the proved source family along. -/
@[expose] noncomputable def familyStep {w : ℕ} {ι : Type*} (i : ι) (s : FamilyState w ι) : FamilyState w ι :=
  ⟨unitTwistGarden s.1 (s.2.placement i),s.2.twist i⟩

/-- Raw actual addresses suffice for equality of two transported family states. -/
theorem familyState_ext {w : ℕ} {ι : Type*} {s t : FamilyState w ι} (hg : s.1 = t.1)
    (hx : s.2.kind = t.2.kind)
    (hs : ∀ i, (s.2.atoms i).image Subtype.val = (t.2.atoms i).image Subtype.val)
    (ha : ∀ i, (s.2.upper i).1 = (t.2.upper i).1)
    (hb : ∀ i, (s.2.placement i).lower.1 = (t.2.placement i).lower.1)
    (hl : ∀ i, (s.2.placement i).retained.1 = (t.2.placement i).retained.1)
    (hk : ∀ i, (s.2.placement i).keep = (t.2.placement i).keep) : s = t := by
  cases s with | mk G F =>
    cases t with | mk H K =>
      dsimp only at hg hx hs ha hb hl hk
      cases hg
      have hS : F.atoms = K.atoms := funext (fun i => Finset.image_injective Subtype.val_injective (hs i))
      have hA : F.upper = K.upper := funext (fun i => Subtype.ext (ha i))
      have hP : F.placement = K.placement := funext (fun i =>
        CorePlacement.ext_data (Subtype.ext (hb i)) (Subtype.ext (hl i)) (hk i))
      exact congrArg (Sigma.mk G) (CoreFamily.ext_data hx hS hA hP)

end WaveTurbulence.Twist
