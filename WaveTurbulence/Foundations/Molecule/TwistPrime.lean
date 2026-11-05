/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.TwistMiniTransport

/-! # The actual unit twist preserves source primeness

TARGET twist: prime iff prime. An embedded mini piece has three bonds
between its branches, whereas the lower block joint has at most two to
any other atom. Every remaining mini piece transports with the same code.
-/

public section
namespace WaveTurbulence.Twist
open TTree Reg.Skeleton
variable {w : ℕ} (G : Garden w) (P : CorePlacement G)

/-- Primeness is invariant whenever the lower atom cannot participate in a triple bond. -/
theorem unitTwist_prime_of_noTriple (hno : NoTripleAt G P.lower) :
    IsPrimeGarden (unitTwistGarden G P) ↔ IsPrimeGarden G := by
  constructor
  · intro hprime
    have hplain : G.IsPlain := by
      have hh := unitTwistGarden_plain (unitTwistGarden G P) (reversePlacement G P) hprime.1
      rw [unitTwistGarden_involutive] at hh
      exact hh
    refine ⟨hplain,?_⟩
    rintro ⟨m⟩
    exact hprime.2 (miniOccurrence_unitTwist G P hplain hno m)
  · intro hprime
    have hplain := unitTwistGarden_plain G P hprime.1
    have hnew := noTripleAt_unitTwist G P hno
    refine ⟨hplain,?_⟩
    rintro ⟨m⟩
    have hm := miniOccurrence_unitTwist (unitTwistGarden G P) (reversePlacement G P) hplain hnew m
    rw [unitTwistGarden_involutive] at hm
    exact hprime.2 hm

/-- The designated unit twist of every source core CL vine is prime iff the original garden is. -/
theorem unitTwist_prime {X : VineType} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
    (hcore : IsCoreCLVine G X S a b) (hP : IsPlacementAt G S b P) :
    IsPrimeGarden (unitTwistGarden G P) ↔ IsPrimeGarden G := by
  apply unitTwist_prime_of_noTriple G P
  intro q hq
  have hb := hP.1
  rw [hb] at hq ⊢
  exact block_joint_no_triple G hcore.1.1 hq

end WaveTurbulence.Twist
