/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcMom2
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelTop

/-! # P4-W2 (session 17): the region data of a block is unique; `(Lvl.top B).region = R`

`clRegionData_ext`: two `CLRegionData G U a b` are equal (the slots `kept`, `positive`, `negative` agree for nested blocks with the same lower joint, `region_lower_eq_of_subset`,
and `excluded` is determined by `upper`).  `top_region_eq`: the region of the top level is the region of the chain assembly, so `TermCertW .. (Lvl.top B)` can be proved with the
engine assembly `B` itself (`rw [top_region_eq B]` in the goal).
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree WaveTurbulence.VineEstS5C

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}

theorem clRegionData_ext (R1 R2 : CLRegionData G U a b) : R1 = R2 := by
  obtain ⟨hk, hp, hn⟩ := region_lower_eq_of_subset (Finset.Subset.refl U) R1 R2
  have hex : R1.excluded = R2.excluded := by
    by_contra hne
    have h1 := (R1.upper R2.excluded).mpr (Ne.symm hne)
    have h2 := (R2.upper R2.excluded).mp h1
    exact h2 rfl
  cases R1 with
  | mk s1 pp1 pos1 neg1 d1 ps1 ns1 le1 =>
    cases R2 with
    | mk s2 pp2 pos2 neg2 d2 ps2 ns2 le2 =>
      cases s1; cases s2
      simp only at hk hp hn hex
      subst hk hp hn hex
      rfl

variable {R : CLRegionData G U a b} {n : ℕ}

theorem top_region_eq (B : CLChainAssembly G R n) : (Lvl.top B).region = R := clRegionData_ext _ _

end WaveTurbulence.VineEstS5C.P4.W2
