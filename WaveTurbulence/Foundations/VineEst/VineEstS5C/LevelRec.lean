/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBundle
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBase
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Sp19Canon

/-! # The levels of the induction over the core vines (V5 Step 4d part C, WP-I)

`Lvl B`: a set of core members (those of piece index `< k0`, carried by an injection `e` into the core indices of the assembly) with the chain
region of the pieces `< k0`; `Lvl.state` the restricted start state; `Lvl.split` the split at a member of piece index `k ≥ 1`
(`mkSplitAt`); `Lvl.next` the level below.  `Lvl.classSum`: the class sum of a level.  `Lvl.classSum_nested`: one level of TARGET Step 4:
the class sum is the S-side with the bundle `psiSB` and the lower factor the class sum of the next level
(`tildeJ2_canon`, `tildeJ2_bundle`, `sum_stInt_eq`, `Ktil_eq_canon`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree MeasureTheory

variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}

/-- A level of the induction over the core vines: a set of core members (those of piece index `< k0`), and the chain region of the
pieces `< k0`. -/
structure Lvl (B : CLChainAssembly G R n) where
  ι : Type
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  e : ι → (assemblySourceFamily B).CoreIndex
  he : Function.Injective e
  k0 : ℕ
  hk0 : k0 ≤ n
  hmem : ∀ j, (e j).1.val < k0
  hsurj : ∀ i : (assemblySourceFamily B).CoreIndex, i.1.val < k0 → ∃ j, e j = i
  c : ChainAt G (restrictFamily (assemblySourceFamily B).coreFamily e he)
  hcU : c.U = iregion B 0 k0
  hca : c.a = jointAt B k0
  hcb : c.b = b

attribute [instance] Lvl.fin Lvl.dec

variable (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
  (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer)

/-- The state of a level. -/
noncomputable def Lvl.state (lv : Lvl B) : FamilyReconstruction w lv.ι :=
  restrictState (startState B RD hG layer hLayer) lv.e lv.he

/-- The split of a level at a member of piece index `k ≥ 1`. -/
noncomputable def Lvl.split (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) :
    SplitAt (lv.state B RD hG layer hLayer).skeleton (lv.state B RD hG layer hLayer).family pstar
      {j | (lv.e j).1.val < (lv.e pstar).1.val} :=
  mkSplitAt B lv.e lv.he (lv.e pstar).1.val lv.k0 hk (lv.hmem pstar) lv.hk0 pstar rfl lv.c lv.hcU lv.hca lv.hcb

/-- The next (lower) level below the member `pstar`. -/
noncomputable def Lvl.next (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val) : Lvl B where
  ι := {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val}
  fin := inferInstance
  dec := inferInstance
  e := fun j => lv.e j.1
  he := fun j1 j2 h => Subtype.ext (lv.he h)
  k0 := (lv.e pstar).1.val
  hk0 := (lv.hmem pstar).le.trans lv.hk0
  hmem := fun j => j.2
  hsurj := fun i hi => by
    obtain ⟨j, hj⟩ := lv.hsurj i (hi.trans (lv.hmem pstar))
    exact ⟨⟨j, hj ▸ hi⟩, hj⟩
  c := chainOfSplit (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk)
    (Subtype.val : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} → lv.ι) Subtype.val_injective (fun j => j.2)
  hcU := rfl
  hca := rfl
  hcb := rfl


variable {d : ℕ} {p : ℕ}

/-- The region data of the chain region of a level. -/
noncomputable def Lvl.region (lv : Lvl B) : CLRegionData G lv.c.U lv.c.a lv.c.b :=
  clRegionData G lv.c.block lv.c.cl

end WaveTurbulence.VineEstS5C
