/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBundle
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelBase
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.LevelStep
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

/-- The class sum of a level, with the dynamic parameters explicit. -/
noncomputable def Lvl.classSum (lv : Lvl B) (κ0 : KPar d) (t0 t1 t2 : ℝ) (e f g h : Mom d) : ℂ :=
  ∑ z ∈ canonFinsetK p kind (lv.state B RD hG layer hLayer) lv.c,
    twistedLocalKernel z.1 z.2 κ0.L κ0.γ κ0.δ κ0.F κ0.base t0 t1 t2 e f g h

/-- The region data of the chain region of a level. -/
noncomputable def Lvl.region (lv : Lvl B) : CLRegionData G lv.c.U lv.c.a lv.c.b :=
  clRegionData G lv.c.block lv.c.cl

/-- **One level of TARGET Step 4, nested form**: the class sum of a level is the S-side with the bundle `psiSB` and the lower factor the class
sum of the next level. -/
theorem Lvl.classSum_nested (κ0 : KPar d) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|)
    (hprime : IsPrimeGarden G) (lv : Lvl B) (pstar : lv.ι) (hk : 1 ≤ (lv.e pstar).1.val)
    (hA0 : ∀ j, j ∉ {j | (lv.e j).1.val < (lv.e pstar).1.val} → j ≠ pstar →
      IsEmpty (FamilyOperation (p := p) (kind := kind) (lv.state B RD hG layer hLayer) j))
    (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (lv.split B RD hG layer hLayer pstar hk).RS *
        clLocalZeta (lv.split B RD hG layer hLayer pstar hk).RS *
        ∑' x : ExtS (lv.split B RD hG layer hLayer pstar hk).RS κ0.L κ0.base e f,
          ∫ σ : CLInternalTime (lv.split B RD hG layer hLayer pstar hk).RS,
            psiSB (p := p) (kind := kind) κ0 (lv.state B RD hG layer hLayer) (lv.split B RD hG layer hLayer pstar hk) hprime x.1
              (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ) *
            (lv.next B RD hG layer hLayer pstar hk).classSum (p := p) (kind := kind) B RD hG layer hLayer κ0
              (clLocalClock (lv.split B RD hG layer hLayer pstar hk).RS ![t0, t1, t2] σ
                (lv.split B RD hG layer hLayer pstar hk).sb.b) t1 t2
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).lower.toNode))
              (κ0.base + latticePoint κ0.L (x.1 ((lv.state B RD hG layer hLayer).family.placement pstar).retained.toNode))
              g h := by
  classical
  set A' := lv.state B RD hG layer hLayer with hA'
  set sp := lv.split B RD hG layer hLayer pstar hk with hsp
  let κ : KPar d := { κ0 with t0 := t0, t1 := t1, t2 := t2, e := e, f := f, g := g, h := h }
  have hc : Stage1.OpsCommute p kind w lv.ι := Stage1.opsCommute_all
  have h1 := tildeJ2_canon (p := p) (kind := kind) κ A' sp hprime hA0 hL hF
  have h2 := tildeJ2_bundle (p := p) (kind := kind) κ A' sp hprime hA0 hL hF
  have hKt := Ktil_eq_canon (p := p) (kind := kind) hc (Subtype.val : {j : lv.ι // (lv.e j).1.val < (lv.e pstar).1.val} → lv.ι)
    Subtype.val_injective (fun j => j.2) (fun i hi => ⟨⟨i, hi⟩, rfl⟩) κ hprime sp hA0
  have e1 : lv.classSum (p := p) (kind := kind) B RD hG layer hLayer κ0 t0 t1 t2 e f g h =
      ∑ G ∈ zpFinset p kind pstar _ A' sp hprime, sSumAt κ G.1 G.2 (ktilde (p := p) (kind := kind) κ A' sp hprime G) := h1
  rw [e1, h2]
  congr 1
  refine tsum_congr fun x => integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)
  beta_reduce
  have hp' : IsPrimeGarden A'.skeleton := hprime
  rw [sum_stInt_eq (p := p) (kind := kind) κ A' sp hp' x σ, hKt]
  congr 1

end WaveTurbulence.VineEstS5C
