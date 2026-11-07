/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsSb4

/-! # Measurability of the bundle `psiSB` in the clock (V5 Step 4d part C, `hAbs`, leaf `sbm`)

`measurable_spartFrame`: the frame of the S-part is measurable in any measurable family of clocks.  `measurable_rowVal`: the
exceptional factor is measurable given measurable rows.  `measurable_rowQ_comp`/`measurable_rowT_comp`: the exceptional rows of any state
are continuous in the two times.  **`measurable_psiSB`**: `psiSB x` is measurable as a function of the clock.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
variable {kind : Bool}
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS2 WaveTurbulence.LGSpine WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

section Frame
variable {w d : ℕ} {G : Garden w} {S : Finset (GBranch G.tree)} {a b : GBranch G.tree}
  {D : ReconstructionData G} {hG : G.IsPlain} {L γ δ : ℝ} {F : ℕ → Mom d → ℝ}
  {layer : GNode (D.forest hG) → ℕ} {hLayer : IsLayering (D.garden hG) layer} {base : Mom d}
  {α : Type*} [MeasurableSpace α]

theorem measurable_spartFrame (hF : HF D hG L F layer base) (p0 : SourcePair G) (x : GNode G.tree → (Fin d → ℤ))
    (u : α → GBranch G.tree → ℝ) (hu : ∀ v, Measurable fun z => u z v) :
    Measurable fun z => spartFrame D hG L γ δ F layer hLayer base S a b p0 x (u z) := by
  classical
  have hp : ∀ y : GNode G.tree, Measurable fun z => parentClock (u z a) (u z) y := fun y =>
    measurable_parentClock_top (α := α) (fun z => u z a) u (hu a) hu y
  have hset : MeasurableSet {z | DomF (fun v => layer (D.coreBranch hG v).toNode) S a b (u z)} := by
    have : {z | DomF (fun v => layer (D.coreBranch hG v).toNode) S a b (u z)} =
        ⋂ v ∈ S.erase a, {z | ((layer (D.coreBranch hG v).toNode : ℕ) : ℝ) < u z v ∧
          u z v < (layer (D.coreBranch hG v).toNode : ℕ) + 1 ∧ 0 < u z v ∧
          (v ≠ b → u z v < parentClock (u z a) (u z) v.toNode)} := by
      ext z; simp [DomF]
    rw [this]
    refine Finset.measurableSet_biInter _ fun v _ => ?_
    have h4 : MeasurableSet {z | v ≠ b → u z v < parentClock (u z a) (u z) v.toNode} := by
      by_cases hvb : v = b
      · simp [hvb]
      · simp only [ne_eq, hvb, not_false_eq_true, true_implies]
        exact measurableSet_lt (hu v) (hp _)
    simp only [Set.ofPred_and]
    exact (measurableSet_lt measurable_const (hu v)).inter ((measurableSet_lt (hu v) measurable_const).inter
      ((measurableSet_lt measurable_const (hu v)).inter h4))
  have hphase : Measurable fun z => clRegionalPhase G (S.erase b) L γ δ (cosetDecoration G L base x) (u z) := by
    unfold clRegionalPhase
    exact Finset.measurable_prod _ fun v _ =>
      (continuous_phaseAtom L γ δ (G.sign v.toNode) _).measurable.comp (hu v)
  have hq : ∀ p : SourcePair G, Measurable fun z => qRow D hG L γ δ F layer hLayer base (u z a) x (u z) p := fun p =>
    VineEst.measurable_KQsel_comp _ _ _ L γ δ F _ (native_couple_plain D hG layer hLayer p) _
      (couple_hF hF p (x (p.firstLeaf hG).toNode)) (hp _) (hp _)
  have ht : ∀ v : GBranch G.tree, Measurable fun z => tRow D hG L γ δ F layer hLayer base (u z a) x (u z) v := fun v =>
    VineEst.measurable_KTsel_comp _ _ L γ δ F _ (native_chain_paired D hG layer hLayer v) _
      (chain_hF hF v (x v.toNode)) (hp _) (hu v)
  unfold spartFrame
  exact (Measurable.ite hset measurable_const measurable_const).mul (measurable_const.mul (hphase.mul
    ((Finset.measurable_prod _ fun p _ => hq p).mul (Finset.measurable_prod _ fun v _ => ht v))))

end Frame

section Row
variable {d : ℕ} {α : Type*} [MeasurableSpace α]

theorem measurable_rowVal (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ) (Lq M : Mom d)
    (hq : ∀ {f g : α → ℝ}, Measurable f → Measurable g → Measurable fun z => rq (f z) (g z) Lq)
    (ht : ∀ {f g : α → ℝ}, Measurable f → Measurable g → Measurable fun z => rt (f z) (g z) M)
    {t0 p p' : α → ℝ} (h0 : Measurable t0) (h1 : Measurable p) (h2 : Measurable p') :
    Measurable fun z => rowVal ν rq rt (t0 z) (p z) (p' z) Lq M := by
  classical
  unfold rowVal
  have hq' : Measurable fun z => (if ν = 1 then rq (t0 z) (p' z) Lq else rq (p' z) (t0 z) Lq) := by
    by_cases hν : ν = 1
    · simp only [hν, ite_true]; exact hq h0 h2
    · simp only [hν, ite_false]; exact hq h2 h0
  exact (Measurable.ite (measurableSet_lt h0 h1) measurable_const measurable_const).mul (hq'.mul (ht h1 h0))

end Row

section State
variable {w : ℕ} {ι : Type*} {d : ℕ} {α : Type*} [MeasurableSpace α]

theorem measurable_rowQ_comp (κ : KPar d) (G : FamilyReconstruction w ι) (i : ι)
    (k : Mom d)
    (hk : ∀ ℓ ∈ inputLeaves (sigStar G i).2.1.garden, Summable fun n : Fin d → ℤ =>
      |κ.F ((sigStar G i).2.1.layer ℓ.toNode) (k + latticePoint κ.L n)|)
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun z => rowQ κ G i (f z) (g z) k :=
  VineEst.measurable_KQsel_comp _ _ _ κ.L κ.γ κ.δ κ.F _ (native_couple_plain G.data G.plain (stateLayer G) (stateLayer_isLayering G) _) k hk hf hg

theorem measurable_rowT_comp (κ : KPar d) (G : FamilyReconstruction w ι) (i : ι) (k : Mom d)
    (hk : ∀ ℓ ∈ inputLeaves (sigStar G i).2.2.garden, Summable fun n : Fin d → ℤ =>
      |κ.F ((sigStar G i).2.2.layer ℓ.toNode) (k + latticePoint κ.L n)|)
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun z => rowT κ G i (f z) (g z) k :=
  VineEst.measurable_KTsel_comp _ _ κ.L κ.γ κ.δ κ.F _ (native_chain_paired G.data G.plain (stateLayer G) (stateLayer_isLayering G) _) k hk hf hg

end State

section Bundle
variable {w : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ}

theorem measurable_bundleKernel (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
    (tw : Bool) (ν : ℤˣ) (rq rt : ℝ → ℝ → Mom d → ℂ)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    (hq : ∀ n : Fin d → ℤ, ∀ {f g : (GBranch A.skeleton.tree → ℝ) → ℝ}, Measurable f → Measurable g →
      Measurable fun z => rq (f z) (g z) (κ.base + latticePoint κ.L n))
    (hr : ∀ n : Fin d → ℤ, ∀ {f g : (GBranch A.skeleton.tree → ℝ) → ℝ}, Measurable f → Measurable g →
      Measurable fun z => rt (f z) (g z) (κ.base + latticePoint κ.L n))
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) :
    Measurable (bundleKernel κ A sp tw ν rq rt x) := by
  have hu : ∀ v : GBranch A.skeleton.tree, Measurable fun z : GBranch A.skeleton.tree → ℝ => z v :=
    fun v => measurable_pi_apply v
  have hHF := HF_of_all A.data A.plain κ.L κ.F (stateLayer A) κ.base hF
  unfold bundleKernel
  refine (measurable_spartFrame (u := fun z => z) hHF _ x hu).mul ?_
  cases tw
  · exact measurable_rowVal ν rq rt _ _ (hq _) (hr _) (hu _) (hu _) (hu _)
  · exact measurable_rowVal ν rq rt _ _ (hq _) (hr _) (hu _) (hu _) (hu _)

open Classical in
/-- **Measurability of the bundle `psiSB` in the clock.** -/
theorem measurable_psiSB (κ : KPar d) (A : FamilyReconstruction w ι) (sp0 : SplitAt A.skeleton A.family pstar J)
    (hA : IsPrimeGarden A.skeleton)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) :
    Measurable (psiSB (p := p) (kind := kind) κ A sp0 hA x) := by
  unfold psiSB
  have key : ∀ G ∈ zpFinset p kind pstar J A sp0 hA, Measurable fun u => epsOf A pstar G.1 *
      bundleKernel κ A sp0 (decide (twAt A G.1 pstar)) (nuOf G.1 pstar) (rowQ κ G.1 pstar) (rowT κ G.1 pstar) x u := by
    intro G _
    refine measurable_const.mul (measurable_bundleKernel κ A sp0 _ _ _ _ hF ?_ ?_ x)
    · intro n f g hf hg
      exact measurable_rowQ_comp κ G.1 pstar _ (couple_hF (HF_of_all G.1.data G.1.plain κ.L κ.F (stateLayer G.1) κ.base hF) _ n) hf hg
    · intro n f g hf hg
      exact measurable_rowT_comp κ G.1 pstar _ (chain_hF (hLayer := stateLayer_isLayering G.1) (HF_of_all G.1.data G.1.plain κ.L κ.F (stateLayer G.1) κ.base hF) _ n) hf hg
  have := Finset.measurable_sum (zpFinset p kind pstar J A sp0 hA) key
  convert this using 1

end Bundle

end WaveTurbulence.VineEstS5C
