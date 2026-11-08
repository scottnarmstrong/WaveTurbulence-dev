/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.ContMember
public import WaveTurbulence.Foundations.Flower.V5W.Statements

/-! # V5W-0, T5: continuity of the weighted class kernel

Weighted copies of main's `Cont.memberMod_continuousOn`, `Cont.classSumMod_continuousOn` and
`Cont.twistedRecenteredModC_continuousOn` (Cont/ModClass):

* `norm_regionWeightFW_le`: the region multiplier is bounded by `cψ ^ #(region darts)` (`|g| ≤ cψ`, `1 ≤ cψ`; the top
  filter is a `χ₀` value in `[0, 1]`);
* `memberFW_continuousOn`: one member of the class, through `clRecenteredFW_continuousOn` at the member's own state,
  assembly (`Reach.exists_asm`) and row coherence (`Reach.rowCoherent`);
* `weightedClassContinuity : WeightedClassContinuity` (**T5**): the pinned class kernel `twistedRecenteredFW` is
  continuous in the three hinge times on the output cube, for every output, uniformly in the modulation `λ` (R58).
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.VineEstS4 WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.LGSpine VineParamContract TTree
  Reg Reg.Skeleton RegRed MeasureTheory
open WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineC WaveTurbulence.VineSpaceK
  WaveTurbulence.Flower.Stage1W
open scoped ENNReal

section Bound
variable {w d : ℕ} {ι : Type*}

theorem norm_topFilterWeight_le (S : Option ℝ) (q : Fin 4 → Mom d) : ‖topFilterWeight S q‖ ≤ 1 := by
  unfold topFilterWeight
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases S with _ | s
  · simp
  · simp only [Option.elim]
    unfold WaveTurbulence.chi0
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _

/-- **The region multiplier is bounded** by `cψ` per dart of the region. -/
theorem norm_regionWeightFW_le (p : ℕ) (g : Mom d → ℂ) (S : Option ℝ) (L : ℝ) (base : Mom d)
    (X : FamilyReconstruction w ι) (U : Finset (GBranch X.skeleton.tree)) (a : GBranch X.skeleton.tree)
    (cψ : ℝ) (hc : 1 ≤ cψ) (hg : ∀ x, ‖g x‖ ≤ cψ) (x : GNode X.skeleton.tree → Fin d → ℤ) :
    ‖regionWeightFW p g S L base X U a x‖ ≤
      cψ ^ (Finset.univ.filter (X.skeleton.molecule.InGroup U)).card := by
  unfold regionWeightFW
  rw [norm_mul]
  have h1 : ‖∏ y ∈ Finset.univ.filter (X.skeleton.molecule.InGroup U),
      (if nodeRowIncoh X.data X.plain (stateLayer X) (stateLayer_isLayering X) (Mole.dartNode X.skeleton y) = 0 then
        topPsi p g (stateCoreLayer X (X.skeleton.molecule.atom (X.skeleton.molecule.mate y)))
          (stateCoreLayer X (X.skeleton.molecule.atom y))
          (cosetDecoration X.skeleton L base x (Mole.dartNode X.skeleton y))
      else 1)‖ ≤ cψ ^ (Finset.univ.filter (X.skeleton.molecule.InGroup U)).card := by
    rw [norm_prod]
    calc _ ≤ ∏ _y ∈ Finset.univ.filter (X.skeleton.molecule.InGroup U), cψ :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun y _ => by
            split_ifs
            · exact norm_topPsi_le p g cψ hc hg _ _ _
            · simpa using hc)
      _ = _ := Finset.prod_const _
  have h2 : ‖nodeWeight (topFilterWeight S) L base a x‖ ≤ 1 := norm_topFilterWeight_le S _
  calc _ ≤ cψ ^ (Finset.univ.filter (X.skeleton.molecule.InGroup U)).card * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (pow_nonneg (by linarith) _)
    _ = _ := mul_one _

end Bound

variable {w : ℕ} {ι : Type*}

/-- **One member of the class** (weighted copy of `Cont.memberMod_continuousOn`). -/
theorem memberFW_continuousOn {P : WTParams} (lam : ℝ)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (htop : TopIncoherentDecayAtR P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {kind : Bool} {M : List ι} {A Bs : FamilyReconstruction w ι}
    {c : ChainAt A.skeleton A.family} {c' : ChainAt Bs.skeleton Bs.family} (hr : Reach p kind M A c Bs c') {n : ℕ}
    {R0 : CLRegionData A.skeleton c.U c.a c.b} (hM9 : VINEPARAM) (B0 : CLChainAssembly A.skeleton R0 n)
    (lA : GNode (A.data.forest A.plain) → ℕ) (hLA : IsLayering (A.data.garden A.plain) lA) (hlA : stateLayer A = lA)
    (hAlay : ∀ x, lA x ≤ p) (hAord : A.layered.garden.order ≤ P.N (p + 1) ^ 4)
    (bk0 : Fin (assemblyShape hM9 B0).I → Fin 4) (q0 : Fin 3 → ℕ) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (hq0 : q0 0 = lA (A.data.coreBranch A.plain c.a).toNode)
    (hqle1 : (q0 1 : ℝ) ≤ assemblyTimeQ hM9 B0 (fun v => lA (A.data.coreBranch A.plain v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B0⟩, 0⟩))
    (hqle2 : (q0 2 : ℝ) ≤ assemblyTimeQ hM9 B0 (fun v => lA (A.data.coreBranch A.plain v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B0⟩, 0⟩))
    (H : RowCoherent hM9 B0 A.data A.plain lA hLA
      (step3W hM9 B0 A.data A.plain lA hLA bk0 q0 centre wBar) P.L P.γ P.δ h p)
    (g : Mom P.d → ℂ) (cψ : ℝ) (hcψ : 1 ≤ cψ) (hgP : GPresented (32 * P.d) g cψ) (S : Option ℝ) :
    ∀ E ∈ outSet (step3D hM9 B0 A.data A.plain lA hLA bk0 q0 centre wBar) P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => recPhase (A.skeleton.sign c.a.toNode) P.L P.γ P.δ (tt 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 0) (sumintBoundary (A.skeleton.sign c.a.toNode) E 1)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 3) *
        twistedLocalKernelFW p g S Bs c' P.L P.γ P.δ h wBar (modW lam)
          (tt 0) (tt 1) (tt 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 1) (sumintBoundary (A.skeleton.sign c.a.toNode) E 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 3))
        (cubeSet q0) := by
  classical
  subst hlA
  obtain rfl := regionData_subsingleton R0 (clRegionData A.skeleton c.block c.cl)
  obtain ⟨e, B1, hc, ha, hb, hU, hl⟩ := hr.exists_asm B0
  have hlayB : ∀ x, stateLayer Bs x ≤ p := reach_stateLayer_le hr hAlay
  have hI1 := assemblyShape_I_pos hM9 B1
  set bk1 : Fin (assemblyShape hM9 B1).I → Fin 4 := canonBadKind hM9 B1 Bs.data Bs.plain (stateLayer Bs) with hbk1
  have hbad2 : ∀ i, bk1 i ≠ 2 := fun i => by
    rcases canonBadKind_cases hM9 B1 Bs.data Bs.plain (stateLayer Bs) i with h0 | h0 <;> rw [hbk1, h0] <;> decide
  have hq1 : q0 0 = stateLayer Bs (Bs.data.coreBranch Bs.plain c'.a).toNode := by
    rw [hq0, ← ha]
    exact (hl c.a).symm
  have hrc := hr.rowCoherent hM9 B0 B1 bk0 q0 bk1 q0 centre wBar hq0 hq1 P.L P.γ P.δ h H
  have hsz : RowSizes hM9 B1 Bs.data Bs.plain (P.N (p + 1) ^ 4) :=
    rowSizes_of_state hM9 Bs B1 (by rw [hr.order_eq]; exact hAord)
  have hel := fun v => eligible_of hM9 B1 Bs.data Bs.plain (stateLayer Bs) (stateLayer_isLayering Bs)
    (step3W hM9 B1 Bs.data Bs.plain (stateLayer Bs) (stateLayer_isLayering Bs) bk1 q0 centre wBar) rfl hq1 P.L P.γ P.δ
    h (P.N (p + 1) ^ 4) p hlayB hsz hrc v
  have hfirst : assemblyTimeQ hM9 B1 (fun v => stateLayer Bs (Bs.data.coreBranch Bs.plain v).toNode)
        (.inl ⟨⟨0, hI1⟩, 0⟩) =
      assemblyTimeQ hM9 B0 (fun v => stateLayer A (A.data.coreBranch A.plain v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B0⟩, 0⟩) := by
    rw [assemblyTimeQ_first hM9 B1 Bs.data Bs.plain (stateLayer Bs) hI1,
      assemblyTimeQ_first hM9 B0 A.data A.plain (stateLayer A) (assemblyShape_I_pos hM9 B0)]
    have := hl c.b
    rw [hb] at this
    exact_mod_cast this
  have hgn : ∀ x, ‖g x‖ ≤ cψ := fun x => GPresented.norm_le hgP (by linarith) x
  have key := clRecenteredFW_continuousOn lam hgate hinc htop hd hη0 hη6 hη2 hC hδ hL hw hp hB hBpos hM9 B1 Bs.data
    Bs.plain (stateLayer Bs) (stateLayer_isLayering Bs) hlayB q0 hq1 centre wBar bk1 hbad2 hel
    (Or.inr (hfirst ▸ hqle1)) (Or.inr (hfirst ▸ hqle2)) g cψ hcψ hgP
    (regionWeightFW p g S P.L wBar Bs c'.U c'.a) _ (pow_nonneg (by linarith) _)
    (fun z => norm_regionWeightFW_le p g S P.L wBar Bs c'.U c'.a cψ hcψ hgn z)
  intro E hE
  have hsign : Bs.skeleton.sign c'.a.toNode = A.skeleton.sign c.a.toNode := hr.sign_a
  have := key E hE
  rw [hsign] at this
  exact this

/-- The weighted recentered class kernel is the sum of the recentered weighted member kernels. -/
theorem twistedRecenteredFW_eq_sum {d : ℕ} (p : ℕ) (g : Mom d → ℂ) (S : Option ℝ) (G : Garden w)
    (a : GBranch G.tree) (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family))
    (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d) (W : ℝ → ℂ) (t0 t1 t2 : ℝ) (e f g' k : Mom d) :
    twistedRecenteredFW p g S G a Z L γ δ F base W t0 t1 t2 e f g' k =
      ∑ x ∈ Z, recPhase (G.sign a.toNode) L γ δ t0 e f g' k *
        twistedLocalKernelFW p g S x.1 x.2 L γ δ F base W t0 t1 t2 e f g' k := by
  unfold twistedRecenteredFW
  rw [Finset.mul_sum]

/-- **The class level, generic in the member set** (weighted copy of `Cont.classSumMod_continuousOn`). -/
theorem classSumFW_continuousOn {P : WTParams} (lam : ℝ)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (htop : TopIncoherentDecayAtR P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {kind : Bool} {A : FamilyReconstruction w ι} {c : ChainAt A.skeleton A.family} {n : ℕ}
    {R0 : CLRegionData A.skeleton c.U c.a c.b} (hM9 : VINEPARAM) (B0 : CLChainAssembly A.skeleton R0 n)
    (lA : GNode (A.data.forest A.plain) → ℕ) (hLA : IsLayering (A.data.garden A.plain) lA) (hlA : stateLayer A = lA)
    (hAlay : ∀ x, lA x ≤ p) (hAord : A.layered.garden.order ≤ P.N (p + 1) ^ 4)
    (bk0 : Fin (assemblyShape hM9 B0).I → Fin 4) (q0 : Fin 3 → ℕ) (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (hq0 : q0 0 = lA (A.data.coreBranch A.plain c.a).toNode)
    (hqle1 : (q0 1 : ℝ) ≤ assemblyTimeQ hM9 B0 (fun v => lA (A.data.coreBranch A.plain v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B0⟩, 0⟩))
    (hqle2 : (q0 2 : ℝ) ≤ assemblyTimeQ hM9 B0 (fun v => lA (A.data.coreBranch A.plain v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B0⟩, 0⟩))
    (H : RowCoherent hM9 B0 A.data A.plain lA hLA
      (step3W hM9 B0 A.data A.plain lA hLA bk0 q0 centre wBar) P.L P.γ P.δ h p)
    (g : Mom P.d → ℂ) (cψ : ℝ) (hcψ : 1 ≤ cψ) (hgP : GPresented (32 * P.d) g cψ) (S : Option ℝ)
    (Z : Finset (Σ Bs : FamilyReconstruction w ι, ChainAt Bs.skeleton Bs.family))
    (hZ : ∀ x ∈ Z, ∃ M : List ι, Reach p kind M A c x.1 x.2) :
    ∀ E ∈ outSet (step3D hM9 B0 A.data A.plain lA hLA bk0 q0 centre wBar) P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => twistedRecenteredFW p g S A.skeleton c.a Z P.L P.γ P.δ h wBar (modW lam)
          (tt 0) (tt 1) (tt 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 1) (sumintBoundary (A.skeleton.sign c.a.toNode) E 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 3)) (cubeSet q0) := by
  intro E hE
  have hsum : (fun tt : Fin 3 → ℝ => twistedRecenteredFW p g S A.skeleton c.a Z P.L P.γ P.δ h wBar (modW lam)
          (tt 0) (tt 1) (tt 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 1) (sumintBoundary (A.skeleton.sign c.a.toNode) E 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 3)) =
      fun tt => ∑ x ∈ Z, recPhase (A.skeleton.sign c.a.toNode) P.L P.γ P.δ (tt 0)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 0) (sumintBoundary (A.skeleton.sign c.a.toNode) E 1)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 3) *
        twistedLocalKernelFW p g S x.1 x.2 P.L P.γ P.δ h wBar (modW lam) (tt 0) (tt 1) (tt 2)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 0) (sumintBoundary (A.skeleton.sign c.a.toNode) E 1)
          (sumintBoundary (A.skeleton.sign c.a.toNode) E 2) (sumintBoundary (A.skeleton.sign c.a.toNode) E 3) :=
    funext fun tt => twistedRecenteredFW_eq_sum p g S A.skeleton c.a Z _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [hsum]
  exact continuousOn_finsetSum _ fun x hx => by
    obtain ⟨M, hM⟩ := hZ x hx
    exact memberFW_continuousOn lam hgate hinc htop hd hη0 hη6 hη2 hC hδ hL hw hp hB hBpos hM hM9 B0 lA hLA hlA
      hAlay hAord bk0 q0 centre wBar hq0 hqle1 hqle2 H g cψ hcψ hgP S E hE

/-- **T5: continuity of the weighted class kernel** (weighted `Cont.twistedRecenteredModC_continuousOn`). -/
theorem weightedClassContinuity : WeightedClassContinuity := by
  intro w kind P lam hgate hinc htop hd hη0 hη6 hη2 hC hδ hL hw p hp h Bh hB hBpos G U a b R n hprime hM9 B RD hG
    layer hLayer hlay hord centre wBar g cψ hcψ hgP _hreal S _hS H
  have hZ : ∀ x ∈ canonFinsetK p kind (startState B RD hG layer hLayer) (chainStart B),
      ∃ M : List _, Reach p kind M (startState B RD hG layer hLayer) (chainStart B) x.1 x.2 := fun x hx => by
    obtain ⟨M, _, hM⟩ := (mem_canonFinset hprime).1 hx
    exact ⟨M, hM⟩
  have hI := assemblyShape_I_pos hM9 B
  exact classSumFW_continuousOn lam (A := startState B RD hG layer hLayer) (c := chainStart B) hgate hinc htop hd
    hη0 hη6 hη2 hC hδ hL hw hp hB hBpos hM9 B layer hLayer (stateLayer_start B RD hG layer hLayer) hlay hord
    (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar rfl
    (qOutOf_one_le hM9 B RD hG layer hLayer hI) (qOutOf_two_le hM9 B RD hG layer hLayer hI)
    H g cψ hcψ hgP S _ hZ

end WaveTurbulence.Flower.V5W
