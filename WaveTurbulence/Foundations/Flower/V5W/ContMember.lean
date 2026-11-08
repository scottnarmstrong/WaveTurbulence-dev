/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.V5W.ContCore

/-! # V5W-0, row 0c (part 3): continuity of one recentered weighted member kernel

`clRecenteredFW_continuousOn`: weighted copy of main's `Cont.clRecenteredMod_continuousOn` (Cont/ModCore).  The rows of
`assemblyClockedFW` are selected: the coherent ones are main's rows (bounds `coupleRow_leaf_le`/`treeRow_leaf_le`,
continuity `rows_continuousH`), the incoherent ones are bounded by INC-TOP's `TopIncoherentDecayAtR` (at the clock-slot
layers, which are the root parent layers: `coupleRootParents_rowQ`, `treeRootParent_rowQ`) and continuous by row 0a.
The region multiplier enters through the bounded lattice factor of `clockedExprEpsMX`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
noncomputable section
namespace WaveTurbulence.Flower.V5W
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3.Eng
  WaveTurbulence.DegenVine WaveTurbulence.LGSpine VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory Filter
  Topology
open WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS5C.Cont WaveTurbulence.VineC
  WaveTurbulence.Flower.Stage1W
open scoped ENNReal

/-- Leafwise control of the (spine) layer profiles of `h` on a garden with layers `≤ p` (main's
`VineEstS5C.controlled_layerProfiles`, for `LGSpine.layerProfiles`, the profiles of the pinned incoherent rows). -/
theorem controlled_layerProfiles_spine {P : WTParams} {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ} {p : ℕ}
    (hB : ProfileBound P h Bh p) {w : ℕ} (LG : LayeredGarden w) (hlay : ∀ x, LG.layer x ≤ p) :
    LeafwiseControlled LG (layerProfiles LG h) (fun z => Real.toNNReal (Bh (Links.layerAt LG z))) := by
  intro ℓ hℓ
  have hle : Links.layerAt LG ℓ.1 ≤ p := (Links.layerAt_node LG ℓ.toNode).le.trans (hlay _)
  obtain ⟨h0, h1⟩ := hB _ hle
  rw [layerProfiles_leaf, Real.coe_toNNReal _ h0, ← Links.layerAt_node LG ℓ.toNode]
  exact h1

/-- **Continuity of one recentered weighted member kernel** in `(t₀,t₁,t₂)` on the closed output cube, for every
output of the output set (weighted copy of `Cont.clRecenteredMod_continuousOn`). -/
theorem clRecenteredFW_continuousOn {P : WTParams} (lam : ℝ)
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (htop : TopIncoherentDecayAtR P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b}
    {n : ℕ} (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
    (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
    (qOut : Fin 3 → ℕ) (hqo : qOut 0 = layer (RD.coreBranch hG a).toNode) (centre : Fin 4 → Mom P.d)
    (wBar : Mom P.d) (badKind : Fin (assemblyShape hM9 B).I → Fin 4) (hbad2 : ∀ i, badKind i ≠ 2)
    (hel : ∀ v, CoupleEligible hM9 B RD hG (step3W hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ
          h layer hLayer (P.N (p + 1) ^ 4) p v ∧
        TreeEligible hM9 B RD hG (step3W hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ
          h layer hLayer (P.N (p + 1) ^ 4) p v)
    (hq1 : (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching ∨
      (qOut 1 : ℝ) ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (hq2 : (b.child R.negative).1.2 ∈ (G.tree (b.child R.negative).1.1).branching ∨
      (qOut 2 : ℝ) ≤ assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode)
        (.inl ⟨⟨0, assemblyShape_I_pos hM9 B⟩, 0⟩))
    (g : Mom P.d → ℂ) (cψ : ℝ) (hcψ : 1 ≤ cψ) (hgP : GPresented (32 * P.d) g cψ)
    (m : (GNode G.tree → Fin P.d → ℤ) → ℂ) (Cm : ℝ) (hCm : 0 ≤ Cm) (hm : ∀ z, ‖m z‖ ≤ Cm) :
    ∀ E ∈ outSet (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => recPhase (G.sign a.toNode) P.L P.γ P.δ (tt 0)
          (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3) *
        clLocalKernelFW p g RD hG R P.L P.γ P.δ h layer hLayer wBar m (modW lam)
          (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3))
        (cubeSet (step3D hM9 B RD hG layer hLayer badKind qOut centre wBar).qOut) := by
  classical
  have hL0 : 0 < P.L := by linarith
  set W := step3W hM9 B RD hG layer hLayer badKind qOut centre wBar with hW
  set D := sourceSumintDatum hM9 B hG W with hD
  have hI := assemblyShape_I_pos hM9 B
  have hbad2' : ∀ i, D.badKind i ≠ 2 := fun i => hbad2 i
  have hqq : ∀ v, (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
      (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1 := fun v => (hel v).2.1
  have hgn : ∀ x, ‖g x‖ ≤ cψ := fun x => GPresented.norm_le hgP (by linarith) x
  have hWq : W.q = assemblyTimeQ hM9 B (fun v => layer (RD.coreBranch hG v).toNode) := rfl
  have hWqo : W.qOut 0 = layer (RD.coreBranch hG a).toNode := hqo
  set cr := assemblyClockedFW hM9 B RD hG W p g P.L P.γ P.δ h layer hLayer with hcr
  have hsum : ∀ k : Mom P.d, ∀ ℓ : ℕ, ℓ ≤ p → Summable fun n : Fin P.d → ℤ => |h ℓ (k + latticePoint P.L n)| :=
    fun k ℓ hℓ => summable_abs_coset_of_SNormR (A := 40 * P.d) (B := 40 * P.d) hL (by omega) (hB ℓ hℓ).1 (h ℓ)
      (hB ℓ hℓ).2 k
  have hplainC : ∀ v, (rowCoupleLG hM9 B RD hG layer hLayer v).garden.IsPlain := by
    intro v
    unfold rowCoupleLG
    rw [nativeCoupleLayered_garden]
    exact (decodedCouple_decodes _).1.1
  have hpairT : ∀ v, IsPairedTree (rowTreeLG hM9 B RD hG layer hLayer v).garden := by
    intro v
    unfold rowTreeLG
    exact decodedTree_isPairedTree _ _
  -- continuity of the selected rows
  have hcont : ∀ ρ k, Continuous fun c => cr.W ρ c k := by
    intro ρ k
    rcases ρ with v | v
    · by_cases hc : coupleIncoh RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 = 0
      · rw [hcr, assemblyClockedFW_inl_coh hM9 B RD hG layer hLayer W p g P.L P.γ P.δ h v hc]
        exact rows_continuousH hB hd hL hlay W (Sum.inl v) k
      · rw [hcr, assemblyClockedFW_inl_incoh hM9 B RD hG layer hLayer W p g P.L P.γ P.δ h hWq hWqo v hc]
        exact continuous_coupleLeavesTop_time P.L P.γ P.δ p g _ _ h (rowCoupleLG hM9 B RD hG layer hLayer v)
          (hplainC v) k cψ hcψ hgn (fun ℓ _ => hsum k _ (hlay _))
    · by_cases hc : treeIncoh RD hG layer hLayer (assemblyBranchOf hM9 B v).1 = 0
      · rw [hcr, assemblyClockedFW_inr_coh hM9 B RD hG layer hLayer W p g P.L P.γ P.δ h v hc]
        exact rows_continuousH hB hd hL hlay W (Sum.inr v) k
      · rw [hcr, assemblyClockedFW_inr_incoh hM9 B RD hG layer hLayer W p g P.L P.γ P.δ h hWq hWqo v hc]
        exact continuous_treeLeavesTop_time P.L P.γ P.δ p g _ h (rowTreeLG hM9 B RD hG layer hLayer v)
          (hpairT v) k cψ hcψ hgn (fun ℓ _ => hsum k _ (hlay _))
  -- finite restriction norms of the selected rows
  have hres : ∀ ρ, ∃ θ : ℝ, 0 ≤ θ ∧
      XNormRestr θ (30 * P.d) (Eng.rowOrder D ρ) (rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ) Set.univ
        (cr.W ρ) ≠ ⊤ := by
    intro ρ
    rcases ρ with v | v
    · by_cases hc : coupleIncoh RD hG layer hLayer (assemblyPairOf hM9 B hG v).1 = 0
      · refine ⟨6 * P.η ^ 6, by positivity, ?_⟩
        rw [hcr, assemblyClockedFW_inl_coh hM9 B RD hG layer hLayer W p g P.L P.γ P.δ h v hc]
        exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (coupleRow_leaf_le W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).1)
      · refine ⟨P.η, hη0.le, ?_⟩
        rw [hcr, assemblyClockedFW_inl_incoh hM9 B RD hG layer hLayer W p g P.L P.γ P.δ h hWq hWqo v hc]
        obtain ⟨hq0, hq0', hn, hr0, hr1, -⟩ := (hel v).1
        have hwf : (rowCouple hM9 B RD hG v).wf = true := RD.couple_wf _
        have hsize : (rowCouple hM9 B RD hG v).size = 2 * ((rowCouple hM9 B RD hG v).size / 2) :=
          (Nat.two_mul_div_two_of_even (code_size_even _)).symm
        have hlayLG : ∀ x, (rowCoupleLG hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _
        have hX := (htop p hp _ hn (fun _ => g) cψ hcψ (fun _ => hgP)).1 (rowCouple hM9 B RD hG v) hwf hsize
          (rowCoupleLG hM9 B RD hG layer hLayer v) (rowCouple_decodes v) hlayLG _ _ hq0 hq0' hr0 hr1
          (Nat.one_le_iff_ne_zero.mpr hc) (layerProfiles (rowCoupleLG hM9 B RD hG layer hLayer v) h) _
          (controlled_layerProfiles_spine hB _ hlayLG)
        refine ne_top_of_le_ne_top ?_ hX
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by unfold regBound; exact ENNReal.ofReal_ne_top))
          ENNReal.ofReal_ne_top
    · by_cases hc : treeIncoh RD hG layer hLayer (assemblyBranchOf hM9 B v).1 = 0
      · refine ⟨6 * P.η ^ 6, by positivity, ?_⟩
        rw [hcr, assemblyClockedFW_inr_coh hM9 B RD hG layer hLayer W p g P.L P.γ P.δ h v hc]
        exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
          (treeRow_leaf_le W hgate hinc hd hη6 hη2 hC hδ.le hL hw hp hB hlay v (hel v).2)
      · refine ⟨P.η, hη0.le, ?_⟩
        rw [hcr, assemblyClockedFW_inr_incoh hM9 B RD hG layer hLayer W p g P.L P.γ P.δ h hWq hWqo v hc]
        obtain ⟨hqq', hqp, hn, hr0, hlone, -⟩ := (hel v).2
        have hwf : (rowTree hM9 B RD v).wf = true := RD.tree_wf _
        have hsize : (rowTree hM9 B RD v).size = 2 * ((rowTree hM9 B RD v).size / 2) :=
          (Nat.two_mul_div_two_of_even (chain_size_even _)).symm
        have hlayLG : ∀ x, (rowTreeLG hM9 B RD hG layer hLayer v).layer x ≤ p := fun x => hlay _
        have hX := (htop p hp _ hn (fun _ => g) cψ hcψ (fun _ => hgP)).2 (rowTree hM9 B RD v) hwf hsize
          (rowTreeLG hM9 B RD hG layer hLayer v) (rowTree_decodes v) hlayLG _ _ hqq' hqp hr0 hlone
          (Nat.one_le_iff_ne_zero.mpr hc) (layerProfiles (rowTreeLG hM9 B RD hG layer hLayer v) h) _
          (controlled_layerProfiles_spine hB _ hlayLG)
        refine ne_top_of_le_ne_top ?_ hX
        exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by unfold regBound; exact ENNReal.ofReal_ne_top))
          ENNReal.ofReal_ne_top
  -- pointwise decay of the selected rows
  have hdec : ∀ ρ, ∃ M : ℝ, 0 < M ∧ ∀ c ∈ closure (interior (rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ)),
      ∀ k, ‖cr.W ρ c k‖ ≤ M * decayWt D (30 * P.d) ρ k := by
    intro ρ
    obtain ⟨θ, hθ, hfin⟩ := hres ρ
    obtain ⟨M, hM, hlt⟩ := exists_lt_ofReal hfin
    refine ⟨M, hM, fun c hc k => ?_⟩
    have h1 := norm_le_decay_of_XNormRestr hθ (30 * P.d) (Eng.rowOrder D ρ) _ _ M hlt c hc k (hcont ρ k)
    rcases ρ with v | v
    · exact h1
    · simpa [decayWt, Eng.rowOrder] using h1
  choose M hM0 hMd using hdec
  set Bx : (D.S.VIdx → (Fin P.d → ℤ)) → (Fin 4 → Mom P.d) → ℝ := fun x E =>
    (∏ ρ, M ρ) * ∏ ρ, decayWt D (30 * P.d) ρ (rowMom D P.L x E ρ) with hBx
  have hBxs : ∀ E, Summable fun x => Bx x E := fun E =>
    (summable_decayWt D hL0 (by omega : P.d + 1 ≤ 30 * P.d) E).mul_left _
  have hBx0 : ∀ x E, 0 ≤ Bx x E := fun x E =>
    mul_nonneg (Finset.prod_nonneg fun ρ _ => (hM0 ρ).le)
      (Finset.prod_nonneg fun ρ _ => decayWt_nonneg D _ ρ _)
  have hbd : ∀ E x, ∀ tt ∈ cubeSet D.qOut, ∀ τ ∈ D.timeDom hI (tt 0) (tt 1) (tt 2),
      ∏ ρ, ‖cr.W ρ (cr.clock τ tt ρ) (rowMom D P.L x E ρ)‖ ≤ Bx x E := by
    intro E x tt htt τ hτ
    calc _ ≤ ∏ ρ, (M ρ * decayWt D (30 * P.d) ρ (rowMom D P.L x E ρ)) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun ρ _ =>
            hMd ρ _ (rowBx_closure hM9 B RD hG layer hLayer W P.L P.γ P.δ h hqq ρ
              (rows_clock_mem_cube hM9 B RD hG layer hLayer W
                (step3W_ok hM9 B RD hG layer hLayer badKind qOut centre wBar) P.L P.γ P.δ h tt htt τ hτ ρ)) _)
      _ = Bx x E := Finset.prod_mul_distrib
  intro E hE
  obtain ⟨β, hβ, rfl⟩ := outSet_exists_beta hL0.ne' (G.sign a.toNode) wBar E (fun c => (hE.1 c).1) hE.2.1
  simp only [sumintBoundary_invol]
  set E' := sumintBoundary (G.sign a.toNode) (fun j => wBar + latticePoint P.L (β j)) with hE'
  set mx : (D.S.VIdx → (Fin P.d → ℤ)) → ℂ :=
    fun x => m (clExtendIndices R ((clNormalizedChainEquiv hL0.ne' B W.wBar β hβ hM9).symm x).1) with hmx
  have hcontI : ContinuousOn (fun tt => ((coupling P.d P.L P.γ P.δ : ℂ) ^ clLocalOrder1 R * clLocalZeta R) *
      clockedExprEpsMX (D := D) (fun v : ↥U => childLabel hM9 B hG v.1 0)
        (fun v : ↥U => childLabel hM9 B hG v.1 1) (fun v : ↥U => childLabel hM9 B hG v.1 2) cr
        (assemblyCoreFirstSign hM9 B) (assemblyCoreSign hM9 B) hI P.L P.γ (2 * P.δ) P.η mx
        (fun (_ : Fin 3 → ℝ) (τ : D.S.TVar → ℝ) =>
          Complex.exp (((Real.pi * lam * τ (.inl ⟨⟨0, hI⟩, 0⟩) : ℝ) : ℂ) * Complex.I)) tt E')
      (cubeSet D.qOut) :=
    continuousOn_const.mul (continuousOn_clockedExprEpsMX hbad2' _ _ _ _ _ _ hI P.L P.γ (2 * P.δ) P.η E' mx Cm hCm
      (fun x => hm _) _ (continuous_mlow lam hI) (norm_mlow_le lam hI) hcont (cubeSet D.qOut) (fun x => Bx x E')
      (hBxs E') (fun x => hBx0 x E') (hbd E'))
  set b1 : Prop := (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching with hb1
  set b2 : Prop := (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching with hb2
  have hcomp := (hcontI.comp (continuous_leafT D.qOut b1 b2).continuousOn (mapsTo_leafT_cubeSet D.qOut b1 b2))
  refine hcomp.congr fun tt _ => ?_
  have hl0 := leafT_zero D.qOut b1 b2 tt
  have hl1 := leafT_one D.qOut b1 b2 tt
  have hl2 := leafT_two D.qOut b1 b2 tt
  have hcongr := recPhase_clLocalKernelFW_congr p g RD hG R P.L P.γ P.δ h layer hLayer wBar m (modW lam)
    (tt 0) (tt 1) (tt 2) (leafT D.qOut b1 b2 tt 1) (leafT D.qOut b1 b2 tt 2)
    (wBar + latticePoint P.L (β 0)) (wBar + latticePoint P.L (β 1))
    (wBar + latticePoint P.L (β 2)) (wBar + latticePoint P.L (β 3))
    (by by_cases h' : b1
        · exact Or.inl h'
        · exact Or.inr (by rw [hl1]; simp [h']))
    (by by_cases h' : b2
        · exact Or.inl h'
        · exact Or.inr (by rw [hl2]; simp [h']))
  refine hcongr.trans ?_
  have hk := kernelFW_eq_clockedExprEpsMX hM9 B p g RD hG W (fun _ => rfl) hbad2' (L := P.L) hL0.ne' P.γ P.δ P.η lam
    h layer hLayer rfl (step3W_ok hM9 B RD hG layer hLayer badKind qOut centre wBar) m β hβ (leafT D.qOut b1 b2 tt)
    (by by_cases h' : b1
        · right; rw [hl1]; simp only [h', ite_true]
          rcases hq1 with h'' | h''
          · exact absurd h'' h'
          · exact h''
        · left; exact not_not.1 h')
    (by by_cases h' : b2
        · right; rw [hl2]; simp only [h', ite_true]
          rcases hq2 with h'' | h''
          · exact absurd h'' h'
          · exact h''
        · left; exact not_not.1 h')
  rw [hl0] at hk
  exact hk

end WaveTurbulence.Flower.V5W
