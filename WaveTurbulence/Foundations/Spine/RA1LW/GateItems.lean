/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.XNormBridge
public import WaveTurbulence.Foundations.RegularAsymptotics.RegrefDraft.TreeItems
public import WaveTurbulence.Foundations.Spine.RA1LW.RegLeafwise
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.LeafwiseSpineInputs

/-! # Layer translation, relayering and the trace for leafwise kernels (RA1-LEAFWISE)

Leafwise forms of REGREF's `regularAsymptotics_couples` item (1) translation and `tree_item2_le`:
the layer-`r` error of a regular couple / tree with individually modified leaf inputs is bounded by the
layer-`0` restriction-norm bound (translation; for a tree with `q' < r` relayering, freezing `s = r` and the
trace). -/

public section
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp MeasureTheory Set Filter TTree WaveTurbulence.Fourier WaveTurbulence.Regref
open scoped ENNReal Topology

variable {d : ℕ}

theorem sub_mem_timeBox_self' {q : ℝ} {ts : Fin 2 → ℝ} (h : ts ∈ timeBox q q) :
    ts - (fun _ => q) ∈ timeBox 0 0 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [Pi.sub_apply] <;> linarith

theorem couple_app_shift (δ r : ℝ) (H : LGSpine.LeafProfiles 2 d) (Q : RegCpl) (t s : ℝ) (k : Mom d) :
    LGSpine.LeafApp.couple δ r H Q t s k = LGSpine.LeafApp.couple δ 0 H Q (t - r) (s - r) k := by
  simp only [LGSpine.LeafApp.couple, JB_shift r Q t s]

theorem tree_app_shift (δ r : ℝ) (H : LGSpine.LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) (t s : ℝ)
    (k : Mom d) :
    LGSpine.LeafApp.tree δ r H X ζ t s k = LGSpine.LeafApp.tree δ 0 H X ζ (t - r) (s - r) k := by
  simp only [LGSpine.LeafApp.tree, JBtree_shift r X t s]

theorem tree_app_of_le (δ r : ℝ) (H : LGSpine.LeafProfiles 1 d) (X : RegChain) (ζ : ℤˣ) (t s : ℝ)
    (k : Mom d) (h : s ≤ r) :
    LGSpine.LeafApp.tree δ r H X ζ t s k = LGSpine.LeafApp.tree δ r H X ζ t r k := by
  simp only [LGSpine.LeafApp.tree, JBtree_of_le r X t s h]

/-- Couples: translation of the layer-`r` error to the layer-`0` restriction norm. -/
theorem couple_item_le (L γ δ : ℝ) (H : LGSpine.LeafProfiles 2 d) {Q : RegCpl} {LG : LayeredGarden 2}
    (hdec : Q.Decodes LG.garden) {r : ℕ} (hlay : ∀ a, LG.layer a = r) {η : ℝ} {Λ : ℕ} {M : ℝ≥0∞}
    (hM : mixedRestrictionNorm η Λ Λ (timeBox 0 0) Set.univ
      (fun ts k => LGSpine.coupleLeaves L γ δ (layer0 LG) H (ts.1 0) (ts.1 1) k.1 -
        LGSpine.LeafApp.couple δ 0 H Q (ts.1 0) (ts.1 1) k.1) ≤ M) :
    XNormRestr η Λ Λ (timeBox r r) Set.univ
      (fun ts k => LGSpine.coupleLeaves L γ δ LG H (ts 0) (ts 1) k -
        LGSpine.LeafApp.couple δ r H Q (ts 0) (ts 1) k) ≤ M := by
  refine le_trans ?_ ((XNormRestr_eq_mixedRestrictionNorm η Λ Λ (timeBox 0 0)
    (fun ts k => LGSpine.coupleLeaves L γ δ (layer0 LG) H (ts 0) (ts 1) k -
        LGSpine.LeafApp.couple δ 0 H Q (ts 0) (ts 1) k)).le.trans hM)
  refine XNormRestr_shift_le η Λ Λ (fun _ => (r : ℝ)) (fun ts hts => sub_mem_timeBox_self' hts)
    fun ts _ k _ => ?_
  simp only [Pi.sub_apply]
  have h1 := KQstarLeaf_shift L γ δ LG hdec.1 (fun ℓ => (H ℓ.1 : Mom d → ℝ)) r hlay (ts 0) (ts 1) k
  rw [couple_app_shift δ r H Q]
  exact congrArg₂ _ h1 rfl

/-- **Leafwise tree item**: the layer-`(r, q')` error of a regular tree with individually modified leaf
inputs, from the layer-`0` restriction-norm bound (translation for `q' = r`; relayering, freezing `s = r` and
the trace for `q' < r`). -/
theorem tree_item_le (L γ δ : ℝ) (H : LGSpine.LeafProfiles 1 d)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hFs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k : Mom d,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|)
    {q' r : ℕ} (hq : q' ≤ r)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r)
    {η : ℝ} (hη : 0 ≤ η) {Λ : ℕ} (hΛ : Λ ≠ 0) {M : ℝ≥0∞}
    (hM : mixedRestrictionNorm η Λ 0 (timeBoxGt 0 0) Set.univ
      (fun ts k => LGSpine.treeLeaves L γ δ (layer0 LG) H (ts.1 0) (ts.1 1) k.1 -
        LGSpine.LeafApp.tree δ 0 H X (LG.garden.sig 0) (ts.1 0) (ts.1 1) k.1) ≤ M) :
    XNormRestr η Λ 0 (timeBoxGt r q') Set.univ
      (fun ts k => LGSpine.treeLeaves L γ δ LG H (ts 0) (ts 1) k -
        LGSpine.LeafApp.tree δ r H X (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ traceConst (r := 2) η chiUnit * M := by
  set ζ := LG.garden.sig 0
  set h₀ : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k =>
    LGSpine.treeLeaves L γ δ (layer0 LG) H (ts 0) (ts 1) k -
      LGSpine.LeafApp.tree δ 0 H X ζ (ts 0) (ts 1) k with hh₀
  have hP := isPairedTree_of_decodesTree hX
  let Fl : GLeaf LG.garden.tree → Mom d → ℝ := fun ℓ => H ℓ.1
  have hrel : ∀ t s k, LGSpine.treeLeaves L γ δ LG H t s k =
      LGSpine.treeLeaves L γ δ (constLayer LG r) H t s k :=
    fun t s k => (KTstarLeaf_relayer L γ δ (LG := LG) (fun _ => r) (constLayer LG r).isLayering
      (fun b => by
        rw [hlay b.toNode]
        split_ifs with hc
        · exact absurd hc (branch_ne_lonePath hX b)
        · rfl) Fl t s k).symm
  have hshift : ∀ t s k, LGSpine.treeLeaves L γ δ (constLayer LG r) H t s k =
      LGSpine.treeLeaves L γ δ (layer0 LG) H (t - r) (s - r) k :=
    fun t s k => KTstarLeaf_shift L γ δ (constLayer LG r) hX Fl r (fun _ => rfl) t s k
  have hf : ∀ t s k, LGSpine.treeLeaves L γ δ LG H t s k - LGSpine.LeafApp.tree δ r H X ζ t s k =
      h₀ ![t - r, s - r] k := by
    intro t s k
    rw [hrel, hshift, tree_app_shift]
    rfl
  have hM' : XNormRestr η Λ 0 (timeBoxGt 0 0) Set.univ h₀ ≤ M :=
    (XNormRestr_eq_mixedRestrictionNorm η Λ 0 _ h₀).le.trans hM
  have hK1 : 1 ≤ traceConst (r := 2) η chiUnit :=
    one_le_traceConst hη chiUnit_contDiff (coordinateCutoff_chiUnit (t := fun _ => 0)
      ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩)
  rcases hq.lt_or_eq with hlt | heq
  · -- `q' < r`: freeze `s = r`, translate, trace
    have hfreeze : ∀ ts ∈ timeBoxGt r q', ∀ k : Mom d,
        LGSpine.treeLeaves L γ δ LG H (ts 0) (ts 1) k - LGSpine.LeafApp.tree δ r H X ζ (ts 0) (ts 1) k =
          h₀ (Function.update (ts - fun i => ![(r : ℝ), (q' : ℝ)] i) 1 0) k := by
      intro ts hts k
      have hs : ts 1 ≤ r := by
        have := hts.1.2.2
        have hq1 : ((q' : ℝ) + 1) ≤ r := by exact_mod_cast hlt
        linarith
      rw [hrel]
      have hind := KTstarLeaf_indep_of_le L γ δ (constLayer LG r) hP Fl (ts 0) (ts 1) r k
        (fun b _ => ⟨by simpa [constLayer] using hs, by simp [constLayer]⟩)
      rw [show LGSpine.treeLeaves L γ δ (constLayer LG r) H (ts 0) (ts 1) k =
          LGSpine.treeLeaves L γ δ (constLayer LG r) H (ts 0) r k from hind,
        tree_app_of_le δ r H X ζ (ts 0) (ts 1) k hs, ← hrel, hf]
      congr 1
      funext i
      fin_cases i <;> simp [Function.update]
    have hcont : ∀ k ∈ (Set.univ : Set (Mom d)), Continuous fun ts => h₀ ts k := by
      intro k _
      refine Continuous.sub ?_ ?_
      · exact continuous_KTstarLeaf_time (L := L) (γ := γ) (δ := δ) (layer0 LG) hP Fl k (fun ℓ hℓ => hFs ℓ hℓ k)
      · have hJ : Continuous fun p : ℝ × ℝ => X.JBtree 0 p.1 p.2 := LGSpine.continuous_RegChain_JBtree 0 X
        have hJ' : Continuous fun ts : Fin 2 → ℝ => ((X.JBtree 0 (ts 0) (ts 1) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp (hJ.comp (by fun_prop : Continuous fun ts : Fin 2 → ℝ => (ts 0, ts 1)))
        unfold LGSpine.LeafApp.tree
        by_cases hdom : X.dominant
        · simp only [hdom, ite_true]
          exact continuous_const.mul (continuous_finsetSum _ fun Z _ =>
            (continuous_const.mul hJ').mul continuous_const)
        · simp only [hdom]
          exact continuous_const
    calc XNormRestr η Λ 0 (timeBoxGt r q') Set.univ _
        ≤ XNormRestr η Λ 0 (timeBox 0 0) Set.univ (fun ts k => h₀ (Function.update ts 1 0) k) := by
          refine XNormRestr_shift_le η Λ 0 (fun i => ![(r : ℝ), (q' : ℝ)] i) (fun ts hts => ?_)
            (fun ts hts k _ => hfreeze ts hts k)
          obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, -⟩ := hts
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
      _ ≤ mixedRestrictionNorm η Λ 0 (timeBox 0 0) Set.univ
            (fun ts k => h₀ (Function.update ts.1 1 0) k.1) :=
          (XNormRestr_eq_mixedRestrictionNorm η Λ 0 _ _).le
      _ ≤ traceConst (r := 2) η chiUnit * mixedRestrictionNorm η Λ 0 (timeBoxGt 0 0) Set.univ
            (fun ts k => h₀ ts.1 k.1) :=
          mixedRestrictionNorm_trace_le hΛ hη chiUnit_contDiff chiUnit_hasCompactSupport h₀ hcont 1 0
            (fun t ht => update_mem_closure_interior ht) (fun t ht => coordinateCutoff_chiUnit ht)
      _ ≤ traceConst (r := 2) η chiUnit * M := mul_le_mul' le_rfl hM
  · -- `q' = r`: translate by `(r, r)`
    subst heq
    calc XNormRestr η Λ 0 (timeBoxGt q' q') Set.univ _
        ≤ XNormRestr η Λ 0 (timeBoxGt 0 0) Set.univ h₀ := by
          refine XNormRestr_shift_le η Λ 0 (fun _ => (q' : ℝ)) (fun ts hts => ?_)
            (fun ts _ k _ => ?_)
          · obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩ := hts
            refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith
          · rw [hf]
            congr 1
            funext i
            fin_cases i <;> simp
      _ ≤ M := hM'
      _ ≤ traceConst (r := 2) η chiUnit * M := le_mul_of_one_le_left zero_le hK1

end WaveTurbulence.RA1Leafwise
