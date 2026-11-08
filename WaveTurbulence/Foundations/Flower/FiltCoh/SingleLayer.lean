/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FiltCoh.TreeBound
public import WaveTurbulence.Foundations.Flower.FiltCoh.CoupleBound
public import WaveTurbulence.Foundations.Spine.RA1LW.Gate

/-! # FILT-COH: single-layer regular objects, any layer, individual leaf bounds (bound only)

Main's reductions for the regular asymptotics (`RA1Leafwise.couple_scaled`, `tree_scaled`, `couple_item_le`,
`tree_item_le`), with the leading term removed: multilinearity in the leaf profiles, translation to layer `r`, and,
for a tree whose lone leaf lies in a lower layer, relayering, freezing `s = r` and the trace. All are generic in the
time weight. -/

public section
open WaveTurbulence.Induct
noncomputable section
namespace WaveTurbulence.Flower.FiltCoh
open WaveTurbulence.RegAsymp MeasureTheory Set Filter TTree WaveTurbulence.Fourier WaveTurbulence.Regref
open WaveTurbulence.RA1Leafwise LGSpine
open scoped ENNReal Topology

variable {d : ℕ}

/-- Leafwise scaling of a couple-kernel bound (main's `couple_scaled`, leading term removed). -/
theorem couple_kernel_scaled (L γ δ θ : ℝ) (hd : 1 ≤ d) (Q : RegCpl) (LG : LayeredGarden 2)
    (_hQ : Q.Decodes LG.garden) (T : Set (Fin 2 → ℝ)) (X : ℝ≥0∞) (hX : X ≠ ⊤)
    (hRA : ∀ H' : LeafProfiles 2 d, (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      mixedRestrictionNorm θ (30 * d) (30 * d) T Set.univ
        (fun ts k => coupleLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1) ≤ X)
    (H : LeafProfiles 2 d) (B : Fin 2 × Path → NNReal) (hH : LeafwiseControlled LG H B) :
    mixedRestrictionNorm θ (30 * d) (30 * d) T Set.univ
        (fun ts k => coupleLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) ≤
      ENNReal.ofReal (leafSizeProduct LG B) * X := by
  classical
  unfold leafSizeProduct
  refine le_of_forall_eps (inputLeaves LG.garden) (fun ℓ => (B ℓ.1 : ℝ)) _ X hX ?_
  intro ε hε
  let S : Finset (Fin 2 × Path) := (inputLeaves LG.garden).image (fun ℓ => ℓ.1)
  let β : Fin 2 × Path → ℝ := fun z => (B z : ℝ) + ε
  have hβ0 : ∀ z, 0 < β z := fun z => by have := (B z).2; simp only [β]; positivity
  have hβne : ∀ z, β z ≠ 0 := fun z => (hβ0 z).ne'
  let H' := normProfile S β H
  have hnorm : ∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1 := by
    refine normProfile_norm_le (S := S) (B := fun z => (B z : ℝ)) hd (fun z => (B z).2) (fun z => ?_)
      hβ0 ?_
    · simp only [β]; linarith
    · intro z hz
      obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hz
      exact hH ℓ hℓ
  have hscale : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = fun k => β ℓ.1 * H' ℓ.1 k := fun ℓ hℓ =>
    normProfile_scale hβne (Finset.mem_image_of_mem _ hℓ)
  set P : ℝ := ∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 with hP
  have hPpos : 0 < P := Finset.prod_pos fun ℓ _ => hβ0 _
  have hD : (fun (ts : T) (k : (Set.univ : Set (Mom d))) =>
        coupleLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) =
      fun ts k => (P : ℂ) • coupleLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1 := by
    funext ts k
    rw [RA1Leafwise.coupleLeaves_scale L γ δ LG H H' β hscale]
    simp only [smul_eq_mul, hP]
  rw [hD]
  have hc : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  refine (mixedRestrictionNorm_smul_le hc θ _ _ _ _ _).trans ?_
  rw [show ‖(P : ℂ)‖ₑ = ENNReal.ofReal P by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos]]
  exact mul_le_mul' le_rfl (hRA H' hnorm)

/-- Leafwise scaling of a tree-kernel bound (main's `tree_scaled`, leading term removed). -/
theorem tree_kernel_scaled (L γ δ θ : ℝ) (hd : 1 ≤ d) (_X : RegChain) (LG : LayeredGarden 1)
    (T : Set (Fin 2 → ℝ)) (M : ℝ≥0∞) (hM : M ≠ ⊤)
    (hRA : ∀ H' : LeafProfiles 1 d, (∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1) →
      mixedRestrictionNorm θ (30 * d) 0 T Set.univ
        (fun ts k => treeLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1) ≤ M)
    (H : LeafProfiles 1 d) (B : Fin 1 × Path → NNReal) (hH : LeafwiseControlled LG H B) :
    mixedRestrictionNorm θ (30 * d) 0 T Set.univ
        (fun ts k => treeLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) ≤
      ENNReal.ofReal (leafSizeProduct LG B) * M := by
  classical
  unfold leafSizeProduct
  refine le_of_forall_eps (inputLeaves LG.garden) (fun ℓ => (B ℓ.1 : ℝ)) _ M hM ?_
  intro ε hε
  let S : Finset (Fin 1 × Path) := (inputLeaves LG.garden).image (fun ℓ => ℓ.1)
  let β : Fin 1 × Path → ℝ := fun z => (B z : ℝ) + ε
  have hβ0 : ∀ z, 0 < β z := fun z => by have := (B z).2; simp only [β]; positivity
  have hβne : ∀ z, β z ≠ 0 := fun z => (hβ0 z).ne'
  let H' := normProfile S β H
  have hnorm : ∀ z, SNormR (40 * d) (40 * d) (H' z) ≤ ENNReal.ofReal 1 := by
    refine normProfile_norm_le (S := S) (B := fun z => (B z : ℝ)) hd (fun z => (B z).2) (fun z => ?_)
      hβ0 ?_
    · simp only [β]; linarith
    · intro z hz
      obtain ⟨ℓ,hℓ,rfl⟩ := Finset.mem_image.mp hz
      exact hH ℓ hℓ
  have hscale : ∀ ℓ ∈ inputLeaves LG.garden, H ℓ.1 = fun k => β ℓ.1 * H' ℓ.1 k := fun ℓ hℓ =>
    normProfile_scale hβne (Finset.mem_image_of_mem _ hℓ)
  set P : ℝ := ∏ ℓ ∈ inputLeaves LG.garden, β ℓ.1 with hP
  have hPpos : 0 < P := Finset.prod_pos fun ℓ _ => hβ0 _
  have hD : (fun (ts : T) (k : (Set.univ : Set (Mom d))) =>
        treeLeaves L γ δ LG H (ts.1 0) (ts.1 1) k.1) =
      fun ts k => (P : ℂ) • treeLeaves L γ δ LG H' (ts.1 0) (ts.1 1) k.1 := by
    funext ts k
    rw [RA1Leafwise.treeLeaves_scale L γ δ LG H H' β hscale]
    simp only [smul_eq_mul, hP]
  rw [hD]
  have hc : (P : ℂ) ≠ 0 := by exact_mod_cast hPpos.ne'
  refine (mixedRestrictionNorm_smul_le hc θ _ _ _ _ _).trans ?_
  rw [show ‖(P : ℂ)‖ₑ = ENNReal.ofReal P by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos]]
  exact mul_le_mul' le_rfl (hRA H' hnorm)

/-- Translation of a couple-kernel bound from layer `0` to layer `r` (main's `couple_item_le`). -/
theorem couple_kernel_item_le (L γ δ : ℝ) (H : LeafProfiles 2 d) {Q : RegCpl} {LG : LayeredGarden 2}
    (hdec : Q.Decodes LG.garden) {r : ℕ} (hlay : ∀ a, LG.layer a = r) {θ : ℝ} {Λ : ℕ} {M : ℝ≥0∞}
    (hM : mixedRestrictionNorm θ Λ Λ (timeBox 0 0) Set.univ
      (fun ts k => coupleLeaves L γ δ (layer0 LG) H (ts.1 0) (ts.1 1) k.1) ≤ M) :
    XNormRestr θ Λ Λ (timeBox r r) Set.univ
      (fun ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k) ≤ M := by
  refine le_trans ?_ ((XNormRestr_eq_mixedRestrictionNorm θ Λ Λ (timeBox 0 0)
    (fun ts k => coupleLeaves L γ δ (layer0 LG) H (ts 0) (ts 1) k)).le.trans hM)
  refine XNormRestr_shift_le θ Λ Λ (fun _ => (r : ℝ)) (fun ts hts => sub_mem_timeBox_self' hts)
    fun ts _ k _ => ?_
  exact KQstarLeaf_shift L γ δ LG hdec.1 (fun ℓ => (H ℓ.1 : Mom d → ℝ)) r hlay (ts 0) (ts 1) k

/-- Layer translation, relayering, freezing `s = r` and the trace for a tree-kernel bound (main's
`tree_item_le`, leading term removed). -/
theorem tree_kernel_item_le (L γ δ : ℝ) (H : LeafProfiles 1 d)
    {X : RegChain} {LG : LayeredGarden 1} (hX : X.DecodesTree LG.garden)
    (hFs : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k : Mom d,
      Summable fun n : Fin d → ℤ => |H ℓ.1 (k + latticePoint L n)|)
    {q' r : ℕ} (hq : q' ≤ r)
    (hlay : ∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r)
    {θ : ℝ} (hθ : 0 ≤ θ) {Λ : ℕ} (hΛ : Λ ≠ 0) {M : ℝ≥0∞}
    (hM : mixedRestrictionNorm θ Λ 0 (timeBoxGt 0 0) Set.univ
      (fun ts k => treeLeaves L γ δ (layer0 LG) H (ts.1 0) (ts.1 1) k.1) ≤ M) :
    XNormRestr θ Λ 0 (timeBoxGt r q') Set.univ
      (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k) ≤ traceConst (r := 2) θ chiUnit * M := by
  set h₀ : (Fin 2 → ℝ) → Mom d → ℂ := fun ts k =>
    treeLeaves L γ δ (layer0 LG) H (ts 0) (ts 1) k with hh₀
  have hP := isPairedTree_of_decodesTree hX
  let Fl : GLeaf LG.garden.tree → Mom d → ℝ := fun ℓ => H ℓ.1
  have hrel : ∀ t s k, treeLeaves L γ δ LG H t s k =
      treeLeaves L γ δ (constLayer LG r) H t s k :=
    fun t s k => (KTstarLeaf_relayer L γ δ (LG := LG) (fun _ => r) (constLayer LG r).isLayering
      (fun b => by
        rw [hlay b.toNode]
        split_ifs with hc
        · exact absurd hc (branch_ne_lonePath hX b)
        · rfl) Fl t s k).symm
  have hshift : ∀ t s k, treeLeaves L γ δ (constLayer LG r) H t s k =
      treeLeaves L γ δ (layer0 LG) H (t - r) (s - r) k :=
    fun t s k => KTstarLeaf_shift L γ δ (constLayer LG r) hX Fl r (fun _ => rfl) t s k
  have hf : ∀ t s k, treeLeaves L γ δ LG H t s k = h₀ ![t - r, s - r] k := by
    intro t s k
    rw [hrel, hshift]
    rfl
  have hM' : XNormRestr θ Λ 0 (timeBoxGt 0 0) Set.univ h₀ ≤ M :=
    (XNormRestr_eq_mixedRestrictionNorm θ Λ 0 _ h₀).le.trans hM
  have hK1 : 1 ≤ traceConst (r := 2) θ chiUnit :=
    one_le_traceConst hθ chiUnit_contDiff (coordinateCutoff_chiUnit (t := fun _ => 0)
      ⟨⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩⟩)
  rcases hq.lt_or_eq with hlt | heq
  · have hfreeze : ∀ ts ∈ timeBoxGt r q', ∀ k : Mom d,
        treeLeaves L γ δ LG H (ts 0) (ts 1) k =
          h₀ (Function.update (ts - fun i => ![(r : ℝ), (q' : ℝ)] i) 1 0) k := by
      intro ts hts k
      have hs : ts 1 ≤ r := by
        have := hts.1.2.2
        have hq1 : ((q' : ℝ) + 1) ≤ r := by exact_mod_cast hlt
        linarith
      rw [hrel]
      have hind := KTstarLeaf_indep_of_le L γ δ (constLayer LG r) hP Fl (ts 0) (ts 1) r k
        (fun b _ => ⟨by simpa [constLayer] using hs, by simp [constLayer]⟩)
      rw [show treeLeaves L γ δ (constLayer LG r) H (ts 0) (ts 1) k =
          treeLeaves L γ δ (constLayer LG r) H (ts 0) r k from hind, ← hrel, hf]
      congr 1
      funext i
      fin_cases i <;> simp [Function.update]
    have hcont : ∀ k ∈ (Set.univ : Set (Mom d)), Continuous fun ts => h₀ ts k := by
      intro k _
      exact continuous_KTstarLeaf_time (L := L) (γ := γ) (δ := δ) (layer0 LG) hP Fl k (fun ℓ hℓ => hFs ℓ hℓ k)
    calc XNormRestr θ Λ 0 (timeBoxGt r q') Set.univ _
        ≤ XNormRestr θ Λ 0 (timeBox 0 0) Set.univ (fun ts k => h₀ (Function.update ts 1 0) k) := by
          refine XNormRestr_shift_le θ Λ 0 (fun i => ![(r : ℝ), (q' : ℝ)] i) (fun ts hts => ?_)
            (fun ts hts k _ => hfreeze ts hts k)
          obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, -⟩ := hts
          refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp <;> linarith
      _ ≤ mixedRestrictionNorm θ Λ 0 (timeBox 0 0) Set.univ
            (fun ts k => h₀ (Function.update ts.1 1 0) k.1) :=
          (XNormRestr_eq_mixedRestrictionNorm θ Λ 0 _ _).le
      _ ≤ traceConst (r := 2) θ chiUnit * mixedRestrictionNorm θ Λ 0 (timeBoxGt 0 0) Set.univ
            (fun ts k => h₀ ts.1 k.1) :=
          mixedRestrictionNorm_trace_le hΛ hθ chiUnit_contDiff chiUnit_hasCompactSupport h₀ hcont 1 0
            (fun t ht => update_mem_closure_interior ht) (fun t ht => coordinateCutoff_chiUnit ht)
      _ ≤ traceConst (r := 2) θ chiUnit * M := mul_le_mul' le_rfl hM
  · subst heq
    calc XNormRestr θ Λ 0 (timeBoxGt q' q') Set.univ _
        ≤ XNormRestr θ Λ 0 (timeBoxGt 0 0) Set.univ h₀ := by
          refine XNormRestr_shift_le θ Λ 0 (fun _ => (q' : ℝ)) (fun ts hts => ?_)
            (fun ts _ k _ => ?_)
          · obtain ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩ := hts
            refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩ <;> simp <;> linarith
          · rw [hf]
            congr 1
            funext i
            fin_cases i <;> simp
      _ ≤ M := hM'
      _ ≤ traceConst (r := 2) θ chiUnit * M := le_mul_of_one_le_left zero_le hK1

end WaveTurbulence.Flower.FiltCoh
