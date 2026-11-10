/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.CapPNT
public import WaveTurbulence.Foundations.Flower.MkSlotsB.ROne
public import WaveTurbulence.Foundations.Flower.MkSlots.CapObl
public import WaveTurbulence.Foundations.Flower.ProtPin.ProtGate
public import WaveTurbulence.Foundations.Flower.ProtWhole.AnnFree

/-! # B3s-HELPER8 / CAP: D3 and D6 on a cap couple with stem filters

The filtered twin of β's `MkSlotsB/CapPSup.lean` (copied by source and generalized, see `COPIED-SHA256SUMS`): on a
D6b cap couple `D : CapG LG j0 c X ζ` (paired tree `D.T1`), for a pattern configuration `cfg` (`term`, `rootTerm`,
`penTerm`, `termChild i`), with D3's multiplier carrying two filter layers `F`, `Fu` (`capMF`) or D6's multiplier with one
selected annular filter at a chain vertex `v` (`capMA`):

* `capF_xnorm`: D3's bound on `cfg.box` at one momentum, `θ = η` (`L^{31d+6}`) or `θ = 1/4` at `term` (`L^{47d+2}`);
* `capF_sup`: the superposition on the window `[p, p + 1]` when `cfg` does not pin the root;
* `capF_pointwise`: the pointwise bound at clocks `x ∈ [t, p + 1]` when `cfg` pins the root;
* `capA_xnorm`, `capA_sup`: D6 (`ProtAnnBoundAt`, `pin = true`, `Sel = {v}`, `θ = η`) at `term`, the superposition on
  the window, mass `L^{2(47d+5)} · M₂^{-1/18}`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtWhole WaveTurbulence.Flower.ProtCut
  WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsB

namespace WaveTurbulence.Flower.MkSlotsO

/-! ### The multipliers -/

section Mult

variable {w d : ℕ} {G : Garden w}

/-- **D3's multiplier** with two filter layers: star weights, upper filters `F` (scales `M`) and `Fu` (scales `Mu`),
the dagger indicator. -/
def capMF (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ) (F : Finset (GBranch G.tree))
    (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ)
    (ind : (GNode G.tree → Mom d) → ℝ) : (GNode G.tree → Mom d) → ℂ :=
  fun κ => IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ * filtWeight Fu (fun _ => false) Mu κ *
    (ind κ : ℂ)

/-- **D6's multiplier** with the selected annular filters on `Sel` (scale `M₂`). -/
def capMA (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ) (F : Finset (GBranch G.tree))
    (M : GBranch G.tree → ℝ) (Sel : Finset (GBranch G.tree)) (M₂ : ℝ) (Fu : Finset (GBranch G.tree))
    (Mu : GBranch G.tree → ℝ) (ind : (GNode G.tree → Mom d) → ℝ) : (GNode G.tree → Mom d) → ℂ :=
  fun κ => IncTop.starWeight S ω κ *
    filtWeight (F ∪ Sel) (fun b => decide (b ∈ Sel)) (fun b => if b ∈ Sel then M₂ else M b) κ *
    filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)

/-- Without selected vertices D6's multiplier is D3's. -/
theorem capMA_empty (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ) (F : Finset (GBranch G.tree))
    (M : GBranch G.tree → ℝ) (M₂ : ℝ) (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ)
    (ind : (GNode G.tree → Mom d) → ℝ) : capMA S ω F M ∅ M₂ Fu Mu ind = capMF S ω F M Fu Mu ind := by
  funext κ
  unfold capMA capMF
  simp only [Finset.union_empty, Finset.notMem_empty, decide_false, ↓reduceIte]

theorem norm_filtWeight_false_le (F : Finset (GBranch G.tree)) (M : GBranch G.tree → ℝ) (κ : GNode G.tree → Mom d) :
    ‖filtWeight F (fun _ => false) M κ‖ ≤ 1 := by
  unfold filtWeight
  rw [norm_prod]
  refine Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun b _ => ?_
  simp only [Bool.false_eq_true, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
  exact XChain.ProductCut.chi0_le_one _

theorem norm_filtWeight_le (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (κ : GNode G.tree → Mom d) : ‖filtWeight F ann M κ‖ ≤ MkDefs.chiDNorm ^ F.card := by
  unfold filtWeight
  rw [norm_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun b _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  split_ifs
  · exact MkDefs.abs_chiD_le_chiDNorm _
  · rw [abs_of_nonneg (XChain.ProductCut.chi0_nonneg _)]
    exact (XChain.ProductCut.chi0_le_one _).trans MkDefs.one_le_chiDNorm

end Mult

/-! ### D3 for a pattern configuration of a cap couple, with filters -/

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ}

/-- **D3 at a pattern configuration with filters**, on `cfg.box`, at one momentum (`θ = η` at `L^{31d+6}`, or
`θ = 1/4` at `term`, `L^{47d+2}`). -/
theorem capF_xnorm {P : WTParams} (hD3 : ProtBoundAt P) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (cfg : ProtCfg) (hv : cfg.Valid X D.T1 p)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i)
    (hamb : ProtAmbient p X D.T1) {θ cL : ℝ}
    (hθ : (θ = P.η ∧ cL = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ cL = 47 * P.d + 2 ∧ cfg = .term))
    {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch D.T1.garden.tree)) (M : GBranch D.T1.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch D.T1.garden.tree)) (Mu : GBranch D.T1.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) :
    XNormRestr θ (30 * P.d) 0 (cfg.box X t p p) {k₀}
      (fun ts k => kernelProt P.L P.γ P.δ D.T1 H1 (capMF S ω F M Fu Mu ind)
        (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ cL) *
        regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B) := by
  have hnot : cfg = .none ∨ cfg = .root ∨ cfg = .trace → False := by
    rintro (h | h | h) <;> rcases hcfg with h' | h' | h' | ⟨i, h'⟩ <;> rw [h'] at h <;> exact absurd h (by simp)
  have hθ' : (θ = P.η ∧ cL = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ cL = 47 * P.d + 2 ∧ (cfg = .none ∨ cfg = .term)) := by
    rcases hθ with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, Or.inr h3⟩
  have key := hD3 p hp n hn 1 D.T1 X hshape hsz cfg hv hamb θ cL hθ' s t hps hst htp p le_rfl S ω cω hpres F M hM
    Fu Mu hMu ind hind (fun h => (hnot h).elim) H1 B hLC k₀ k₀
  have hk : ({k₀} : Set (Mom P.d)) ⊆ latticeBall P.L k₀ k₀ := by
    intro k hk
    rw [Set.mem_singleton_iff.1 hk]
    exact ⟨by simp, 0, by simp [WaveTurbulence.Links.latticePoint_zero]⟩
  exact (xnormRestr_anti_out _ _ _ _ hk _).trans key

/-- **The superposition of a configuration that does not pin the root**, from D3 with filters. -/
theorem capF_sup {P : WTParams} (hD3 : ProtBoundAt P) {θ cL : ℝ} {C : ℝ≥0∞} (hC : CapSupProp P.d θ C)
    (hθ0 : 0 ≤ θ) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (cfg : ProtCfg) (hv : cfg.Valid X D.T1 p)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i)
    (hθ : (θ = P.η ∧ cL = 31 * P.d + 6) ∨ (θ = 1 / 4 ∧ cL = 47 * P.d + 2 ∧ cfg = .term))
    (hroot : cfg.pinsRoot X = false)
    (hamb : ProtAmbient p X D.T1) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch D.T1.garden.tree)) (M : GBranch D.T1.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch D.T1.garden.tree)) (Mu : GBranch D.T1.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (Cm : ℝ) (hm : ∀ K, ‖capMF S ω F M Fu Mu ind K‖ ≤ Cm)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) :
    ∃ (w : (Fin 2 → ℤ) → ℝ) (u : (Fin 2 → ℤ) → ℂ), (∀ m, 0 ≤ w m) ∧ Summable w ∧ (∀ m, ‖u m‖ ≤ 1) ∧
      (∀ x ∈ Icc (p : ℝ) (p + 1), HasSum (fun m => (w m : ℂ) * u m * fsPhase m ![x, p])
        (capCfgKer P.L P.γ P.δ D H1 (capMF S ω F M Fu Mu ind) cfg s t k₀ x)) ∧
      ∑' m, maxBracketPow θ (half m) * ENNReal.ofReal (w m) ≤
        C * (2 * ((∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ cL) *
          regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B))) := by
  have hH : ∀ ℓ ∈ inputLeaves D.T1.garden, Summable fun n : Fin P.d → ℤ => |H1 ℓ.1 (k₀ + latticePoint P.L n)| :=
    hLC.summable_coset hd hL k₀
  have hbox : cfg.box X t p p = timeBoxGt p p := by
    unfold ProtCfg.box; rw [hroot]; rfl
  have hx := capF_xnorm hD3 D hp hn hshape hsz cfg hv hcfg hamb hθ hps hst htp S ω cω hpres F M hM Fu Mu hMu ind
    hind H1 B hLC k₀
  rw [hbox] at hx
  refine capSup_of_xnorm hθ0 hC p _ (continuous_capCfgKer P.L P.γ P.δ D H1 _ Cm hm cfg hcfg s t k₀ hH)
    (fun ts k => kernelProt P.L P.γ P.δ D.T1 H1 (capMF S ω F M Fu Mu ind)
      (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) k₀
    (fun ts => capCfgKer_port P.L P.γ P.δ D H1 _ cfg hcfg s t k₀ ts) _ ?_ hx
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) ?_)
    ENNReal.ofReal_ne_top
  · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  · unfold regBound; exact ENNReal.ofReal_ne_top

/-- **The pointwise bound at a root-pinning configuration**, with filters: the kernel at any clock `x ∈ [t, p + 1]`
is bounded by D3's bound (`θ = η`). -/
theorem capF_pointwise {P : WTParams} (hD3 : ProtBoundAt P) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hη : 0 ≤ P.η) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (cfg : ProtCfg) (hv : cfg.Valid X D.T1 p)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i)
    (hroot : cfg.pinsRoot X = true)
    (hamb : ProtAmbient p X D.T1) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch D.T1.garden.tree)) (M : GBranch D.T1.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch D.T1.garden.tree)) (Mu : GBranch D.T1.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (Cm : ℝ) (hm : ∀ K, ‖capMF S ω F M Fu Mu ind K‖ ≤ Cm)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) (x : ℝ) (hx : x ∈ Icc t (p + 1)) :
    ‖capCfgKer P.L P.γ P.δ D H1 (capMF S ω F M Fu Mu ind) cfg s t k₀ x‖ₑ ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
        regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B) := by
  have hH : ∀ ℓ ∈ inputLeaves D.T1.garden, Summable fun n : Fin P.d → ℤ => |H1 ℓ.1 (k₀ + latticePoint P.L n)| :=
    hLC.summable_coset hd hL k₀
  have hbox : cfg.box X t p p = {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p p ∧ t ≤ ts 0} := by
    unfold ProtCfg.box; simp only [hroot, ↓reduceIte]
  have hxn := capF_xnorm hD3 D hp hn hshape hsz cfg hv hcfg hamb (Or.inl ⟨rfl, rfl⟩) hps hst htp S ω cω hpres
    F M hM Fu Mu hMu ind hind H1 B hLC k₀
  rw [hbox] at hxn
  set G : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => kernelProt P.L P.γ P.δ D.T1 H1
    (capMF S ω F M Fu Mu ind) (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0
  have hFG : ∀ ts, G ts k₀ = capCfgKer P.L P.γ P.δ D H1 (capMF S ω F M Fu Mu ind) cfg s t k₀ (ts 0) :=
    fun ts => capCfgKer_port P.L P.γ P.δ D H1 _ cfg hcfg s t k₀ ts
  have hcont := continuous_capCfgKer P.L P.γ P.δ D H1 _ Cm hm cfg hcfg s t k₀ hH
  have hFc : ∀ k ∈ ({k₀} : Set (Mom P.d)), ContinuousOn (fun ts => G ts k)
      {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p p ∧ t ≤ ts 0} := by
    intro k hk
    rw [Set.mem_singleton_iff.1 hk]
    simp only [hFG]
    exact (hcont.comp (continuous_apply 0)).continuousOn
  have hpt : (p : ℝ) < t := hps.trans hst
  have hmem : (![x, p] : Fin 2 → ℝ) ∈ {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p p ∧ t ≤ ts 0} :=
    ⟨mem_timeBoxGt_seg ⟨lt_of_lt_of_le hpt hx.1, hx.2⟩, by simpa using hx.1⟩
  have hfin : (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
      regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B) ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) ?_)
      ENNReal.ofReal_ne_top
    · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
    · unfold regBound; exact ENNReal.ofReal_ne_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hlt := lt_of_le_of_lt hxn (ENNReal.lt_add_right hfin (ENNReal.coe_ne_zero.mpr hε.ne'))
  obtain ⟨-, -, -, -, hb⟩ := exists_continuous_version (Λ := 30 * P.d) hη
    (cutBox_subset_closure_interior p t htp hpt) hFc hlt
  have := hb _ hmem k₀ rfl
  rw [hFG] at this
  simpa using this.le

/-! ### D6 at `term` with one selected chain vertex -/

/-- **D6 at `term` with one selected chain vertex `v`**, on the window box, at one momentum. -/
theorem capA_xnorm {P : WTParams} (hD6 : ProtAnnBoundAt P) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (hX : X.lonePath ≠ []) (v : GBranch D.T1.garden.tree) (hv1 : v.1.2 <+: X.lonePath) (hv2 : v.1.2 ≠ X.lonePath)
    (hv3 : v.1.2 ≠ X.lonePath.dropLast) (hamb : ProtAmbient p X D.T1) (M₂ : ℝ) (hM₂ : P.L ≤ M₂)
    {s t : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (hlone : ∀ a : GNode D.T1.garden.tree, a.1.2 = X.lonePath → D.T1.layer a = p)
    (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch D.T1.garden.tree)) (M : GBranch D.T1.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch D.T1.garden.tree)) (Mu : GBranch D.T1.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) :
    XNormRestr P.η (30 * P.d) 0 (timeBoxGt p p) {k₀}
      (fun ts k => kernelProt P.L P.γ P.δ D.T1 H1 (capMA S ω F M {v} M₂ Fu Mu ind)
        (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) *
        ENNReal.ofReal (P.L ^ ((47 * P.d + 5) * 2) * M₂ ^ (-((1 : ℝ) / 18))) *
        regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B) := by
  have hSel : ∀ b ∈ ({v} : Finset (GBranch D.T1.garden.tree)), b.1.1.val = 0 ∧ b.1.2 <+: X.lonePath ∧
      b.1.2 ≠ X.lonePath ∧ (true = true → b.1.2 ≠ X.lonePath.dropLast) := by
    intro b hb
    rw [Finset.mem_singleton.1 hb]
    exact ⟨Fin.val_eq_zero _, hv1, hv2, fun _ => hv3⟩
  have key := hD6 p hp n hn 1 D.T1 X hshape hsz true {v} (fun _ => hX) hSel (by simp) (by simp) hamb M₂ hM₂ s
    hps hsp p le_rfl (fun _ => hlone) S ω cω hpres F M hM Fu Mu hMu ind hind (fun h => absurd h (by simp)) H1 B hLC
    k₀ k₀
  have hk : ({k₀} : Set (Mom P.d)) ⊆ latticeBall P.L k₀ k₀ := by
    intro k hk
    rw [Set.mem_singleton_iff.1 hk]
    exact ⟨by simp, 0, by simp [WaveTurbulence.Links.latticePoint_zero]⟩
  refine (xnormRestr_anti_out _ _ _ _ hk _).trans (le_of_eq_of_le ?_ (key.trans (le_of_eq ?_)))
  · rfl
  · simp

/-- **The superposition of a `term` cap couple with one selected chain vertex**, from D6. -/
theorem capA_sup {P : WTParams} (hD6 : ProtAnnBoundAt P) {C : ℝ≥0∞} (hC : CapSupProp P.d P.η C)
    (hη : 0 ≤ P.η) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (hX : X.lonePath ≠ []) (v : GBranch D.T1.garden.tree) (hv1 : v.1.2 <+: X.lonePath) (hv2 : v.1.2 ≠ X.lonePath)
    (hv3 : v.1.2 ≠ X.lonePath.dropLast) (hamb : ProtAmbient p X D.T1) (M₂ : ℝ) (hM₂ : P.L ≤ M₂)
    {s t : ℝ} (hps : (p : ℝ) < s) (hsp : s < p + 1)
    (hlone : ∀ a : GNode D.T1.garden.tree, a.1.2 = X.lonePath → D.T1.layer a = p)
    (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (F : Finset (GBranch D.T1.garden.tree)) (M : GBranch D.T1.garden.tree → ℝ) (hM : ∀ b ∈ F, P.L ≤ M b)
    (Fu : Finset (GBranch D.T1.garden.tree)) (Mu : GBranch D.T1.garden.tree → ℝ) (hMu : ∀ b ∈ Fu, P.L ≤ Mu b)
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (Cm : ℝ) (hm : ∀ K, ‖capMA S ω F M {v} M₂ Fu Mu ind K‖ ≤ Cm)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) :
    ∃ (w : (Fin 2 → ℤ) → ℝ) (u : (Fin 2 → ℤ) → ℂ), (∀ m, 0 ≤ w m) ∧ Summable w ∧ (∀ m, ‖u m‖ ≤ 1) ∧
      (∀ x ∈ Icc (p : ℝ) (p + 1), HasSum (fun m => (w m : ℂ) * u m * fsPhase m ![x, p])
        (capCfgKer P.L P.γ P.δ D H1 (capMA S ω F M {v} M₂ Fu Mu ind) .term s t k₀ x)) ∧
      ∑' m, maxBracketPow P.η (half m) * ENNReal.ofReal (w m) ≤
        C * (2 * ((∏ a ∈ S, ENNReal.ofReal (cω a)) *
          ENNReal.ofReal (P.L ^ ((47 * P.d + 5) * 2) * M₂ ^ (-((1 : ℝ) / 18))) *
          regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B))) := by
  have hH : ∀ ℓ ∈ inputLeaves D.T1.garden, Summable fun n : Fin P.d → ℤ => |H1 ℓ.1 (k₀ + latticePoint P.L n)| :=
    hLC.summable_coset hd hL k₀
  have hcfg : ProtCfg.term = .term ∨ ProtCfg.term = .rootTerm ∨ ProtCfg.term = .penTerm ∨
      ∃ i, ProtCfg.term = .termChild i := Or.inl rfl
  have hx := capA_xnorm hD6 D hp hn hshape hsz hX v hv1 hv2 hv3 hamb M₂ hM₂ (t := t) hps hsp hlone S ω cω hpres
    F M hM Fu Mu hMu ind hind H1 B hLC k₀
  refine capSup_of_xnorm hη hC p _ (continuous_capCfgKer P.L P.γ P.δ D H1 _ Cm hm .term hcfg s t k₀ hH)
    (fun ts k => kernelProt P.L P.γ P.δ D.T1 H1 (capMA S ω F M {v} M₂ Fu Mu ind)
      (fun _ => ts 0) (ts 1) (ProtCfg.term.fix X s t (ts 0)) k (fun _ => 0) 0) k₀
    (fun ts => capCfgKer_port P.L P.γ P.δ D H1 _ .term hcfg s t k₀ ts) _ ?_ hx
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) ?_)
    ENNReal.ofReal_ne_top
  · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  · unfold regBound; exact ENNReal.ofReal_ne_top

end WaveTurbulence.Flower.MkSlotsO
