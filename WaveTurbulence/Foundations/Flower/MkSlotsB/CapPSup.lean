/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsB.CapPKer

/-! # B3s-HELPER3 (B5): D3 for every pattern configuration of a cap couple

The twin of B3s's `CapD3` for the configurations of D2b's `objCfg` on a cap couple (`term`, `termChild i`, `penTerm`,
`rootTerm`), from D3's full `ProtBoundAt`:
* `capCfg_xnorm`: D3's bound on `cfg.box` (R176);
* `capCfg_sup`: if `cfg` does not pin the root (`cfg.box = timeBoxGt p p`), the superposition on the window
  `[p, p + 1]` (B3s's `capSup_of_xnorm`);
* `kernelProt_up_const`: if every root is pinned and every pinned value is `≤ v₀`, the protected kernel does not
  depend on the upper clock `x ≥ v₀` (a free branch lies below its first pinned ancestor);
* `capCfg_pointwise`: if `cfg` pins the root, the value at any clock `x ≥ t` is bounded by D3's bound (pointwise
  value of a continuous function ≤ its restricted `X`-norm on the cut box). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped ENNReal
open MeasureTheory Set
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtWhole WaveTurbulence.Flower.ProtCut
  WaveTurbulence.Flower.MkSlots

namespace WaveTurbulence.Flower.MkSlotsB

/-! ### The kernel does not see the upper clock above the pins (every root pinned) -/

section Const

variable {w d : ℕ}

/-- A free branch lies strictly below the largest pinned value when every root is pinned (induction on depth). -/
theorem free_below_pins (LG : LayeredGarden w) (fix : GBranch LG.garden.tree → Option ℝ) (v₀ : ℝ)
    (hroot : ∀ b : GBranch LG.garden.tree, b.1.2 = [] → fix b ≠ none)
    (hval : ∀ b v, fix b = some v → v ≤ v₀) (τ : GBranch LG.garden.tree → ℝ)
    (hpin : ∀ b v, fix b = some v → τ b = v)
    (hedge : ∀ b b' : GBranch LG.garden.tree, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b) :
    ∀ (n : ℕ) (b : GBranch LG.garden.tree), b.1.2.length = n → fix b = none → τ b < v₀ := by
  intro n
  induction n with
  | zero =>
    intro b hn hb
    exact absurd hb (hroot b (List.length_eq_zero_iff.mp hn))
  | succ n ih =>
    intro b hn hb
    have hne : b.1.2 ≠ [] := fun h => by rw [h] at hn; simp at hn
    obtain ⟨par, hpar⟩ := exists_parent_branch b hne
    have hlen : par.1.2.length = n := by
      obtain ⟨-, i, hi⟩ := hpar
      have := congrArg List.length hi
      simp only [List.length_append, List.length_singleton] at this
      omega
    have h1 := hedge par b hpar (Or.inl hb)
    by_cases hp : fix par = none
    · exact h1.trans (ih par hlen hp)
    · obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hp
      rw [hpin par v hv] at h1
      exact lt_of_lt_of_le h1 (hval par v hv)

/-- **The protected kernel does not depend on the upper clock above the pins** (every root pinned, pinned values
`≤ v₀`). -/
theorem kernelProt_up_const (L γ δ : ℝ) (LG : LayeredGarden w) (H : LeafProfiles w d)
    (m : (GNode LG.garden.tree → Mom d) → ℂ) (s' : ℝ) (fix : GBranch LG.garden.tree → Option ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) (v₀ : ℝ)
    (hroot : ∀ b : GBranch LG.garden.tree, b.1.2 = [] → fix b ≠ none)
    (hval : ∀ b v, fix b = some v → v ≤ v₀) (x x' : ℝ) (hx : v₀ ≤ x) (hx' : v₀ ≤ x') :
    kernelProt L γ δ LG H m (fun _ => x) s' fix k₀ nroot nfl =
      kernelProt L γ δ LG H m (fun _ => x') s' fix k₀ nroot nfl := by
  have key : ∀ (y : ℝ), v₀ ≤ y → ∀ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
      LG.garden.extendFix fix τ ∈ kDomainFix LG (fun _ => y) fix ↔
        ∀ b, (fix b = none → (LG.layer b.toNode : ℝ) < LG.garden.extendFix fix τ b ∧
          LG.garden.extendFix fix τ b < LG.layer b.toNode + 1 ∧ 0 < LG.garden.extendFix fix τ b) ∧
          ∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → (fix b' = none ∨ fix b = none) →
            LG.garden.extendFix fix τ b' < LG.garden.extendFix fix τ b := by
    intro y hy τ
    set T := LG.garden.extendFix fix τ
    have hpin : ∀ b v, fix b = some v → T b = v := fun b v hb => by
      show LG.garden.extendFix fix τ b = v
      rw [capExtendFix_eq]; exact extendFixI_some fix τ hb
    constructor
    · intro h b
      exact ⟨fun hb => ⟨((h b).1 hb).1, ((h b).1 hb).2.1, ((h b).1 hb).2.2.1⟩, (h b).2⟩
    · intro h b
      refine ⟨fun hb => ⟨(h b).1 hb |>.1, (h b).1 hb |>.2.1, (h b).1 hb |>.2.2, ?_⟩, (h b).2⟩
      have := free_below_pins LG fix v₀ hroot hval T hpin (fun b b' hbb' hf => (h b).2 b' hbb' hf) _ b rfl hb
      exact lt_of_lt_of_le this hy
  rw [kernelProt_eq_tsum, kernelProt_eq_tsum]
  congr 1
  refine tsum_congr fun κ => ?_
  unfold protSummand protTime protDom
  have hI : (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
      (kDomainFix LG (fun _ => x) fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s' < τ b}).indicator
        (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ)) =
      ∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
      (kDomainFix LG (fun _ => x') fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s' < τ b}).indicator
        (phaseProd L γ δ LG.garden (cosetDecoration LG.garden L k₀ κ.1)) (LG.garden.extendFix fix τ) := by
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    dsimp only
    have e : LG.garden.extendFix fix τ ∈ kDomainFix LG (fun _ => x) fix ↔
        LG.garden.extendFix fix τ ∈ kDomainFix LG (fun _ => x') fix := (key x hx τ).trans (key x' hx' τ).symm
    by_cases hA : LG.garden.extendFix fix τ ∈
        kDomainFix LG (fun _ => x) fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s' < τ b}
    · have hB : LG.garden.extendFix fix τ ∈
          kDomainFix LG (fun _ => x') fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s' < τ b} :=
        ⟨e.1 hA.1, hA.2⟩
      rw [Set.indicator_of_mem hA, Set.indicator_of_mem hB]
    · have hB : LG.garden.extendFix fix τ ∉
          kDomainFix LG (fun _ => x') fix ∩ {τ | ∀ b, LG.garden.IsLoneParent b → fix b = none → s' < τ b} :=
        fun h => hA ⟨e.2 h.1, h.2⟩
      rw [Set.indicator_of_notMem hA, Set.indicator_of_notMem hB]
  rw [hI]

end Const

/-! ### D3 for a pattern configuration of a cap couple -/

variable {LG : LayeredGarden 2} {j0 c : Fin 2} {X : RegChain} {ζ : ℤˣ}

/-- **D3 at a pattern configuration** on `cfg.box`, at one momentum. -/
theorem capCfg_xnorm {P : WTParams} (hD3 : ProtBoundAt P) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (cfg : ProtCfg) (hv : cfg.Valid X D.T1 p)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i)
    (hamb : ProtAmbient p X D.T1) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) :
    XNormRestr P.η (30 * P.d) 0 (cfg.box X t p p) {k₀}
      (fun ts k => kernelProt P.L P.γ P.δ D.T1 H1 (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ))
        (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
        regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B) := by
  have hnot : cfg = .none ∨ cfg = .root ∨ cfg = .trace → False := by
    rintro (h | h | h) <;> rcases hcfg with h' | h' | h' | ⟨i, h'⟩ <;> rw [h'] at h <;> exact absurd h (by simp)
  have key := hD3 p hp n hn 1 D.T1 X hshape hsz cfg hv hamb P.η (31 * P.d + 6)
    (Or.inl ⟨rfl, rfl⟩) s t hps hst htp p le_rfl S ω cω hpres ∅ (fun _ => P.L) (by simp) ∅ (fun _ => P.L)
    (by simp) ind hind (fun h => (hnot h).elim) H1 B hLC k₀ k₀
  have hk : ({k₀} : Set (Mom P.d)) ⊆ latticeBall P.L k₀ k₀ := by
    intro k hk
    rw [Set.mem_singleton_iff.1 hk]
    exact ⟨by simp, 0, by simp [WaveTurbulence.Links.latticePoint_zero]⟩
  refine (xnormRestr_anti_out _ _ _ _ hk _).trans (le_of_eq_of_le ?_ key)
  congr 1
  funext ts k
  congr 1
  funext κ
  simp [filtWeight_empty]

/-- The kernel of a pattern configuration at the upper clock `x`, with the lone port void. -/
def capCfgKer (L γ δ : ℝ) {d : ℕ} (D : CapG LG j0 c X ζ) (H1 : LeafProfiles 1 d)
    (m : (GNode D.T1.garden.tree → Mom d) → ℂ) (cfg : ProtCfg) (s t : ℝ) (k₀ : Mom d) (x : ℝ) : ℂ :=
  kernelProt L γ δ D.T1 H1 m (fun _ => x) 0 (cfg.fix X s t x) k₀ (fun _ => 0) 0

theorem capCfgKer_port (L γ δ : ℝ) {d : ℕ} (D : CapG LG j0 c X ζ) (H1 : LeafProfiles 1 d)
    (m : (GNode D.T1.garden.tree → Mom d) → ℂ) (cfg : ProtCfg)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i) (s t : ℝ) (k₀ : Mom d)
    (ts : Fin 2 → ℝ) :
    kernelProt L γ δ D.T1 H1 m (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k₀ (fun _ => 0) 0 =
      capCfgKer L γ δ D H1 m cfg s t k₀ (ts 0) :=
  kernelProt_port _ _ _ _ _ _ _ _ _ _ _ _ _ (D.lonePin cfg hcfg s t (ts 0))

theorem cfg_ne_trace (cfg : ProtCfg) (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i) :
    cfg ≠ .trace := by
  rcases hcfg with h | h | h | ⟨i, h⟩ <;> rw [h] <;> simp

theorem continuous_capCfgKer (L γ δ : ℝ) {d : ℕ} (D : CapG LG j0 c X ζ) (H1 : LeafProfiles 1 d)
    (m : (GNode D.T1.garden.tree → Mom d) → ℂ) (Cm : ℝ) (hm : ∀ K, ‖m K‖ ≤ Cm) (cfg : ProtCfg)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i) (s t : ℝ) (k₀ : Mom d)
    (hH : ∀ ℓ ∈ inputLeaves D.T1.garden, Summable fun n : Fin d → ℤ => |H1 ℓ.1 (k₀ + latticePoint L n)|) :
    Continuous (capCfgKer L γ δ D H1 m cfg s t k₀) := by
  have he : capCfgKer L γ δ D H1 m cfg s t k₀ =
      fun x => kernelProt L γ δ D.T1 H1 m (fun _ => x) 0 (cfg.fix X s t 0) k₀ (fun _ => 0) 0 := by
    funext x
    unfold capCfgKer
    rw [fix_up_indep cfg (cfg_ne_trace cfg hcfg) X s t x 0]
  rw [he]
  exact continuous_kernelProt_up L γ δ D.T1 H1 m Cm hm 0 _ k₀
    (PL234.card_lone_le_of_decodesTree (Reg.decodedTree_decodes X ζ)) hH

/-- **The superposition of a configuration that does not pin the root** on the window `[p, p + 1]`, from D3. -/
theorem capCfg_sup {P : WTParams} (hD3 : ProtBoundAt P) {C : ℝ≥0∞} (hC : CapSupProp P.d P.η C)
    (hη : 0 ≤ P.η) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (cfg : ProtCfg) (hv : cfg.Valid X D.T1 p)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i)
    (hroot : cfg.pinsRoot X = false)
    (hamb : ProtAmbient p X D.T1) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (Cm : ℝ) (hm : ∀ K, ‖IncTop.starWeight S ω K * (ind K : ℂ)‖ ≤ Cm)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) :
    ∃ (w : (Fin 2 → ℤ) → ℝ) (u : (Fin 2 → ℤ) → ℂ), (∀ m, 0 ≤ w m) ∧ Summable w ∧ (∀ m, ‖u m‖ ≤ 1) ∧
      (∀ x ∈ Icc (p : ℝ) (p + 1), HasSum (fun m => (w m : ℂ) * u m * fsPhase m ![x, p])
        (capCfgKer P.L P.γ P.δ D H1 (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ)) cfg s t k₀ x)) ∧
      ∑' m, maxBracketPow P.η (half m) * ENNReal.ofReal (w m) ≤
        C * (2 * ((∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
          regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B))) := by
  have hH : ∀ ℓ ∈ inputLeaves D.T1.garden, Summable fun n : Fin P.d → ℤ => |H1 ℓ.1 (k₀ + latticePoint P.L n)| :=
    hLC.summable_coset hd hL k₀
  have hbox : cfg.box X t p p = timeBoxGt p p := by
    unfold ProtCfg.box; rw [hroot]; rfl
  have hx := capCfg_xnorm hD3 D hp hn hshape hsz cfg hv hcfg hamb hps hst htp S ω cω hpres ind hind H1 B hLC k₀
  rw [hbox] at hx
  refine capSup_of_xnorm hη hC p _ (continuous_capCfgKer P.L P.γ P.δ D H1 _ Cm hm cfg hcfg s t k₀ hH)
    (fun ts k => kernelProt P.L P.γ P.δ D.T1 H1 (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ))
      (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) k₀
    (fun ts => capCfgKer_port P.L P.γ P.δ D H1 _ cfg hcfg s t k₀ ts) _ ?_ hx
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top) ?_)
    ENNReal.ofReal_ne_top
  · exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  · unfold regBound; exact ENNReal.ofReal_ne_top

/-! ### Configurations that pin the root: a pointwise bound on the cut box -/

theorem convex_cutBox (p t : ℝ) : Convex ℝ {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p p ∧ t ≤ ts 0} := by
  have h2 : Convex ℝ {ts : Fin 2 → ℝ | t ≤ ts 0} := by
    intro x hx y hy a b ha hb hab
    show t ≤ a * x 0 + b * y 0
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [show t ≤ x 0 from hx, show t ≤ y 0 from hy]
  exact (convex_timeBoxGt p p).inter h2

theorem cutBox_subset_closure_interior (p t : ℝ) (htp : t < p + 1) (hpt : p < t) :
    {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p p ∧ t ≤ ts 0} ⊆
      closure (interior {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p p ∧ t ≤ ts 0}) := by
  set B := {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p p ∧ t ≤ ts 0}
  have hne : (interior B).Nonempty := by
    let U : Set (Fin 2 → ℝ) := {ts | (p : ℝ) < ts 1 ∧ ts 1 < ts 0 ∧ ts 0 < p + 1 ∧ t < ts 0}
    have hUo : IsOpen U := by
      simp only [U, Set.ofPred_and]
      exact (isOpen_lt continuous_const (continuous_apply 1)).inter ((isOpen_lt (continuous_apply 1)
        (continuous_apply 0)).inter ((isOpen_lt (continuous_apply 0) continuous_const).inter
          (isOpen_lt continuous_const (continuous_apply 0))))
    have hUsub : U ⊆ B := by
      rintro ts ⟨h1, h2, h3, h4⟩
      exact ⟨⟨⟨⟨by linarith, h3.le⟩, ⟨h1.le, by linarith⟩⟩, h2⟩, h4.le⟩
    refine ⟨![(t + (p + 1)) / 2, (p + t) / 2 - (t - p) / 4], interior_maximal hUsub hUo ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> linarith
  rw [(convex_cutBox p t).closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

/-- **The pointwise bound at a root-pinning configuration**: the kernel at any clock `x ∈ [t, p + 1]` is bounded by
D3's bound. -/
theorem capCfg_pointwise {P : WTParams} (hD3 : ProtBoundAt P) (D : CapG LG j0 c X ζ) {p n : ℕ}
    (hη : 0 ≤ P.η) (hd : 1 ≤ P.d) (hL : 1 ≤ P.L)
    (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4) (hshape : ProtShape p X D.T1) (hsz : protSize X D.T1 = 2 * n)
    (cfg : ProtCfg) (hv : cfg.Valid X D.T1 p)
    (hcfg : cfg = .term ∨ cfg = .rootTerm ∨ cfg = .penTerm ∨ ∃ i, cfg = .termChild i)
    (hroot : cfg.pinsRoot X = true)
    (hamb : ProtAmbient p X D.T1) {s t : ℝ} (hps : (p : ℝ) < s) (hst : s < t)
    (htp : t < p + 1) (S : Finset (GNode D.T1.garden.tree)) (ω : GNode D.T1.garden.tree → IncTop.Star P.d → ℂ)
    (cω : GNode D.T1.garden.tree → ℝ) (hpres : ∀ a ∈ S, IncTop.StarPresented (30 * P.d) (ω a) (cω a))
    (ind : (GNode D.T1.garden.tree → Mom P.d) → ℝ) (hind : TermChildIndicator X ind)
    (Cm : ℝ) (hm : ∀ K, ‖IncTop.starWeight S ω K * (ind K : ℂ)‖ ≤ Cm)
    (H1 : LeafProfiles 1 P.d) (B : (Fin 1 × TTree.Path) → NNReal) (hLC : LeafwiseControlled D.T1 H1 B)
    (k₀ : Mom P.d) (x : ℝ) (hx : x ∈ Icc t (p + 1)) :
    ‖capCfgKer P.L P.γ P.δ D H1 (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ)) cfg s t k₀ x‖ₑ ≤
      (∏ a ∈ S, ENNReal.ofReal (cω a)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
        regBound P n (protIncoh X D.T1) * ENNReal.ofReal (leafSizeProduct D.T1 B) := by
  have hH : ∀ ℓ ∈ inputLeaves D.T1.garden, Summable fun n : Fin P.d → ℤ => |H1 ℓ.1 (k₀ + latticePoint P.L n)| :=
    hLC.summable_coset hd hL k₀
  have hbox : cfg.box X t p p = {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p p ∧ t ≤ ts 0} := by
    unfold ProtCfg.box; simp only [hroot, ↓reduceIte]
  have hxn := capCfg_xnorm hD3 D hp hn hshape hsz cfg hv hcfg hamb hps hst htp S ω cω hpres ind hind H1 B hLC k₀
  rw [hbox] at hxn
  set F : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => kernelProt P.L P.γ P.δ D.T1 H1
    (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ)) (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0
  have hFG : ∀ ts, F ts k₀ = capCfgKer P.L P.γ P.δ D H1 (fun κ => IncTop.starWeight S ω κ * (ind κ : ℂ)) cfg s t k₀ (ts 0) :=
    fun ts => capCfgKer_port P.L P.γ P.δ D H1 _ cfg hcfg s t k₀ ts
  have hcont := continuous_capCfgKer P.L P.γ P.δ D H1 _ Cm hm cfg hcfg s t k₀ hH
  have hFc : ∀ k ∈ ({k₀} : Set (Mom P.d)), ContinuousOn (fun ts => F ts k)
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

end WaveTurbulence.Flower.MkSlotsB
