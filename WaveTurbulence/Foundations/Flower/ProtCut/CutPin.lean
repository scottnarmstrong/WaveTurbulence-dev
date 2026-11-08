/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CheckP3

/-! # D2c-2 PROT-CUT: the terminal cut with designations inside the pieces (time level)

`X = appendChain Xp (pair m Qr Qg inner nil)`. A designation `F` is **admissible** (`CutPinFix`) when it designates
the terminal node `𝔫_b` at `s` and every designation of `F` is at time `s` at a node strictly below `𝔫_a`
(inside the interior, the side couples, or `𝔫_b`). Then (o104 (P5), (P7); o73 (13.1) for `F = termFix`):

`protTime_cutPin`: the free-time integral is `∫_{u ∈ cutU} (phases at u, s) · prefix(T, u) · interior(u, s) ·
Qr(u, s) · Qg(u, s) du`, where the interior and side-couple pieces carry the pulled-back designations
`F ∘ βI`, `F ∘ βR`, `F ∘ βG`.

The new step is the vanishing for `u ≤ s` (`protTime_pin_zero`): the chain child of `𝔫_a` is either designated at `s`
(then `s < u` is a pin constraint) or free with a designated descendant at time `s`, hence later than `s`
(`lt_of_free_above_pin`) and earlier than `u`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **Admissible designations for the generalized terminal cut**: `𝔫_b` at `s`; every designation at `s`, at a node
strictly below `𝔫_a` (paths `Xp.lonePath ++ q`, `q ≠ []`). -/
structure CutPinFix (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (s : ℝ) {T : Fin 1 → TTree}
    (F : GBranch T → Option ℝ) : Prop where
  term : ∀ b : GBranch T, b.1.2 = Xp.lonePath ++ bPath m inner → F b = some s
  below : ∀ b σ, F b = some σ → σ = s ∧ ∃ q : Path, q ≠ [] ∧ b.1.2 = Xp.lonePath ++ q

theorem termFix_cutPinFix (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (s : ℝ) {T : Fin 1 → TTree} :
    CutPinFix Xp m inner s (termFix Xp m inner s : GBranch T → Option ℝ) := by
  refine ⟨fun b hb => by simp [termFix, hb], fun b σ h => ?_⟩
  unfold termFix at h
  split_ifs at h with hb
  exact ⟨(Option.some.inj h).symm, bPath m inner, bPath_ne_nil m inner, hb⟩

/-- A strict prefix of the path of a branching node is a branching node. -/
theorem mem_branching_of_strict_prefix {w : ℕ} {T : Fin w → TTree} (b0 : GBranch T) (p q : Path) (hq : q ≠ [])
    (h : b0.1.2 = p ++ q) : p ∈ (T b0.1.1).branching := by
  obtain ⟨x, r, rfl⟩ := List.exists_cons_of_ne_nil hq
  have hb := b0.2
  rw [h] at hb
  exact TTree.branching_of_append_mem _ (i := x) (TTree.mem_nodes_of_prefix _ (TTree.branching_subset_nodes _ hb)
    ⟨r, by simp⟩)

/-- **Lower-clock propagation to a designation**: a free branch `a` above a designated branch `b0`, all of whose
designations on the way down to `b0` are at times `≥ s`, is later than `s`. -/
theorem lt_of_free_above_pin {w : ℕ} {T : Fin w → TTree} (fix : GBranch T → Option ℝ) (τ : GBranch T → ℝ) (s : ℝ)
    (hchild : ∀ b b' : GBranch T, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b)
    (hpin : ∀ b v, fix b = some v → τ b = v) (b0 : GBranch T) (hb0 : fix b0 ≠ none) :
    ∀ (n : ℕ) (a : GBranch T) (q : Path), a.1.1 = b0.1.1 → b0.1.2 = a.1.2 ++ q → q.length = n + 1 →
      fix a = none →
      (∀ c : GBranch T, ∀ v, c.1.1 = a.1.1 → a.1.2 <+: c.1.2 → c.1.2 <+: b0.1.2 → fix c = some v → s ≤ v) →
      s < τ a := by
  intro n
  induction n with
  | zero =>
    intro a q h1 h2 h3 hfa hs
    obtain ⟨i, rfl⟩ : ∃ i, q = [i] := by
      match q, h3 with
      | [i], _ => exact ⟨i, rfl⟩
    have hc : b0.IsChildOf a := ⟨h1.symm, i, h2⟩
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hb0
    have hsv := hs b0 v h1.symm ⟨[i], h2.symm⟩ (List.prefix_refl _) hv
    have hlt := hchild a b0 hc (Or.inr hfa)
    rw [hpin b0 v hv] at hlt
    linarith
  | succ n ih =>
    intro a q h1 h2 h3 hfa hs
    obtain ⟨i, q', rfl⟩ : ∃ i q', q = i :: q' := by
      match q, h3 with
      | i :: q', _ => exact ⟨i, q', rfl⟩
    have hq' : q'.length = n + 1 := by simpa using h3
    have hq'ne : q' ≠ [] := fun h => by rw [h] at hq'; simp at hq'
    have hmem : a.1.2 ++ [i] ∈ (T a.1.1).branching := by
      have := mem_branching_of_strict_prefix b0 (a.1.2 ++ [i]) q' hq'ne (by rw [h2]; simp)
      rwa [← h1] at this
    let a' : GBranch T := ⟨(a.1.1, a.1.2 ++ [i]), hmem⟩
    have hc : a'.IsChildOf a := ⟨rfl, i, rfl⟩
    have h2' : b0.1.2 = a'.1.2 ++ q' := by rw [h2]; simp [a']
    have hpre : a'.1.2 <+: b0.1.2 := ⟨q', h2'.symm⟩
    have hlt := hchild a a' hc (Or.inr hfa)
    cases hfa' : fix a' with
    | some v =>
      have hsv := hs a' v rfl (List.prefix_append _ _) hpre hfa'
      rw [hpin a' v hfa'] at hlt
      linarith
    | none =>
      have := ih a' q' h1 h2' hq' hfa' (fun c v hc1 hc2 hc3 hcv =>
        hs c v hc1 ((List.prefix_append _ _).trans hc2) hc3 hcv)
      linarith

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}
variable (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
variable {s : ℝ} {F : GBranch LG.garden.tree → Option ℝ} (hF : CutPinFix Xp m inner s F)
include D hZ hsZ hF

theorem pin_aB : F (D.aB hZ hsZ) = none := by
  cases h : F (D.aB hZ hsZ) with
  | none => rfl
  | some σ =>
    obtain ⟨-, q, hq, hp⟩ := hF.below _ σ h
    rw [show (D.aB hZ hsZ).1.2 = Xp.lonePath from congrArg Prod.snd (D.aB_path hZ hsZ)] at hp
    exact absurd (by simpa using hp) hq

theorem pin_bG : F (D.bG hZ hsZ) = some s :=
  hF.term _ (congrArg Prod.snd (D.bG_path hZ hsZ))

theorem pin_inl (x : GBranch LGp.garden.tree) : F ((D.gd hZ hsZ).ofSum (.inl x)) = none := by
  cases h : F ((D.gd hZ hsZ).ofSum (.inl x)) with
  | none => rfl
  | some σ =>
    obtain ⟨-, q, -, hp⟩ := hF.below _ σ h
    exact absurd ⟨q, hp.symm⟩ (D.top_not_prefix hZ hsZ x)

theorem pin_parent (b : GBranch LG.garden.tree) (hb : (D.aB hZ hsZ).IsChildOf b) : F b = none := by
  cases h : F b with
  | none => rfl
  | some σ =>
    obtain ⟨-, q, hq, hp⟩ := hF.below _ σ h
    obtain ⟨-, i, hi⟩ := hb
    have hi' : Xp.lonePath = b.1.2 ++ [i] := by
      rw [← hi]; exact (congrArg Prod.snd (D.aB_path hZ hsZ)).symm
    rw [hp] at hi'
    have := congrArg List.length hi'
    have hq0 : q.length ≠ 0 := fun h0 => hq (List.eq_nil_of_length_eq_zero h0)
    simp only [List.length_append, List.length_singleton] at this
    omega

omit hF in
theorem ofSum_inr_rootB : (D.gd hZ hsZ).ofSum (.inr (D.hp hZ hsZ).rootB) = D.aB hZ hsZ := rfl

theorem cutU_sub_pin (T s' : ℝ) : cutU LG Xp T s ⊆ pinSet LG (fun _ => T) s' F (D.aB hZ hsZ) := by
  rintro u ⟨h1, h2, h3, h4, h5⟩
  refine ⟨by rw [D.layer_aB]; exact h1, by rw [D.layer_aB]; exact h2, h3, h4, fun b' _ σ hσ => ?_,
    fun b hb σ hσ => ?_, fun hl => absurd hl (D.aB_not_lone hZ hsZ)⟩
  · rw [(hF.below b' σ hσ).1]; exact h5
  · rw [D.pin_parent hZ hsZ hF b hb] at hσ; simp at hσ

/-! ### The glue and pair steps -/

/-- **The glue step**: with `𝔫_a` designated at `u`, the (undesignated) prefix splits off. -/
theorem protTime_glueP (L γ δ : ℝ) {d : ℕ} (T s' u : ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s' (Function.update F (D.aB hZ hsZ) (some u)) K =
      protTime L γ δ LGp (fun _ => T) u (fun _ => none) (K ∘ (D.gd hZ hsZ).ι₁) *
        protTime L γ δ (D.LGZ hZ hsZ) (fun _ => T) s'
          (fun y => Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr y)))
          (K ∘ (D.gd hZ hsZ).ι₂) := by
  set fix := Function.update F (D.aB hZ hsZ) (some u)
  have hD := fun τ hτ => protDom_glue_pinned (LG₂ := D.LGZ hZ hsZ) (D.gd hZ hsZ) (fun _ => T) s' fix
    (D.hp hZ hsZ).rootB rfl u (Function.update_self _ _ _)
    (fun x => by rw [D.layP, ← layerAt_node]; rfl) (fun y => rfl) (D.hlone hZ hsZ) (D.hlone₁ hZ hsZ) τ hτ
  rw [protTime_glue L γ δ (LG₂ := D.LGZ hZ hsZ) (D.gd hZ hsZ) (fun _ => T) s' fix (fun _ => T) u
    (fun _ => T) s' K hD]
  congr 2
  funext x
  show Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inl x)) = none
  rw [Function.update_of_ne, D.pin_inl hZ hsZ hF x]
  intro he
  have := (D.gd hZ hsZ).ofSum_injective he
  simp at this

omit hF in
theorem βi_ne_rootB (x : GBranch LGi.garden.tree) : (D.hp hZ hsZ).βi x ≠ (D.hp hZ hsZ).rootB := by
  intro he
  have := congrArg (fun b : GBranch GZ.tree => b.1.2) he
  simp [PairData.βi, PairData.rootB] at this

omit hF in
theorem βr_ne_rootB (y : GBranch LGr.garden.tree) : (D.hp hZ hsZ).βr y ≠ (D.hp hZ hsZ).rootB := by
  intro he
  have h2 : rBase m inner (GZ.sig 0) y.1.1 ++ y.1.2 = [] := congrArg (fun b : GBranch GZ.tree => b.1.2) he
  exact D.rBase_ne_nil hZ hsZ _ _ (List.append_eq_nil_iff.mp h2).1

omit hF in
theorem βg_ne_rootB (y : GBranch LGg.garden.tree) : (D.hp hZ hsZ).βg y ≠ (D.hp hZ hsZ).rootB := by
  intro he
  have h2 : gBase m inner (GZ.sig 0) y.1.1 ++ y.1.2 = [] := congrArg (fun b : GBranch GZ.tree => b.1.2) he
  exact D.gBase_ne_nil hZ hsZ _ _ (List.append_eq_nil_iff.mp h2).1

omit hF in
theorem upd_βi (u : ℝ) (x : GBranch LGi.garden.tree) :
    Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βi x))) = F (D.βI x) := by
  rw [Function.update_of_ne (D.ofSum_inr_ne_aB hZ hsZ _ (D.βi_ne_rootB hZ hsZ x)), D.ofSum_I hZ hsZ]

omit hF in
theorem upd_βr (u : ℝ) (y : GBranch LGr.garden.tree) :
    Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βr y))) = F (D.βR y) := by
  rw [Function.update_of_ne (D.ofSum_inr_ne_aB hZ hsZ _ (D.βr_ne_rootB hZ hsZ y)), D.ofSum_R hZ hsZ]

omit hF in
theorem upd_βg (u : ℝ) (y : GBranch LGg.garden.tree) :
    Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βg y))) = F (D.βG y) := by
  rw [Function.update_of_ne (D.ofSum_inr_ne_aB hZ hsZ _ (D.βg_ne_rootB hZ hsZ y)), D.ofSum_G hZ hsZ]

/-- **The pair step**, for `s ≤ u ≤ T`, with the designations of `F` inside the pieces. -/
theorem protTime_pairP (L γ δ : ℝ) {d : ℕ} (T s' u : ℝ) (hsu : s ≤ u) (huT : u ≤ T)
    (K : GNode GZ.tree → Mom d) :
    protTime L γ δ (D.LGZ hZ hsZ) (fun _ => T) s'
        (fun y => Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr y))) K =
      Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode GZ K (D.hp hZ hsZ).rootB * u : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode GZ K (D.hp hZ hsZ).bB * s : ℝ) * Complex.I) *
        (protTime L γ δ LGi (fun _ => u) s (fun x => F (D.βI x)) (K ∘ (D.hp hZ hsZ).ιi) *
          (protTime L γ δ LGr (fun y => cupR m inner (GZ.sig 0) u s y.1.1) 0 (fun y => F (D.βR y))
              (K ∘ (D.hp hZ hsZ).ιr) *
            protTime L γ δ LGg (fun y => cupG m inner (GZ.sig 0) u s y.1.1) 0 (fun y => F (D.βG y))
              (K ∘ (D.hp hZ hsZ).ιg))) := by
  have hfa : Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr (D.hp hZ hsZ).rootB)) = some u :=
    Function.update_self _ _ _
  have hfb : Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr (D.hp hZ hsZ).bB)) = some s := by
    rw [Function.update_of_ne (D.ofSum_inr_ne_aB hZ hsZ _ (D.bB_ne_rootB hZ hsZ))]
    exact D.pin_bG hZ hsZ hF
  have hle : ∀ σ, (∃ b, F b = some σ) → σ ≤ u := by
    rintro σ ⟨b, hb⟩
    rw [(hF.below b σ hb).1]; exact hsu
  have hleR : ∀ σ, (∃ b, F b = some σ) → ∀ j, σ ≤ cupR m inner (GZ.sig 0) u s j := by
    rintro σ ⟨b, hb⟩ j
    rw [(hF.below b σ hb).1]; unfold cupR; split_ifs <;> linarith
  have hleG : ∀ σ, (∃ b, F b = some σ) → ∀ j, σ ≤ cupG m inner (GZ.sig 0) u s j := by
    rintro σ ⟨b, hb⟩ j
    rw [(hF.below b σ hb).1]; unfold cupG; split_ifs <;> linarith
  have e := PairData.protTime_pair (LG := D.LGZ hZ hsZ) (D.hp hZ hsZ) L γ δ T s' u s
    (fun y => Function.update F (D.aB hZ hsZ) (some u) ((D.gd hZ hsZ).ofSum (.inr y))) hfa hfb
    (D.hli hZ hsZ) (D.hlr hZ hsZ) (D.hlg hZ hsZ) huT (hsu.trans huT)
    (fun x σ hx => by rw [D.upd_βi hZ hsZ] at hx; exact hle σ ⟨_, hx⟩)
    (fun y σ hy => by rw [D.upd_βr hZ hsZ] at hy; exact hleR σ ⟨_, hy⟩ _)
    (fun y σ hy => by rw [D.upd_βg hZ hsZ] at hy; exact hleG σ ⟨_, hy⟩ _) K
  have fi : (fun x => Function.update F (D.aB hZ hsZ) (some u)
      ((D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βi x)))) = fun x => F (D.βI x) :=
    funext (D.upd_βi hZ hsZ u)
  have fr : (fun y => Function.update F (D.aB hZ hsZ) (some u)
      ((D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βr y)))) = fun y => F (D.βR y) :=
    funext (D.upd_βr hZ hsZ u)
  have fg : (fun y => Function.update F (D.aB hZ hsZ) (some u)
      ((D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βg y)))) = fun y => F (D.βG y) :=
    funext (D.upd_βg hZ hsZ u)
  rw [fi, fr, fg] at e
  exact e

/-! ### Vanishing below `s` -/

/-- **The pin constraints force `s < u`**: the chain child of `𝔫_a` is designated at `s` (then `s < u` is a pin
constraint) or free above the designated `𝔫_b` (then later than `s`, earlier than `u`). -/
theorem lt_of_mem_protDom_pin (T s' u : ℝ) (hP : u ∈ pinSet LG (fun _ => T) s' F (D.aB hZ hsZ))
    (τ : GBranch LG.garden.tree → ℝ)
    (hτ : ∀ b v, Function.update F (D.aB hZ hsZ) (some u) b = some v → τ b = v)
    (hmem : τ ∈ protDom LG (fun _ => T) s' (Function.update F (D.aB hZ hsZ) (some u))) : s < u := by
  have hpath_a : (D.aB hZ hsZ).1.2 = Xp.lonePath := congrArg Prod.snd (D.aB_path hZ hsZ)
  have hpath_b : (D.bG hZ hsZ).1.2 = Xp.lonePath ++ bPath m inner := congrArg Prod.snd (D.bG_path hZ hsZ)
  by_cases hin : inner.lonePath = []
  · -- `𝔫_b` is the chain child of `𝔫_a`
    have hchild : (D.bG hZ hsZ).IsChildOf (D.aB hZ hsZ) := by
      refine ⟨Subsingleton.elim _ _, m.c, ?_⟩
      rw [hpath_b, hpath_a]
      simp [bPath, hin]
    exact hP.2.2.2.2.1 _ hchild s (D.pin_bG hZ hsZ hF)
  have hchildD : ∀ b b' : GBranch LG.garden.tree, b'.IsChildOf b →
      (Function.update F (D.aB hZ hsZ) (some u) b' = none ∨ Function.update F (D.aB hZ hsZ) (some u) b = none) →
      τ b' < τ b := fun b b' hc hor => (hmem.1 b).2 b' hc hor
  -- the chain child `c` of `𝔫_a` (the interior root)
  have hcmem := mem_branching_of_strict_prefix (D.bG hZ hsZ) (Xp.lonePath ++ [m.c]) inner.lonePath hin
    (by rw [hpath_b]; simp [bPath])
  let c : GBranch LG.garden.tree := ⟨((D.bG hZ hsZ).1.1, Xp.lonePath ++ [m.c]), hcmem⟩
  have hca : c.IsChildOf (D.aB hZ hsZ) := ⟨Subsingleton.elim _ _, m.c, by rw [hpath_a]⟩
  have hca_ne : c ≠ D.aB hZ hsZ := isChildOf_ne hca
  cases hfc : F c with
  | some v =>
    have h1 := hP.2.2.2.2.1 c hca v hfc
    rwa [(hF.below c v hfc).1] at h1
  | none =>
    have hfc' : Function.update F (D.aB hZ hsZ) (some u) c = none := by
      rw [Function.update_of_ne hca_ne]; exact hfc
    have hfb' : Function.update F (D.aB hZ hsZ) (some u) (D.bG hZ hsZ) ≠ none := by
      have hne : D.bG hZ hsZ ≠ D.aB hZ hsZ := D.ofSum_inr_ne_aB hZ hsZ _ (D.bB_ne_rootB hZ hsZ)
      rw [Function.update_of_ne hne, D.pin_bG hZ hsZ hF]
      simp
    obtain ⟨n, hn⟩ : ∃ n, inner.lonePath.length = n + 1 :=
      Nat.exists_eq_succ_of_ne_zero (fun h => hin (List.eq_nil_of_length_eq_zero h))
    have hlt := lt_of_free_above_pin (Function.update F (D.aB hZ hsZ) (some u)) τ s hchildD hτ (D.bG hZ hsZ) hfb'
      n c inner.lonePath rfl (by rw [hpath_b]; simp [c, bPath]) hn hfc' (fun c' v _ hc2 _ hcv => by
        have hne : c' ≠ D.aB hZ hsZ := by
          intro he
          have h4 := congrArg List.length (congrArg (fun b : GBranch LG.garden.tree => b.1.2) he)
          obtain ⟨r, hr⟩ := hc2
          have h3 := congrArg List.length hr
          simp only [hpath_a] at h4
          simp only [c, List.length_append, List.length_singleton] at h3
          omega
        rw [Function.update_of_ne hne] at hcv
        exact (hF.below c' v hcv).1.ge)
    have hcu : τ c < τ (D.aB hZ hsZ) := hchildD _ _ hca (Or.inl hfc')
    rw [hτ _ _ (Function.update_self _ _ _)] at hcu
    linarith

/-- **Vanishing for `u ≤ s`.** -/
theorem protTime_pin_zero (L γ δ : ℝ) {d : ℕ} (T s' u : ℝ)
    (hP : u ∈ pinSet LG (fun _ => T) s' F (D.aB hZ hsZ)) (hus : u ≤ s) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s' (Function.update F (D.aB hZ hsZ) (some u)) K = 0 := by
  unfold protTime
  refine (integral_congr_ae (Filter.Eventually.of_forall fun σ => ?_)).trans (integral_zero _ _)
  refine Set.indicator_of_notMem (fun hmem => ?_) _
  exact absurd (D.lt_of_mem_protDom_pin hZ hsZ hF T s' u hP _ (fun b v hv => extendFix_some _ _ _ hv) hmem)
    (not_lt.mpr hus)

/-! ### The generalized terminal cut -/

/-- **The terminal cut with designations inside the pieces** (o73 (13.1); o104 (P5), (P7), time level). -/
theorem protTime_cutPin (L γ δ : ℝ) {d : ℕ} (T s' : ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s' F K =
      ∫ u in cutU LG Xp T s,
        Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode GZ (K ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).rootB * u : ℝ) * Complex.I) *
          Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode GZ (K ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).bB * s : ℝ) * Complex.I) *
        (protTime L γ δ LGp (fun _ => T) u (fun _ => none) (K ∘ (D.gd hZ hsZ).ι₁) *
          (protTime L γ δ LGi (fun _ => u) s (fun x => F (D.βI x)) (K ∘ (D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιi) *
            (protTime L γ δ LGr (fun y => cupR m inner (GZ.sig 0) u s y.1.1) 0 (fun y => F (D.βR y))
                (K ∘ (D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιr) *
              protTime L γ δ LGg (fun y => cupG m inner (GZ.sig 0) u s y.1.1) 0 (fun y => F (D.βG y))
                (K ∘ (D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιg)))) := by
  rw [protTime_pin L γ δ LG (fun _ => T) s' F K (D.aB hZ hsZ) (D.pin_aB hZ hsZ hF),
    ← integral_indicator (measurableSet_cutU LG Xp T s)]
  congr 1
  funext u
  by_cases hU : u ∈ cutU LG Xp T s
  · rw [Set.indicator_of_mem (D.cutU_sub_pin hZ hsZ hF T s' hU), Set.indicator_of_mem hU]
    beta_reduce
    rw [D.protTime_glueP hZ hsZ hF L γ δ T s' u K,
      D.protTime_pairP hZ hsZ hF L γ δ T s' u hU.2.2.2.2.le hU.2.2.2.1.le]
    simp only [Function.comp_assoc]
    ring
  · rw [Set.indicator_of_notMem hU]
    by_cases hP : u ∈ pinSet LG (fun _ => T) s' F (D.aB hZ hsZ)
    · rw [Set.indicator_of_mem hP]
      have hus : u ≤ s := by
        by_contra hlt
        exact hU ⟨by rw [← D.layer_aB]; exact hP.1, by rw [← D.layer_aB]; exact hP.2.1, hP.2.2.1,
          hP.2.2.2.1, lt_of_not_ge hlt⟩
      exact D.protTime_pin_zero hZ hsZ hF L γ δ T s' u hP hus K
    · rw [Set.indicator_of_notMem hP]

end CutTermData

end WaveTurbulence.Flower.ProtCut
