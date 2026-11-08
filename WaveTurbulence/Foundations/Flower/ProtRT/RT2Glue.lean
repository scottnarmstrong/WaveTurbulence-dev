/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Root2Ker
public import WaveTurbulence.Foundations.Flower.MkSlotsO.RootTraceHyp

/-! # RT-GATE (ii), both roots pinned: D2c's type-2 root cut with the second root also pinned (time level)

D2c's `protDom_glue_free2` / `Root2Data.protTime_root2` (ProtCut/Root2.lean; copy recorded in RT2-COPIED.md) with the
root of tree `1` ALSO designated: the bottom couple `K_rest` then carries the pin of its tree-`1` root.
* `rt2_protDom_glue_pin2`: the glue of the time domain when the top node `p` is designated at `u ≤ U 0`, the bottom
  tree-`0` branches are free and the bottom tree-`1` pins lie below the clock `U 1`;
* **`rt2_protTime_root2`**: both roots designated at `σ` (`rootPins (fun _ => True) σ`), clocks `σ`:
  `protTime = ∫_{u ∈ root2U} Z(σ, u) · K_rest(clocks (u, σ), its tree-1 root at σ)`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtRT

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut

/-- **The glue of a couple with pins on the bottom tree `1`.** -/
theorem rt2_protDom_glue_pin2 {LG LG₂ : LayeredGarden 2} {LG₁ : LayeredGarden 1} {X : RegChain}
    (h : GlueData LG.garden LG₁.garden LG₂.garden X) (U : Fin 2 → ℝ) (s s₁ : ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ)
    (p : GBranch LG₁.garden.tree) (u : ℝ) (hfp : fix (h.ofSum (.inl p)) = some u)
    (hfree0 : ∀ y : GBranch LG₂.garden.tree, y.1.1 = 0 → fix (h.ofSum (.inr y)) = none)
    (hpinB : ∀ y v, fix (h.ofSum (.inr y)) = some v → v ≤ U y.1.1) (hu : u ≤ U 0)
    (hl₁ : ∀ x : GBranch LG₁.garden.tree, LG₁.layer x.toNode = LG.layer (h.ofSum (.inl x)).toNode)
    (hl₂ : ∀ y : GBranch LG₂.garden.tree, LG₂.layer y.toNode = LG.layer (h.ofSum (.inr y)).toNode)
    (hlone : ∀ b, LG.garden.IsLoneParent b ↔ ∃ y, b = h.ofSum (.inr y) ∧ LG₂.garden.IsLoneParent y)
    (hlone₁ : ∀ x : GBranch LG₁.garden.tree, LG₁.garden.IsLoneParent x → x = p)
    (hpar : ∀ (x : GBranch LG₁.garden.tree) (y : GBranch LG₂.garden.tree),
      (h.ofSum (.inr y)).IsChildOf (h.ofSum (.inl x)) → x = p)
    (hpar' : ∀ y : GBranch LG₂.garden.tree, y.1 = ((0 : Fin 2), []) →
      (h.ofSum (.inr y)).IsChildOf (h.ofSum (.inl p)))
    (τ : GBranch LG.garden.tree → ℝ) (hτ : ∀ b v, fix b = some v → τ b = v) :
    τ ∈ protDom LG (fun b => U b.1.1) s fix ↔
      (fun x => τ (h.ofSum (.inl x))) ∈ protDom LG₁ (fun _ => U 0) s₁ (fun x => fix (h.ofSum (.inl x))) ∧
        (fun y => τ (h.ofSum (.inr y))) ∈ protDom LG₂ (fun y => bClock U u y.1.1) s
          (fun y => fix (h.ofSum (.inr y))) := by
  have hτp : τ (h.ofSum (.inl p)) = u := hτ _ _ hfp
  have hfst : ∀ y : GBranch LG₂.garden.tree, (h.ofSum (.inr y)).1.1 = y.1.1 := fun y => botAddr_fst _ _
  constructor
  · rintro ⟨hD, hL⟩
    have hlt : ∀ y, (fun y => fix (h.ofSum (.inr y))) y = none → τ (h.ofSum (.inr y)) < bClock U u y.1.1 := by
      refine lt_up_of_chain (fun y => fix (h.ofSum (.inr y))) (fun y => τ (h.ofSum (.inr y))) (bClock U u)
        (fun y y' hc hor => (hD (h.ofSum (.inr y))).2 _ ((h.child_inr_inr y y').mpr hc) hor)
        (fun y hy hf => ?_) (fun y σ hf => ?_)
      · by_cases h0 : y.1.1 = 0
        · have hy0 : y.1 = ((0 : Fin 2), []) := Prod.ext h0 hy
          have := (hD (h.ofSum (.inl p))).2 _ (hpar' y hy0) (Or.inl hf)
          rw [hτp] at this
          unfold bClock; rw [if_pos h0]; exact this
        · have := ((hD (h.ofSum (.inr y))).1 hf).2.2.2
          unfold bClock; rw [if_neg h0]
          simp only [hfst] at this
          exact this
      · have h0 : y.1.1 ≠ 0 := fun h0 => by rw [hfree0 y h0] at hf; simp at hf
        refine ⟨hτ _ _ hf, ?_⟩
        unfold bClock; rw [if_neg h0]
        exact hpinB y σ hf
    refine ⟨⟨fun x => ⟨fun hx => ?_, fun x' hx' hor => ?_⟩, fun x hx hf => ?_⟩,
      ⟨fun y => ⟨fun hy => ?_, fun y' hy' hor => ?_⟩, fun y hy hf => ?_⟩⟩
    · have := (hD (h.ofSum (.inl x))).1 hx
      simp only [hl₁]; exact this
    · exact (hD (h.ofSum (.inl x))).2 _ ((h.child_inl_inl x x').mpr hx') hor
    · have := hlone₁ x hx
      subst this
      simp only [hfp] at hf
      exact absurd hf (by simp)
    · obtain ⟨a1, a2, a3, -⟩ := (hD (h.ofSum (.inr y))).1 hy
      simp only [hl₂]
      exact ⟨a1, a2, a3, hlt y hy⟩
    · exact (hD (h.ofSum (.inr y))).2 _ ((h.child_inr_inr y y').mpr hy') hor
    · exact hL _ ((hlone _).mpr ⟨y, rfl, hy⟩) hf
  · rintro ⟨⟨hD₁, hL₁⟩, ⟨hD₂, hL₂⟩⟩
    refine ⟨(h.forall_branch _).mpr ⟨fun x => ⟨fun hx => ?_, fun b' hb' hor => ?_⟩,
      fun y => ⟨fun hy => ?_, fun b' hb' hor => ?_⟩⟩, fun b hb hf => ?_⟩
    · have := (hD₁ x).1 hx
      simp only [hl₁] at this; exact this
    · rw [← h.ofSum_toSum b'] at hb' hor ⊢
      rcases hc : h.toSum b' with x' | y'
      · rw [hc] at hb' hor
        exact (hD₁ x).2 x' ((h.child_inl_inl x x').mp hb') hor
      · rw [hc] at hb' hor
        have hy0 := GlueFix.child_inr_inl h x y' hb'
        have hx := hpar x y' hb'
        subst hx
        rw [hτp]
        have h4 : τ (h.ofSum (.inr y')) < bClock U u y'.1.1 :=
          ((hD₂ y').1 (hfree0 y' (congrArg Prod.fst hy0 : y'.1.1 = 0))).2.2.2
        unfold bClock at h4
        rw [if_pos (congrArg Prod.fst hy0 : y'.1.1 = 0)] at h4
        exact h4
    · obtain ⟨a1, a2, a3, a4⟩ := (hD₂ y).1 hy
      simp only [hl₂] at a1 a2
      refine ⟨a1, a2, a3, a4.trans_le ?_⟩
      show bClock U u y.1.1 ≤ U (h.ofSum (.inr y)).1.1
      rw [hfst]
      unfold bClock
      split_ifs with h0
      · rw [h0]; exact hu
      · exact le_rfl
    · rw [← h.ofSum_toSum b'] at hb' hor ⊢
      rcases hc : h.toSum b' with x' | y'
      · rw [hc] at hb'
        exact absurd hb' (h.not_child_inl_inr x' y)
      · rw [hc] at hb' hor
        exact (hD₂ y).2 y' ((h.child_inr_inr y y').mp hb') hor
    · obtain ⟨y, rfl, hy⟩ := (hlone b).mp hb
      exact hL₂ y hy hf

namespace Root2B

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D P

theorem rt2_bR_ne_inr (y : GBranch LGB.garden.tree) : D.bR P ≠ D.gd.ofSum (.inr y) := fun he => by
  have := D.gd.ofSum_injective he
  simp at this

theorem rt2_rootPins_bR (σ : ℝ) : MkSlotsO.rootPins (fun _ => True) σ (D.bR P) = none := by
  unfold MkSlotsO.rootPins
  rw [if_neg]
  rintro ⟨h, -⟩
  rw [D.bR_val P] at h
  exact bPath_ne_nil m inner h

theorem rt2_fix_inl (σ u : ℝ) (x : GBranch LGZ.garden.tree) :
    Function.update (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P) (some u) (D.gd.ofSum (.inl x)) =
      pairFix m inner σ u x := by
  by_cases hb : x = P.hp.bB
  · subst hb
    rw [show D.gd.ofSum (.inl P.hp.bB) = D.bR P from rfl, Function.update_self, P.pairFix_bB]
  · rw [Function.update_of_ne (fun he => hb (by simpa [Root2Data.bR] using D.gd.ofSum_injective he))]
    unfold MkSlotsO.rootPins pairFix
    rw [D.inl_val]
    simp only [and_true]
    by_cases h0 : x.1.2 = []
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0, if_neg (show ¬ x.1.2 = bPath m inner from
        fun h => hb (Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)))]

theorem rt2_fix_inr (σ u : ℝ) (y : GBranch LGB.garden.tree) :
    Function.update (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P) (some u) (D.gd.ofSum (.inr y)) =
      trFix 1 σ y := by
  rw [Function.update_of_ne (rt2_bR_ne_inr D P y).symm]
  unfold MkSlotsO.rootPins trFix
  have hv : (D.gd.ofSum (.inr y)).1 = botAddr (cpair m Qr Qg inner).lonePath y.1 := rfl
  obtain ⟨⟨t, q⟩, hq⟩ := y
  rw [hv]
  by_cases ht : t = 0
  · subst ht
    simp [botAddr, cpair_lonePath, lonePos]
  · have ht1 : t = 1 := by fin_cases t <;> simp_all
    subst ht1
    simp [botAddr]

/-- **The glue step with both roots pinned.** -/
theorem rt2_protTime_glue2 (L γ δ : ℝ) {d : ℕ} (s σ u : ℝ) (hu : u ≤ σ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => σ) s (Function.update (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P) (some u)) K =
      protTime L γ δ LGZ (fun _ => σ) s (pairFix m inner σ u) (K ∘ D.gd.ι₁) *
        protTime L γ δ LGB (fun y => bClock (fun _ => σ) u y.1.1) s (trFix 1 σ) (K ∘ D.gd.ι₂) := by
  have hfree0 : ∀ y : GBranch LGB.garden.tree, y.1.1 = 0 →
      Function.update (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P) (some u) (D.gd.ofSum (.inr y)) = none :=
    fun y hy => by
    rw [rt2_fix_inr D P σ u y]; unfold trFix; rw [if_neg]; rintro ⟨h, -⟩; rw [hy] at h; simp at h
  have hpinB : ∀ y v, Function.update (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P) (some u)
      (D.gd.ofSum (.inr y)) = some v → v ≤ (fun _ : Fin 2 => σ) y.1.1 := fun y v hv => by
    rw [rt2_fix_inr D P σ u y] at hv
    unfold trFix at hv
    split_ifs at hv
    simp at hv
    rw [hv]
  set fix := Function.update (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P) (some u)
  have hD := fun τ hτ => rt2_protDom_glue_pin2 D.gd (fun _ => σ) s s fix P.hp.bB u (Function.update_self _ _ _)
    hfree0 hpinB hu D.hl₁ D.hl₂ D.hlone (D.hlone₁ P) (D.hpar P) (D.hpar' P) τ hτ
  rw [show (fun _ : GBranch LG.garden.tree => σ) = (fun b => (fun _ : Fin 2 => σ) b.1.1) from rfl,
    protTime_glue L γ δ D.gd (fun b => (fun _ : Fin 2 => σ) b.1.1) s fix (fun _ => σ) s
      (fun y => bClock (fun _ => σ) u y.1.1) s K hD]
  congr 2
  · funext x; exact rt2_fix_inl D P σ u x
  · funext y; exact rt2_fix_inr D P σ u y

theorem rt2_root2U_sub (s σ : ℝ) :
    root2U LG m inner σ σ ⊆ pinSet LG (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P) := by
  rintro u ⟨h1, h2, h3, h4, h5⟩
  refine ⟨by rw [D.layer_bR P]; exact h1, by rw [D.layer_bR P]; exact h2, h3, h4, fun b' hb' σ' hσ' => ?_,
    fun b hb σ' hσ' => ?_, fun hl => absurd hl (not_loneParent_of_plain D.plain _)⟩
  · exfalso
    unfold MkSlotsO.rootPins at hσ'
    split_ifs at hσ' with hp
    obtain ⟨-, i, hi⟩ := hb'
    rw [hp.1] at hi
    have := congrArg List.length hi
    simp at this
  · unfold MkSlotsO.rootPins at hσ'
    split_ifs at hσ' with hp
    rw [← Option.some.inj hσ']
    exact h5

theorem rt2_pinSet_lt_root (s σ u : ℝ)
    (hu : u ∈ pinSet LG (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P))
    (hnil : inner.lonePath = []) : u < σ := by
  have hchild : (D.bR P).IsChildOf (D.aR P) := by
    refine ⟨rfl, m.c, ?_⟩
    show bPath m inner = [] ++ [m.c]
    simp [bPath, hnil]
  exact hu.2.2.2.2.2.1 _ hchild σ (by unfold MkSlotsO.rootPins; rw [D.aR_val P]; simp)

/-- **Both roots pinned, one decoration of times** (o104 Prop 7.4 (a), `ε = +`, the second root also pinned). -/
theorem rt2_protTime_root2 (L γ δ : ℝ) {d : ℕ} (s σ : ℝ) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) K =
      ∫ u in root2U LG m inner σ σ,
        protTime L γ δ LGZ (fun _ => σ) s (pairFix m inner σ u) (K ∘ D.gd.ι₁) *
          protTime L γ δ LGB (fun y => bClock (fun _ => σ) u y.1.1) s (trFix 1 σ) (K ∘ D.gd.ι₂) := by
  rw [protTime_pin L γ δ LG (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) K (D.bR P)
    (rt2_rootPins_bR D P σ), ← integral_indicator (measurableSet_root2U LG m inner σ σ)]
  congr 1
  funext u
  by_cases hU : u ∈ root2U LG m inner σ σ
  · rw [Set.indicator_of_mem (rt2_root2U_sub D P s σ hU), Set.indicator_of_mem hU,
      rt2_protTime_glue2 D P L γ δ s σ u hU.2.2.2.1.le K]
  · rw [Set.indicator_of_notMem hU]
    by_cases hP : u ∈ pinSet LG (fun _ => σ) s (MkSlotsO.rootPins (fun _ => True) σ) (D.bR P)
    · rw [Set.indicator_of_mem hP]
      have hσu : σ ≤ u := by
        by_contra hlt
        exact hU ⟨by rw [← D.layer_bR P]; exact hP.1, by rw [← D.layer_bR P]; exact hP.2.1, hP.2.2.1,
          hP.2.2.2.1, lt_of_not_ge hlt⟩
      have hin : inner.lonePath ≠ [] := fun hnil =>
        absurd (rt2_pinSet_lt_root D P s σ u hP hnil) (not_lt.mpr hσu)
      rw [rt2_protTime_glue2 D P L γ δ s σ u hP.2.2.2.1.le K, P.protTime_both_zero L γ δ σ s σ u hσu hin,
        zero_mul]
    · rw [Set.indicator_of_notMem hP]

end Root2B

end WaveTurbulence.Flower.ProtRT
