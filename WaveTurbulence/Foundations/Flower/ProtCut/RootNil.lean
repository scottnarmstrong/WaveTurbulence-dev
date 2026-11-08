/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CheckRoot

/-! # D2c PROT-CUT: one-pair chains — (P2) and the root cut without suffix (time and summand level)

A protected tree with code `X = pair m Qr Qg inner nil` (`PairOnly`) is itself a closing pair: the root `𝔫_1` is
linked to the terminal node `𝔫_b`.

* `pairFix σ v`: root at `σ`, `𝔫_b` at `v` — the configuration `rootTerm` (P2) (`cfg_rootTerm_fix`).
* `PairOnly.protTime_both`: both designated: boundary phases × interior(σ, v) × Qr(σ, v) × Qg(σ, v).
* `PairOnly.protTime_root0`: root designated at `σ`, `𝔫_b` integrated over
  `rootU0 = {max(𝔏_b, 0, s) < u < min(𝔏_b + 1, T, σ)}` (the lone-port time `s` bounds `u`: `𝔫_b` is the lone parent).
* `PairOnly.summand_both`, `PairOnly.summand_root0`: the same at one decoration (`PairData.decEquiv`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- Root at `σ` and `𝔫_b` at `v`. -/
def pairFix (m : MiniTreeCode) (inner : RegChain) (σ v : ℝ) {T : Fin 1 → TTree} (b : GBranch T) : Option ℝ :=
  if b.1.2 = [] then some σ else if b.1.2 = bPath m inner then some v else none

/-- The range of `u = τ_{𝔫_b}` without suffix. -/
def rootU0 (LG : LayeredGarden 1) (m : MiniTreeCode) (inner : RegChain) (T σ s : ℝ) : Set ℝ :=
  {u | (layerAt LG ((0 : Fin 1), bPath m inner) : ℝ) < u ∧ u < layerAt LG ((0 : Fin 1), bPath m inner) + 1 ∧
    0 < u ∧ u < T ∧ u < σ ∧ s < u}

theorem measurableSet_rootU0 (LG : LayeredGarden 1) (m : MiniTreeCode) (inner : RegChain) (T σ s : ℝ) :
    MeasurableSet (rootU0 LG m inner T σ s) := by
  unfold rootU0
  simp only [Set.ofPred_and]
  exact (measurableSet_lt measurable_const measurable_id).inter
    ((measurableSet_lt measurable_id measurable_const).inter
      ((measurableSet_lt measurable_const measurable_id).inter
        ((measurableSet_lt measurable_id measurable_const).inter
          ((measurableSet_lt measurable_id measurable_const).inter
            (measurableSet_lt measurable_const measurable_id)))))

theorem volume_rootU0_ne_top (LG : LayeredGarden 1) (m : MiniTreeCode) (inner : RegChain) (T σ s : ℝ) :
    volume (rootU0 LG m inner T σ s) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := volume (Ioo (layerAt LG ((0 : Fin 1), bPath m inner) : ℝ)
    (layerAt LG ((0 : Fin 1), bPath m inner) + 1))) ?_ (measure_mono fun u hu => ⟨hu.1, hu.2.1⟩)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

theorem cfg_rootTerm_fix (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (s t up : ℝ)
    {T : Fin 1 → TTree} :
    (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t up : GBranch T → Option ℝ) = pairFix m inner t s := by
  funext b
  have hd : (cpair m Qr Qg inner).lonePath.dropLast = bPath m inner := by
    rw [cpair_lonePath, lonePos, List.dropLast_concat]
  unfold ProtCfg.fix ProtCfg.pins pairFix
  rw [if_pos (Fin.val_eq_zero _), hd]
  simp only [List.lookup]
  by_cases h1 : b.1.2 = []
  · rw [if_pos h1, show (b.1.2 == []) = true from beq_iff_eq.mpr h1]
  · rw [if_neg h1, show (b.1.2 == []) = false from beq_eq_false_iff_ne.mpr h1]
    by_cases h2 : b.1.2 = bPath m inner
    · rw [if_pos h2, show (b.1.2 == bPath m inner) = true from beq_iff_eq.mpr h2]
    · rw [if_neg h2, show (b.1.2 == bPath m inner) = false from beq_eq_false_iff_ne.mpr h2]

/-- **A one-pair protected tree and its pieces.** -/
structure PairOnly (LG : LayeredGarden 1) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain)
    (LGi : LayeredGarden 1) (LGr LGg : LayeredGarden 2) : Prop where
  dec : (cpair m Qr Qg inner).DecodesTree LG.garden
  decI : inner.DecodesTree LGi.garden
  sigI : LGi.garden.sig 0 = slotSign (LG.garden.sig 0) m.c
  decR : Qr.Decodes LGr.garden
  decG : Qg.Decodes LGg.garden
  layI : ∀ z : GNode LGi.garden.tree, LGi.layer z = layerAt LG ((0 : Fin 1), m.c :: z.1.2)
  layR : ∀ z : GNode LGr.garden.tree,
    LGr.layer z = layerAt LG ((0 : Fin 1), rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2)
  layG : ∀ z : GNode LGg.garden.tree,
    LGg.layer z = layerAt LG ((0 : Fin 1), gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2)

namespace PairOnly

variable {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg)
include D

theorem hp : PairData m Qr Qg inner LG.garden LGi.garden LGr.garden LGg.garden :=
  ⟨D.dec, D.decI, D.sigI, D.decR, D.decG⟩

theorem hli (z : GNode LGi.garden.tree) : LGi.layer z = LG.layer (D.hp.ιi z) := by
  rw [D.layI, ← layerAt_node]; rfl

theorem hlr (z : GNode LGr.garden.tree) : LGr.layer z = LG.layer (D.hp.ιr z) := by
  rw [D.layR, ← layerAt_node]; rfl

theorem hlg (z : GNode LGg.garden.tree) : LGg.layer z = LG.layer (D.hp.ιg z) := by
  rw [D.layG, ← layerAt_node]; rfl

theorem pairFix_rootB (σ v : ℝ) : pairFix m inner σ v D.hp.rootB = some σ := by
  unfold pairFix; exact if_pos rfl

theorem pairFix_bB (σ v : ℝ) : pairFix m inner σ v D.hp.bB = some v := by
  unfold pairFix
  exact (if_neg (bPath_ne_nil m inner)).trans (if_pos rfl)

theorem pairFix_other (σ v : ℝ) (b : GBranch LG.garden.tree) (h1 : b ≠ D.hp.rootB) (h2 : b ≠ D.hp.bB) :
    pairFix m inner σ v b = none := by
  unfold pairFix
  exact (if_neg (fun h => h1 (Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)))).trans
    (if_neg (fun h => h2 (Subtype.ext (Prod.ext (Subsingleton.elim _ _) h))))

theorem pb_ne {z z' : Fin 2 ⊕ (GBranch LGi.garden.tree ⊕ (GBranch LGr.garden.tree ⊕ GBranch LGg.garden.tree))}
    (hz : z ≠ z') : D.hp.pairBranch z ≠ D.hp.pairBranch z' := D.hp.pairBranch_injective.ne hz

theorem fix_βi (σ v : ℝ) (x : GBranch LGi.garden.tree) : pairFix m inner σ v (D.hp.βi x) = none :=
  D.pairFix_other σ v _ (D.pb_ne (z := .inr (.inl x)) (z' := .inl 0) (by simp))
    (D.pb_ne (z := .inr (.inl x)) (z' := .inl 1) (by simp))

theorem fix_βr (σ v : ℝ) (y : GBranch LGr.garden.tree) : pairFix m inner σ v (D.hp.βr y) = none :=
  D.pairFix_other σ v _ (D.pb_ne (z := .inr (.inr (.inl y))) (z' := .inl 0) (by simp))
    (D.pb_ne (z := .inr (.inr (.inl y))) (z' := .inl 1) (by simp))

theorem fix_βg (σ v : ℝ) (y : GBranch LGg.garden.tree) : pairFix m inner σ v (D.hp.βg y) = none :=
  D.pairFix_other σ v _ (D.pb_ne (z := .inr (.inr (.inr y))) (z' := .inl 0) (by simp))
    (D.pb_ne (z := .inr (.inr (.inr y))) (z' := .inl 1) (by simp))

/-- **Both linked nodes designated** (P2, time level). -/
theorem protTime_both (L γ δ : ℝ) {d : ℕ} (T s σ v : ℝ) (hσT : σ ≤ T) (hvT : v ≤ T)
    (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s (pairFix m inner σ v) K =
      Complex.exp ((Real.pi * ((LG.garden.sign D.hp.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LG.garden K D.hp.rootB * σ : ℝ) * Complex.I) *
        Complex.exp ((Real.pi * ((LG.garden.sign D.hp.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
          omegaNode LG.garden K D.hp.bB * v : ℝ) * Complex.I) *
        (protTime L γ δ LGi (fun _ => σ) v (fun _ => none) (K ∘ D.hp.ιi) *
          (protTime L γ δ LGr (fun y => cupR m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
              (K ∘ D.hp.ιr) *
            protTime L γ δ LGg (fun y => cupG m inner (LG.garden.sig 0) σ v y.1.1) 0 (fun _ => none)
              (K ∘ D.hp.ιg))) := by
  have e := PairData.protTime_pair D.hp L γ δ T s σ v (pairFix m inner σ v) (D.pairFix_rootB σ v)
    (D.pairFix_bB σ v) D.hli D.hlr D.hlg hσT hvT
    (fun x τ hx => by rw [D.fix_βi] at hx; simp at hx)
    (fun y τ hy => by rw [D.fix_βr] at hy; simp at hy)
    (fun y τ hy => by rw [D.fix_βg] at hy; simp at hy) K
  rw [e]
  have h1 : (fun x => pairFix m inner σ v (D.hp.βi x)) = fun _ => none := funext (D.fix_βi σ v)
  have h2 : (fun y => pairFix m inner σ v (D.hp.βr y)) = fun _ => none := funext (D.fix_βr σ v)
  have h3 : (fun y => pairFix m inner σ v (D.hp.βg y)) = fun _ => none := funext (D.fix_βg σ v)
  rw [h1, h2, h3]

theorem protTime_both_zero (L γ δ : ℝ) {d : ℕ} (T s σ u : ℝ) (hσu : σ ≤ u) (hin : inner.lonePath ≠ [])
    (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s (pairFix m inner σ u) K = 0 := by
  unfold protTime
  refine (integral_congr_ae (Filter.Eventually.of_forall fun σ' => ?_)).trans (integral_zero _ _)
  refine Set.indicator_of_notMem (fun hmem => ?_) _
  have hI := (PairData.protDom_pair_mp D.hp T s σ u _ (D.pairFix_rootB σ u) (D.pairFix_bB σ u)
    D.hli D.hlr D.hlg (fun x τ' hx => by rw [D.fix_βi] at hx; simp at hx)
    (fun y τ' hy => by rw [D.fix_βr] at hy; simp at hy)
    (fun y τ' hy => by rw [D.fix_βg] at hy; simp at hy) _
    (fun b v hv => extendFix_some _ _ _ hv) hmem).1
  obtain ⟨q, k, hq⟩ := (List.eq_nil_or_concat inner.lonePath).resolve_left hin
  have hmem' : q ∈ (LGi.garden.tree 0).branching := by
    rw [D.decI.1]
    refine TTree.branching_of_append_mem _ (i := k) ?_
    rw [← List.concat_eq_append, ← hq]
    exact lonePath_mem_plug inner _ _
  let x₀ : GBranch LGi.garden.tree := ⟨((0 : Fin 1), q), hmem'⟩
  have hx₀ : LGi.garden.IsLoneParent x₀ := (D.hp.isLoneParent_I x₀).mpr ⟨k, by simpa using hq⟩
  have h1 := hI.2 x₀ hx₀ (D.fix_βi σ u x₀)
  have h2 := ((hI.1 x₀).1 (D.fix_βi σ u x₀)).2.2.2
  simp only at h1 h2
  linarith

theorem update_rootFix (σ u : ℝ) : Function.update (rootFix σ) D.hp.bB (some u) = pairFix m inner σ u := by
  funext b
  by_cases hb : b = D.hp.bB
  · subst hb
    rw [Function.update_self, D.pairFix_bB]
  · rw [Function.update_of_ne hb]
    unfold rootFix pairFix
    by_cases h0 : b.1.2 = []
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
      exact (if_neg (fun h => hb (Subtype.ext (Prod.ext (Subsingleton.elim _ _) h)))).symm

theorem layer_bB : LG.layer D.hp.bB.toNode = layerAt LG ((0 : Fin 1), bPath m inner) := by
  rw [← layerAt_node]; rfl

theorem bB_lone : LG.garden.IsLoneParent D.hp.bB := by
  have hmem : lonePos m inner ∈ (LG.garden.tree 0).leaves := by
    rw [D.dec.1, ← cpair_lonePath]
    exact lonePath_mem_leaves _ _
  refine ⟨⟨((0 : Fin 1), lonePos m inner), hmem⟩, ?_, Subsingleton.elim _ _, m.lone, rfl⟩
  unfold Garden.IsLone
  exact (D.dec.2.1 _).trans (by rw [cpair_lonePath]; simp)

theorem rootU0_sub (T s σ : ℝ) : rootU0 LG m inner T σ s ⊆ pinSet LG (fun _ => T) s (rootFix σ) D.hp.bB := by
  rintro u ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨by rw [D.layer_bB]; exact h1, by rw [D.layer_bB]; exact h2, h3, h4, fun b' hb' σ' hσ' => ?_,
    fun b hb σ' hσ' => ?_, fun _ => h6⟩
  · exfalso
    unfold rootFix at hσ'
    split_ifs at hσ' with hp
    obtain ⟨-, i, hi⟩ := hb'
    rw [hp] at hi
    have := congrArg List.length hi
    simp at this
  · unfold rootFix at hσ'
    split_ifs at hσ' with hp
    rw [← Option.some.inj hσ']
    exact h5

theorem pinSet_lt0 (T s σ u : ℝ) (hu : u ∈ pinSet LG (fun _ => T) s (rootFix σ) D.hp.bB)
    (hnil : inner.lonePath = []) : u < σ := by
  have hchild : D.hp.bB.IsChildOf D.hp.rootB := by
    refine ⟨Subsingleton.elim _ _, m.c, ?_⟩
    show bPath m inner = [] ++ [m.c]
    simp [bPath, hnil]
  exact hu.2.2.2.2.2.1 _ hchild σ (by unfold rootFix; exact if_pos rfl)

/-- **The root pin of a one-pair tree** (time level). -/
theorem protTime_root0 (L γ δ : ℝ) {d : ℕ} (T s σ : ℝ) (hσT : σ ≤ T) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s (rootFix σ) K =
      ∫ u in rootU0 LG m inner T σ s,
        Complex.exp ((Real.pi * ((LG.garden.sign D.hp.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode LG.garden K D.hp.rootB * σ : ℝ) * Complex.I) *
          Complex.exp ((Real.pi * ((LG.garden.sign D.hp.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode LG.garden K D.hp.bB * u : ℝ) * Complex.I) *
        (protTime L γ δ LGi (fun _ => σ) u (fun _ => none) (K ∘ D.hp.ιi) *
          (protTime L γ δ LGr (fun y => cupR m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
              (K ∘ D.hp.ιr) *
            protTime L γ δ LGg (fun y => cupG m inner (LG.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
              (K ∘ D.hp.ιg))) := by
  have hfb : rootFix σ D.hp.bB = none := by
    unfold rootFix; exact if_neg (bPath_ne_nil m inner)
  rw [protTime_pin L γ δ LG (fun _ => T) s (rootFix σ) K D.hp.bB hfb,
    ← integral_indicator (measurableSet_rootU0 LG m inner T σ s)]
  congr 1
  funext u
  by_cases hU : u ∈ rootU0 LG m inner T σ s
  · rw [Set.indicator_of_mem (D.rootU0_sub T s σ hU), Set.indicator_of_mem hU, D.update_rootFix,
      D.protTime_both L γ δ T s σ u hσT hU.2.2.2.1.le]
  · rw [Set.indicator_of_notMem hU]
    by_cases hP : u ∈ pinSet LG (fun _ => T) s (rootFix σ) D.hp.bB
    · rw [Set.indicator_of_mem hP]
      have hσu : σ ≤ u := by
        by_contra hlt
        exact hU ⟨by rw [← D.layer_bB]; exact hP.1, by rw [← D.layer_bB]; exact hP.2.1, hP.2.2.1,
          hP.2.2.2.1, lt_of_not_ge hlt, hP.2.2.2.2.2.2 D.bB_lone⟩
      have hin : inner.lonePath ≠ [] := fun hnil =>
        absurd (D.pinSet_lt0 T s σ u hP hnil) (not_lt.mpr hσu)
      rw [D.update_rootFix, D.protTime_both_zero L γ δ T s σ u hσu hin]
    · rw [Set.indicator_of_notMem hP]

end PairOnly

end WaveTurbulence.Flower.ProtCut
