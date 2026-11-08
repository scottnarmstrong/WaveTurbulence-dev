/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootP3Glue

/-! # D2c PROT-CUT: (P3) at one decoration — the root cut with the terminal designated in the suffix (time level)

`X = pair m Qr Qg inner rest` (`rest ≠ nil`), root at `σ` and the terminal node (the suffix's terminal) at `s`
(`ProtCfg.rootTerm`, `cfg_rootTerm_fix'`). `RootData.protTime_rootCut3`: the root cut of `RootData.protTime_rootCut`
with the suffix piece carrying its own terminal designation `ProtCfg.term.fix rest s` and `u ∈ rootU3 = rootU ∩ {s < u}`
(for `u ≤ s` the suffix chain from its root down to the terminal has no admissible times). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- Root at `σ`, the suffix terminal at `s`. -/
def rootTermFix (m : MiniTreeCode) (inner rest : RegChain) (σ s : ℝ) {T : Fin 1 → TTree} (b : GBranch T) :
    Option ℝ :=
  if b.1.2 = [] then some σ else if b.1.2 = lonePos m inner ++ rest.lonePath.dropLast then some s else none

/-- The range of `u` for (P3). -/
def rootU3 (LG : LayeredGarden 1) (m : MiniTreeCode) (inner : RegChain) (T σ s : ℝ) : Set ℝ :=
  rootU LG m inner T σ ∩ {u | s < u}

theorem measurableSet_rootU3 (LG : LayeredGarden 1) (m : MiniTreeCode) (inner : RegChain) (T σ s : ℝ) :
    MeasurableSet (rootU3 LG m inner T σ s) :=
  (measurableSet_rootU LG m inner T σ).inter (measurableSet_lt measurable_const measurable_id)

theorem rest_dropLast_ne {rest : RegChain} (h : rest ≠ .nil) : rest.lonePath.dropLast ≠ [] := by
  cases rest with
  | nil => exact absurd rfl h
  | pair m' Qr' Qg' inner' rest' =>
    intro h'
    have := congrArg List.length h'
    simp [RegChain.lonePath, List.length_dropLast] at this

theorem cfg_rootTerm_fix' (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) (hrest : rest ≠ .nil)
    (s t up : ℝ) {T : Fin 1 → TTree} :
    (ProtCfg.rootTerm.fix (RegChain.pair m Qr Qg inner rest) s t up : GBranch T → Option ℝ) =
      rootTermFix m inner rest t s := by
  have hne : rest.lonePath ≠ [] := fun h => rest_dropLast_ne hrest (by rw [h]; rfl)
  have hd : (RegChain.pair m Qr Qg inner rest).lonePath.dropLast = lonePos m inner ++ rest.lonePath.dropLast := by
    rw [RootData.lonePath_eq, List.dropLast_append_of_ne_nil hne]
  funext b
  unfold ProtCfg.fix ProtCfg.pins rootTermFix
  rw [if_pos (Fin.val_eq_zero _), hd]
  simp only [List.lookup]
  by_cases h1 : b.1.2 = []
  · rw [if_pos h1, show (b.1.2 == []) = true from beq_iff_eq.mpr h1]
  · rw [if_neg h1, show (b.1.2 == []) = false from beq_eq_false_iff_ne.mpr h1]
    by_cases h2 : b.1.2 = lonePos m inner ++ rest.lonePath.dropLast
    · rw [if_pos h2, show (b.1.2 == lonePos m inner ++ rest.lonePath.dropLast) = true from beq_iff_eq.mpr h2]
    · rw [if_neg h2, show (b.1.2 == lonePos m inner ++ rest.lonePath.dropLast) = false from
        beq_eq_false_iff_ne.mpr h2]

namespace RootData

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
include D

/-- The designations after `𝔫_b` is designated at `u`. -/
def fixU3 (σ s u : ℝ) : GBranch LG.garden.tree → Option ℝ :=
  Function.update (rootTermFix m inner rest σ s) D.bR (some u)

theorem rootTermFix_bR (σ s : ℝ) : rootTermFix m inner rest σ s D.bR = none := by
  unfold rootTermFix
  refine (if_neg (by rw [D.bR_path]; exact bPath_ne_nil m inner)).trans (if_neg ?_)
  show bPath m inner ≠ lonePos m inner ++ rest.lonePath.dropLast
  intro h
  have := congrArg List.length h
  simp [lonePos, bPath] at this

theorem fixU3_inl (σ s u : ℝ) (x : GBranch LGZ.garden.tree) :
    D.fixU3 σ s u (D.gd.ofSum (.inl x)) = D.fixU σ u (D.gd.ofSum (.inl x)) := by
  unfold fixU3 fixU
  by_cases hx : D.gd.ofSum (.inl x) = D.bR
  · rw [hx, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hx, Function.update_of_ne hx]
    unfold rootTermFix rootFix
    by_cases h0 : (D.gd.ofSum (.inl x)).1.2 = []
    · rw [if_pos h0, if_pos h0]
    · rw [if_neg h0, if_neg h0]
      refine if_neg fun h => D.top_not_prefix x ?_
      rw [cpair_lonePath]
      have : x.1.2 = (D.gd.ofSum (.inl x)).1.2 := rfl
      rw [this, h]
      exact List.prefix_append _ _

theorem fixU3_inr (σ s u : ℝ) (y : GBranch LGs.garden.tree) :
    D.fixU3 σ s u (D.gd.ofSum (.inr y)) = ProtCfg.term.fix rest s σ u y := by
  have hne : D.gd.ofSum (.inr y) ≠ D.bR := by
    intro he
    have := congrArg (fun b : GBranch LG.garden.tree => b.1.2) he
    simp only [D.inr_path, D.bR_path] at this
    have h2 := congrArg List.length this
    simp [lonePos, bPath] at h2
  unfold fixU3
  rw [Function.update_of_ne hne]
  unfold rootTermFix ProtCfg.fix ProtCfg.pins
  rw [if_neg (by rw [D.inr_path]; simp [lonePos]), if_pos (Fin.val_eq_zero _)]
  simp only [List.lookup, D.inr_path, List.append_cancel_left_eq]
  by_cases h : y.1.2 = rest.lonePath.dropLast
  · rw [if_pos h, show (y.1.2 == rest.lonePath.dropLast) = true from beq_iff_eq.mpr h]
  · rw [if_neg h, show (y.1.2 == rest.lonePath.dropLast) = false from beq_eq_false_iff_ne.mpr h]

theorem protTime_glueR3 (L γ δ : ℝ) {d : ℕ} (T s' σ s u : ℝ) (hsu : s ≤ u) (huT : u ≤ T)
    (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s' (D.fixU3 σ s u) K =
      protTime L γ δ LGZ (fun _ => T) s' (fun x => D.fixU σ u (D.gd.ofSum (.inl x))) (K ∘ D.gd.ι₁) *
        protTime L γ δ LGs (fun _ => u) s' (ProtCfg.term.fix rest s σ u) (K ∘ D.gd.ι₂) := by
  have hfp : D.fixU3 σ s u (D.gd.ofSum (.inl D.hp.bB)) = some u := Function.update_self _ _ _
  have hpinb : ∀ y v, D.fixU3 σ s u (D.gd.ofSum (.inr y)) = some v → v ≤ u := by
    intro y v hv
    rw [D.fixU3_inr] at hv
    unfold ProtCfg.fix ProtCfg.pins at hv
    rw [if_pos (Fin.val_eq_zero _)] at hv
    simp only [List.lookup] at hv
    split at hv
    · rw [← Option.some.inj hv]; exact hsu
    · simp at hv
  have hD := fun τ hτ => protDom_glue_free' D.gd (fun _ => T) s' s' (D.fixU3 σ s u) D.hp.bB u hfp hpinb
    (fun _ => huT) D.hl₁ D.hl₂ D.hlone D.hlone₁ D.hpar D.hpar' τ hτ
  rw [protTime_glue L γ δ D.gd (fun _ => T) s' (D.fixU3 σ s u) (fun _ => T) s' (fun _ => u) s' K hD]
  congr 2
  · funext x; exact D.fixU3_inl σ s u x
  · funext y; exact D.fixU3_inr σ s u y

theorem fixU3_bR (σ s u : ℝ) : D.fixU3 σ s u D.bR = some u := Function.update_self _ _ _

/-- For `u ≤ s` the suffix chain has no admissible times: the whole time integral vanishes. -/
theorem protTime_fixU3_zero (L γ δ : ℝ) {d : ℕ} (T s' σ s u : ℝ) (hus : u ≤ s)
    (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s' (D.fixU3 σ s u) K = 0 := by
  unfold protTime
  refine (integral_congr_ae (Filter.Eventually.of_forall fun σ' => ?_)).trans (integral_zero _ _)
  refine Set.indicator_of_notMem (fun hmem => ?_) _
  set τ := LG.garden.extendFix (D.fixU3 σ s u) σ'
  have hτ : ∀ b v, D.fixU3 σ s u b = some v → τ b = v := fun b v hv => extendFix_some _ _ _ hv
  have hchild : ∀ b b' : GBranch LG.garden.tree, b'.IsChildOf b →
      (D.fixU3 σ s u b' = none ∨ D.fixU3 σ s u b = none) → τ b' < τ b :=
    fun b b' hc hor => (hmem.1 b).2 b' hc hor
  -- the suffix root and the suffix terminal
  have hT : LGs.garden.tree 0 = rest.plug (LG.garden.sig 0) .leaf := by
    have := D.decS.1; rw [D.sigS] at this; exact this
  have hrb : ([] : Path) ∈ (LGs.garden.tree 0).branching := by
    rw [hT]
    cases hr : rest with
    | nil => exact absurd hr D.rest_ne
    | pair => simp [RegChain.plug, node3, TTree.branching]
  have htb : rest.lonePath.dropLast ∈ (LGs.garden.tree 0).branching := by
    rw [hT]
    have hl := lonePath_mem_leaves rest (LG.garden.sig 0)
    rw [← List.dropLast_append_getLast D.rest_lonePath_ne] at hl
    exact TTree.branching_of_append_mem _ (TTree.leaves_subset_nodes _ hl)
  let rS : GBranch LGs.garden.tree := ⟨((0 : Fin 1), []), hrb⟩
  let tS : GBranch LGs.garden.tree := ⟨((0 : Fin 1), rest.lonePath.dropLast), htb⟩
  set J := D.gd.ofSum (.inr rS)
  set b0 := D.gd.ofSum (.inr tS)
  have hJp : J.1.2 = lonePos m inner := by
    show (D.gd.ofSum (.inr rS)).1.2 = _
    rw [D.inr_path]; simp [rS]
  have hb0p : b0.1.2 = lonePos m inner ++ rest.lonePath.dropLast := by
    show (D.gd.ofSum (.inr tS)).1.2 = _
    rw [D.inr_path]
  have hb0 : D.fixU3 σ s u b0 = some s := by
    rw [D.fixU3_inr]
    unfold ProtCfg.fix ProtCfg.pins
    rw [if_pos (Fin.val_eq_zero _)]
    simp [List.lookup, tS]
  have hJfree : D.fixU3 σ s u J = none := by
    rw [D.fixU3_inr]
    unfold ProtCfg.fix ProtCfg.pins
    rw [if_pos (Fin.val_eq_zero _)]
    have hne := rest_dropLast_ne D.rest_ne
    show List.lookup ([] : Path) [(rest.lonePath.dropLast, s)] = none
    obtain ⟨a, l, hal⟩ := List.exists_cons_of_ne_nil hne
    rw [hal]
    rfl
  -- the lower clock: τ b0 < τ J
  obtain ⟨q', hq'⟩ : ∃ q' : Path, q' = rest.lonePath.dropLast := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, rest.lonePath.dropLast.length = n + 1 := by
    have hne := rest_dropLast_ne D.rest_ne
    exact Nat.exists_eq_succ_of_ne_zero (fun h => hne (List.eq_nil_of_length_eq_zero h))
  have hlow := lt_of_free_ancestor (D.fixU3 σ s u) τ hchild b0 n J rest.lonePath.dropLast
    (Subsingleton.elim _ _) (by rw [hb0p, hJp]) hn (fun c hc1 hc2 hc3 hc4 => by
      have hcne : c ≠ D.bR := by
        intro he
        have := congrArg (fun b : GBranch LG.garden.tree => b.1.2.length) he
        rw [hJp] at hc2
        have h2 := hc2.length_le
        simp only [D.bR_path] at this
        rw [he] at h2
        simp [lonePos, bPath, D.bR_path] at h2
      unfold fixU3
      rw [Function.update_of_ne hcne]
      unfold rootTermFix
      rw [hJp] at hc2
      have h0 : c.1.2 ≠ [] := by
        intro h0; rw [h0] at hc2
        have := hc2.length_le; simp [lonePos] at this
      rw [if_neg h0, if_neg]
      intro hp
      exact hc4 (Subtype.ext (Prod.ext (Subsingleton.elim _ _) (hp.trans hb0p.symm))))
  have hJb : J.IsChildOf D.bR := by
    refine ⟨Subsingleton.elim _ _, m.lone, ?_⟩
    rw [hJp, D.bR_path]
    simp [lonePos, bPath]
  have hup := hchild D.bR J hJb (Or.inl hJfree)
  rw [hτ _ _ hb0] at hlow
  rw [hτ _ _ (D.fixU3_bR σ s u)] at hup
  linarith

theorem rootTermFix_aR (σ s : ℝ) : rootTermFix m inner rest σ s D.aR = some σ := by
  unfold rootTermFix; exact if_pos rfl

theorem rootU3_sub (T s' σ s : ℝ) :
    rootU3 LG m inner T σ s ⊆ pinSet LG (fun _ => T) s' (rootTermFix m inner rest σ s) D.bR := by
  rintro u ⟨⟨h1, h2, h3, h4, h5⟩, -⟩
  refine ⟨by rw [D.layer_bR]; exact h1, by rw [D.layer_bR]; exact h2, h3, h4, fun b' hb' σ' hσ' => ?_,
    fun b hb σ' hσ' => ?_, fun hl => absurd hl D.bR_not_lone⟩
  · exfalso
    obtain ⟨-, i, hi⟩ := hb'
    rw [D.bR_path] at hi
    unfold rootTermFix at hσ'
    split_ifs at hσ' with hp hq
    · rw [hp] at hi; have := congrArg List.length hi; simp at this
    · rw [hq] at hi
      have := congrArg List.length hi
      have hne := rest_dropLast_ne D.rest_ne
      have hl : 1 ≤ rest.lonePath.dropLast.length := List.length_pos_of_ne_nil hne
      simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, lonePos,
        bPath] at this
      omega
  · unfold rootTermFix at hσ'
    split_ifs at hσ' with hp hq
    · rw [← Option.some.inj hσ']; exact h5
    · exfalso
      obtain ⟨-, i, hi⟩ := hb
      rw [D.bR_path, hq] at hi
      have := congrArg List.length hi
      simp only [List.length_append, List.length_cons, List.length_singleton, List.length_nil, lonePos,
        bPath] at this
      omega

theorem pinSet_lt_root3 (T s' σ s u : ℝ)
    (hu : u ∈ pinSet LG (fun _ => T) s' (rootTermFix m inner rest σ s) D.bR) (hnil : inner.lonePath = []) :
    u < σ := by
  have hchild : D.bR.IsChildOf D.aR := by
    refine ⟨Subsingleton.elim _ _, m.c, ?_⟩
    rw [D.bR_path, D.aR_path]
    simp [bPath, hnil]
  exact hu.2.2.2.2.2.1 _ hchild σ (D.rootTermFix_aR σ s)

/-- **(P3) at one decoration** (time level): the root cut with the suffix terminal designated. -/
theorem protTime_rootCut3 (L γ δ : ℝ) {d : ℕ} (T s' σ s : ℝ) (hσT : σ ≤ T) (K : GNode LG.garden.tree → Mom d) :
    protTime L γ δ LG (fun _ => T) s' (rootTermFix m inner rest σ s) K =
      ∫ u in rootU3 LG m inner T σ s,
        Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode LGZ.garden (K ∘ D.gd.ι₁) D.hp.rootB * σ : ℝ) * Complex.I) *
          Complex.exp ((Real.pi * ((LGZ.garden.sign D.hp.bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            omegaNode LGZ.garden (K ∘ D.gd.ι₁) D.hp.bB * u : ℝ) * Complex.I) *
        (protTime L γ δ LGi (fun _ => σ) u (fun _ => none) (K ∘ D.gd.ι₁ ∘ D.hp.ιi) *
          (protTime L γ δ LGr (fun y => cupR m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
              (K ∘ D.gd.ι₁ ∘ D.hp.ιr) *
            (protTime L γ δ LGg (fun y => cupG m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                (K ∘ D.gd.ι₁ ∘ D.hp.ιg) *
              protTime L γ δ LGs (fun _ => u) s' (ProtCfg.term.fix rest s σ u) (K ∘ D.gd.ι₂)))) := by
  rw [protTime_pin L γ δ LG (fun _ => T) s' (rootTermFix m inner rest σ s) K D.bR (D.rootTermFix_bR σ s),
    ← integral_indicator (measurableSet_rootU3 LG m inner T σ s)]
  congr 1
  funext u
  by_cases hU : u ∈ rootU3 LG m inner T σ s
  · rw [Set.indicator_of_mem (D.rootU3_sub T s' σ s hU), Set.indicator_of_mem hU]
    rw [show Function.update (rootTermFix m inner rest σ s) D.bR (some u) = D.fixU3 σ s u from rfl,
      D.protTime_glueR3 L γ δ T s' σ s u hU.2.le hU.1.2.2.2.1.le K,
      D.protTime_pairR L γ δ T s' σ u hσT hU.1.2.2.2.1.le]
    simp only [Function.comp_assoc]
    ring
  · rw [Set.indicator_of_notMem hU]
    by_cases hP : u ∈ pinSet LG (fun _ => T) s' (rootTermFix m inner rest σ s) D.bR
    · rw [Set.indicator_of_mem hP]
      rw [show Function.update (rootTermFix m inner rest σ s) D.bR (some u) = D.fixU3 σ s u from rfl]
      by_cases hus : u ≤ s
      · exact D.protTime_fixU3_zero L γ δ T s' σ s u hus K
      · have hσu : σ ≤ u := by
          by_contra hlt
          exact hU ⟨⟨by rw [← D.layer_bR]; exact hP.1, by rw [← D.layer_bR]; exact hP.2.1, hP.2.2.1,
            hP.2.2.2.1, lt_of_not_ge hlt⟩, lt_of_not_ge hus⟩
        have hin : inner.lonePath ≠ [] := fun hnil =>
          absurd (D.pinSet_lt_root3 T s' σ s u hP hnil) (not_lt.mpr hσu)
        rw [D.protTime_glueR3 L γ δ T s' σ s u (le_of_not_ge hus) hP.2.2.2.1.le K,
          D.protTime_pairR_zero L γ δ T s' σ u hσu hin, zero_mul]
    · rw [Set.indicator_of_notMem hP]

end RootData

end WaveTurbulence.Flower.ProtCut
