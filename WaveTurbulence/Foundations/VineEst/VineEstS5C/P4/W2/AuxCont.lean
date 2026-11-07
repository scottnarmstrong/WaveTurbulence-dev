/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W13.SFFam
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.AuxAe

/-! # P4-W2 AUX (a'): `SepTC` and the continuity of the certified time factors of W1

`SepTC`: a `P2.SepT` whose time factor is continuous on a set `Bc ⊆ B` with `Bc ⊆ closure (interior Bc)` (packaging of the hypotheses of the
slot-general row lemmas `sepRowWS`, `jointRowWS`).

The certified time factors of W1 are `padJ (clampJ q ·)` with `q` the gate level (`L₄` for a low root, `Lₕ` for a high root); `clampJ q Jc` is
continuous on `{ts 0 ≥ q}` and on `{ts 0 < q}`, not across `ts 0 = q`.  Hence (`certC`, `certT`):
* on the HIGH window `winCh` / `winTh` (`t ≥ Lₕ ≥ q`) every `J i` is continuous;
* on the LOW window `winCl` / `winTl`: continuous on `∩ {ts 0 < L₄ + 1}` always, and on all of the window when the root layer is `≤ L₄`
  (`q = L₄`) or the object is trivial.  The excluded line `t = L₄ + 1` is the line `t = q` of a high root with `q = L₄ + 1`, where the
  identity set `V` of the expansion has `t ≠ q` anyway (`ObjExp.term` is the fallback there). -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4.W13 WaveTurbulence.Links WaveTurbulence.Reg
  WaveTurbulence.LGSpine TTree WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5C WaveTurbulence.ZpSurj WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.VineEstS5C.P1
  Set WaveTurbulence.VineEstS3.FS

/-- A separated term whose time factor is continuous on `Bc ⊆ B`, `Bc ⊆ closure (interior Bc)`. -/
structure SepTC (P : WTParams) (Wm : ℕ) (B : Set (Fin 2 → ℝ)) (q : Fin 2 → ℝ) (CJ CM : ℝ) extends SepT P Wm B q CJ CM where
  Bc : Set (Fin 2 → ℝ)
  hBcB : Bc ⊆ B
  hBci : Bc ⊆ closure (interior Bc)
  hcont : ContinuousOn J Bc

/-- The case `Bc = B`. -/
def SepTC.ofCont {P : WTParams} {Wm : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ} (s : SepT P Wm B q CJ CM)
    (h : ContinuousOn s.J B) : SepTC P Wm B q CJ CM where
  toSepT := s
  Bc := B
  hBcB := subset_rfl
  hBci := s.hint
  hcont := h

/-- Restriction of a window to an open set keeps the `closure (interior)` property. -/
theorem inter_open_closure_interior {B U : Set (Fin 2 → ℝ)} (hB : B ⊆ closure (interior B)) (hU : IsOpen U) :
    B ∩ U ⊆ closure (interior (B ∩ U)) := by
  intro x ⟨hxB, hxU⟩
  rw [interior_inter, hU.interior_eq]
  rw [mem_closure_iff]
  intro V hV hxV
  obtain ⟨y, hyV, hyI⟩ := mem_closure_iff.1 (hB hxB) (V ∩ U) (hV.inter hU) ⟨hxV, hxU⟩
  exact ⟨y, hyV.1, hyI, hyV.2⟩

/-! ### The clamped factor -/

theorem continuousOn_clampJ_ge {q : ℝ} {Jc : (Fin 2 → ℝ) → ℂ} (hJ : Continuous Jc) :
    ContinuousOn (clampJ q Jc) {ts | q ≤ ts 0} := by
  have hc : Continuous fun ts : Fin 2 → ℝ => Jc ![min (ts 0) (q + 1), ts 1] := by
    refine hJ.comp (continuous_pi fun l => ?_)
    fin_cases l
    · exact ((continuous_apply 0).min continuous_const)
    · exact continuous_apply 1
  refine hc.continuousOn.congr fun ts hts => ?_
  unfold clampJ
  rw [if_neg (not_lt.2 hts)]

theorem continuousOn_clampJ_lt {q : ℝ} {Jc : (Fin 2 → ℝ) → ℂ} :
    ContinuousOn (clampJ q Jc) {ts | ts 0 < q} := by
  refine (continuousOn_const (c := (0 : ℂ))).congr fun ts hts => ?_
  unfold clampJ
  exact if_pos hts

theorem continuous_padJ {m₀ : ℕ} {J₀ : Fin m₀ → (Fin 2 → ℝ) → ℂ} (h : ∀ i, Continuous (J₀ i)) (i : Fin (max m₀ 1)) :
    Continuous (padJ J₀ i) := by
  unfold padJ
  by_cases hi : i.val < m₀
  · rw [dif_pos hi]; exact h _
  · rw [dif_neg hi]; exact continuous_const

/-- The time factors of the padded clamped expansion are continuous on each side of `ts 0 = q`. -/
def JContLevel (q : ℝ) (J : (Fin 2 → ℝ) → ℂ) : Prop :=
  ContinuousOn J {ts | q ≤ ts 0} ∧ ContinuousOn J {ts | ts 0 < q}

theorem jContLevel_pad {m₀ : ℕ} {q : ℝ} {J₀ : Fin m₀ → (Fin 2 → ℝ) → ℂ} (h : ∀ i, Continuous (J₀ i)) (i : Fin (max m₀ 1)) :
    JContLevel q (padJ (fun j => clampJ q (J₀ j)) i) := by
  unfold padJ
  by_cases hi : i.val < m₀
  · rw [dif_pos hi]; exact ⟨continuousOn_clampJ_ge (h _), continuousOn_clampJ_lt⟩
  · rw [dif_neg hi]; exact ⟨continuousOn_const, continuousOn_const⟩

theorem jContLevel_padSel {m₀ : ℕ} {q : ℝ} {fl : Prop} [Decidable fl] {J₀ : Fin m₀ → (Fin 2 → ℝ) → ℂ}
    (h : ∀ i, Continuous (J₀ i)) (i : Fin (max m₀ 1)) :
    JContLevel q (padJ (fun j => K2.clampSel fl q (J₀ j)) i) := by
  unfold padJ
  by_cases hi : i.val < m₀
  · rw [dif_pos hi]; exact ⟨K2.clampSel_continuousOn_ge (h _), K2.clampSel_continuousOn_lt (h _)⟩
  · rw [dif_neg hi]; exact ⟨continuousOn_const, continuousOn_const⟩

theorem JContLevel.mono_ge {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} (h : JContLevel q J) {B : Set (Fin 2 → ℝ)}
    (hB : ∀ ts ∈ B, q ≤ ts 0) : ContinuousOn J B := h.1.mono fun ts hts => hB ts hts

theorem JContLevel.mono_lt {q : ℝ} {J : (Fin 2 → ℝ) → ℂ} (h : JContLevel q J) {B : Set (Fin 2 → ℝ)}
    (hB : ∀ ts ∈ B, ts 0 < q) : ContinuousOn J B := h.2.mono fun ts hts => hB ts hts

theorem ofCont_jContLevel {P : WTParams} {n W : ℕ} {T : Set (Fin 2 → ℝ)} {F : (Fin 2 → ℝ) → Mom P.d → ℂ} {cost : ℝ}
    (E : ContExp P n W T F cost) (q : ℝ) (f : ℝ → ℝ → Mom P.d → ℂ) (V : Set (Fin 2 → ℝ))
    (hV : ∀ t s : ℝ, ![t, s] ∈ V → ∀ k, f t s k = ∑ i, sepTerm (P.δ ^ n) (clampJ q (E.J i)) (E.M i) t s k)
    {Blo Bhi : Set (Fin 2 → ℝ)} {qlo qhi : Fin 2 → ℝ} (hclo : Blo ⊆ cell qlo) (hilo : Blo ⊆ closure (interior Blo))
    (hchi : Bhi ⊆ cell qhi) (hihi : Bhi ⊆ closure (interior Bhi)) (hC : 1 ≤ P.C₁) (hη : P.η ≤ 1) (hcost : 0 ≤ cost) hlo hhi
    (i : Fin (ObjCert.ofCont E q f V hV hclo hilo hchi hihi hC hη hcost hlo hhi).m) :
    JContLevel q ((ObjCert.ofCont E q f V hV hclo hilo hchi hihi hC hη hcost hlo hhi).J i) :=
  jContLevel_pad E.hJc i

end WaveTurbulence.VineEstS5C.P4.W2
