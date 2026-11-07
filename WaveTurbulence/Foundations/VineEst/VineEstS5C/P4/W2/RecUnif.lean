/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecDisp

/-! # P4-W2 (session 14, step 4a): uniformity of the dispatch constants in `(ν, δ, 𝔇, C₂, L)`

`DispK01 P K0`, `DispK2 P Rb K0` read `P` only through `P.d`, `P.η` (the structures `SepT`, `SepTC`, `CertTerm`, `RemC`, `CertSrc`, `Src` have fields whose types
read only these two).  `WTParams.setLast P ν δ D C₂ L` changes the last five fields, so the structures transport along it by copying the fields
(`Src.setLast`), and `DispK01 P K0 → DispK01 (P.setLast ..) K0` (resp. `DispK2`).  With structure eta, `P = (P.setLast ..).setLast P.ν P.δ P.D P.C₂ P.L`,
so the transport is symmetric.  Consequently the constants `K0` of `exc_dispatch_k01'`, `exc_dispatch_k2'` obtained at ONE reference parameter serve every parameter that
differs from it only in `ν, δ, 𝔇, C₂, L` (`exists_K0_uniform`).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate

/-- Change the last five fields of a parameter vector. -/
@[reducible] def setLastP (P : WTParams) (ν δ : ℝ) (D : ℕ) (C₂ L : ℝ) : WTParams :=
  { P with ν := ν, δ := δ, D := D, C₂ := C₂, L := L }

variable {P : WTParams} {ν δ : ℝ} {D : ℕ} {C₂ L : ℝ}

def sepTSL {Wm : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ} (s : SepT P Wm B q CJ CM) :
    SepT (setLastP P ν δ D C₂ L) Wm B q CJ CM where
  c := s.c
  J := s.J
  M := s.M
  hcell := s.hcell
  hint := s.hint
  hCJ := s.hCJ
  hCM := s.hCM
  hJ := s.hJ
  hM := s.hM

def sepTCSL {Wm : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ} (s : SepTC P Wm B q CJ CM) :
    SepTC (setLastP P ν δ D C₂ L) Wm B q CJ CM where
  toSepT := sepTSL s.toSepT
  Bc := s.Bc
  hBcB := s.hBcB
  hBci := s.hBci
  hcont := s.hcont

def certTermSL {Wm : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CJ CM : ℝ} {f : ℝ → ℝ → Mom P.d → ℂ}
    (s : CertTerm P Wm B q CJ CM f) : CertTerm (setLastP P ν δ D C₂ L) Wm B q CJ CM f where
  toSepTC := sepTCSL s.toSepTC
  V := s.V
  hV := s.hV

def remCSL {Λ₂ : ℕ} {B : Set (Fin 2 → ℝ)} {q : Fin 2 → ℝ} {CR : ℝ} (s : RemC P Λ₂ B q CR) :
    RemC (setLastP P ν δ D C₂ L) Λ₂ B q CR where
  f := s.f
  Bc := s.Bc
  hcell := s.hcell
  hint := s.hint
  hBcB := s.hBcB
  hBci := s.hBci
  hcont := s.hcont
  hCR := s.hCR
  hX := s.hX

variable {β : Type*} {S : SepTerms β P.d} {RQ RT : β → ℝ → ℝ → Mom P.d → ℂ} {q2 q4 qh : ℝ}

def certSrcSL (s : CertSrc P S q2 q4 qh) : CertSrc (setLastP P ν δ D C₂ L) S q2 q4 qh where
  good := s.good
  BQ := s.BQ
  qQ := s.qQ
  BT := s.BT
  qT := s.qT
  cc := s.cc
  cT := s.cT
  CJq := s.CJq
  CMq := s.CMq
  CJt := s.CJt
  CMt := s.CMt
  cq s' b i := certTermSL (s.cq s' b i)
  ct s' b j := certTermSL (s.ct s' b j)
  cq_c := s.cq_c
  ct_c := s.ct_c
  win_q := s.win_q
  win_t := s.win_t

def srcSL (s : Src P S RQ RT q2 q4 qh) : Src (setLastP P ν δ D C₂ L) S RQ RT q2 q4 qh where
  toCertSrc := certSrcSL s.toCertSrc
  CRq := s.CRq
  CRt := s.CRt
  rq s' b := remCSL (s.rq s' b)
  rt s' b := remCSL (s.rt s' b)
  hRQ := s.hRQ
  hRT := s.hRT
  win_rq := s.win_rq
  win_rt := s.win_rt


def xcrossSL (src : Src P S RQ RT q2 q4 qh) (xs : K2.XCross P src) :
    K2.XCross (setLastP P ν δ D C₂ L) (srcSL (ν := ν) (δ := δ) (D := D) (C₂ := C₂) (L := L) src) where
  Bq := xs.Bq
  Bcq := xs.Bcq
  Bt := xs.Bt
  Bct := xs.Bct
  xJq := xs.xJq
  xJt := xs.xJt
  CJxq := xs.CJxq
  CJxt := xs.CJxt
  Kx := xs.Kx
  hKx := xs.hKx
  CJxq_nonneg := xs.CJxq_nonneg
  CJxt_nonneg := xs.CJxt_nonneg
  CJxq_le := xs.CJxq_le
  CJxt_le := xs.CJxt_le
  xq_win := xs.xq_win
  xt_win := xs.xt_win
  xq_cont := xs.xq_cont
  xt_cont := xs.xt_cont
  xq_norm := xs.xq_norm
  xt_norm := xs.xt_norm
  xq_M := xs.xq_M
  xt_M := xs.xt_M
  xq_lo := xs.xq_lo
  xq_hi := xs.xq_hi
  xt_lo := xs.xt_lo
  xt_hi := xs.xt_hi

universe u
variable {A : ℝ}

open Classical in
theorem dispK01_setLast {K0 : ℝ≥0∞} (h : DispK01.{u} P K0) (ν δ : ℝ) (D : ℕ) (C₂ L : ℝ) :
    DispK01.{u} (setLastP P ν δ D C₂ L) K0 := by
  unfold DispK01 at h ⊢
  intro D' hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 caseA β _ S RQ RT q2 q4 qh src bs1 bs2 rA rB hgood c hk Bx hh
  exact h D' hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 caseA S RQ RT (srcSL (P := setLastP P ν δ D C₂ L) (ν := P.ν) (δ := P.δ) (D := P.D) (C₂ := P.C₂) (L := P.L) src : Src P S RQ RT q2 q4 qh)
    bs1 bs2 rA rB hgood c hk Bx hh

open Classical in
theorem dispK2_setLast {Rb : ℝ} {K0 : ℝ≥0∞} (h : DispK2.{u} P Rb K0) (ν δ : ℝ) (D : ℕ) (C₂ L : ℝ) :
    DispK2.{u} (setLastP P ν δ D C₂ L) Rb K0 := by
  unfold DispK2 at h ⊢
  intro D' hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA β _ S RQ RT q2 q4 qh src xs Kx0 hKx1 hKx hqh hq4 hq2 hRb bs1 bs2 rA rB hgood c hk Bx hh
  exact h D' hI hwN hwDec vp vb ε ex ey hfl t0 s1 t1 sa ta hsa hsb hab caseA S RQ RT
    (srcSL (P := setLastP P ν δ D C₂ L) (ν := P.ν) (δ := P.δ) (D := P.D) (C₂ := P.C₂) (L := P.L) src : Src P S RQ RT q2 q4 qh)
    (fun hg => xcrossSL (P := setLastP P ν δ D C₂ L) (ν := P.ν) (δ := P.δ) (D := P.D) (C₂ := P.C₂) (L := P.L) src (xs hg)) Kx0 hKx1 hKx hqh hq4 hq2 hRb bs1 bs2 rA rB hgood c hk Bx hh

/-- **Uniform dispatch constant (kinds `0`, `1`)**: one `K0` serves every `(ν, δ, 𝔇, C₂, L)` with the ambient data `AmbP`, for fixed `(d, γ, η, φin, τ, φ, C₁)`. -/
theorem dispK01_uniform (P₀ : WTParams) :
    ∃ K0 : ℝ≥0∞, K0 ≠ ⊤ ∧ 1 ≤ K0 ∧ ∀ (ν δ : ℝ) (D : ℕ) (C₂ L : ℝ), AmbP A (setLastP P₀ ν δ D C₂ L) →
      DispK01.{u} (setLastP P₀ ν δ D C₂ L) K0 := by
  by_cases h : ∃ (ν δ : ℝ) (D : ℕ) (C₂ L : ℝ), AmbP A (setLastP P₀ ν δ D C₂ L)
  · obtain ⟨ν0, δ0, D0, C0, L0, G0⟩ := h
    obtain ⟨K0, hK0, h1, hd⟩ := exc_dispatch_k01'.{u} G0
    exact ⟨K0, hK0, h1, fun ν δ D C₂ L _ => dispK01_setLast hd ν δ D C₂ L⟩
  · exact ⟨1, ENNReal.one_ne_top, le_rfl, fun ν δ D C₂ L G => absurd ⟨ν, δ, D, C₂, L, G⟩ h⟩

/-- **Uniform dispatch constant (kind `2`)** at the clock radius `Rb`. -/
theorem dispK2_uniform (P₀ : WTParams) (Rb : ℝ) :
    ∃ K0 : ℝ≥0∞, K0 ≠ ⊤ ∧ 1 ≤ K0 ∧ ∀ (ν δ : ℝ) (D : ℕ) (C₂ L : ℝ), AmbP A (setLastP P₀ ν δ D C₂ L) →
      DispK2.{u} (setLastP P₀ ν δ D C₂ L) Rb K0 := by
  by_cases h : ∃ (ν δ : ℝ) (D : ℕ) (C₂ L : ℝ), AmbP A (setLastP P₀ ν δ D C₂ L)
  · obtain ⟨ν0, δ0, D0, C0, L0, G0⟩ := h
    obtain ⟨K0, hK0, h1, hd⟩ := exc_dispatch_k2'.{u} G0 Rb
    exact ⟨K0, hK0, h1, fun ν δ D C₂ L _ => dispK2_setLast hd ν δ D C₂ L⟩
  · exact ⟨1, ENNReal.one_ne_top, le_rfl, fun ν δ D C₂ L G => absurd ⟨ν, δ, D, C₂, L, G⟩ h⟩

end WaveTurbulence.VineEstS5C.P4.W2
