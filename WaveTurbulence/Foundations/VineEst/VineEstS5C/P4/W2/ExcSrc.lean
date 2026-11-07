/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.ExcWinWrap
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Index

/-! # P4-W2 (session 7, step 3c): the certified source of a bundle (`Src`) and the generic bundle summand

`bundlePtG caseA S bs₁ bs₂ rA rB RQ RT`: the summand `c` of a bundle at a point (the shape of `bundlePt` and of BOT-DECOMP's `botPt`).
`Src P S RQ RT q₂ q₄ qₕ`: for every index `b` the certified couple and tree terms (low window `false`, high window `true`, with the window facts `WinOK` of `ExcWin`),
the remainders `RQ b`, `RT b` as `RemC`s on the two windows with their window facts, the common coefficients and the sizes.  `Src.sz`: the product of the sizes entering the row
bounds of the summand `c`.  `Ksp`, `spConst_le*`: the spatial constants of `spConst`. -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open WaveTurbulence WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.VineEstS3.FS WaveTurbulence.VineEstS5A WaveTurbulence.VineEstS4c
  WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P4 MeasureTheory
open scoped ENNReal ComplexConjugate

variable {P : WTParams}

open Classical in
/-- The summand `c` of a bundle at the point `(t₀, s₁, t₁, x, y)` (the shape of `bundlePt` and `botPt`). -/
noncomputable def bundlePtG (caseA : Prop) {β : Type*} [DecidableEq β] {d : ℕ} (S : SepTerms β d) (bs₁ bs₂ rA rB : Finset β)
    (RQ RT : β → ℝ → ℝ → Mom d → ℂ) (t0 s1 t1 : ℝ) (x y : Mom d) : Ch S bs₁ bs₂ rA rB → ℂ :=
  Sum.elim (fun c => if caseA then ptP S bs₁ bs₂ t0 s1 t1 x y c else -(starRingEnd ℂ) (ptP S bs₁ bs₂ t0 t1 s1 y x c))
    (fun c => ptR S RQ RT rA rB t0 s1 t1 x y c)

/-- The certified terms of a bundle: certified couple and tree terms on the low (`false`) and the high (`true`) window. -/
structure CertSrc (P : WTParams) {β : Type*} (S : SepTerms β P.d) (q2 q4 qh : ℝ) where
  good : β → Prop
  BQ : Bool → Set (Fin 2 → ℝ)
  qQ : Bool → Fin 2 → ℝ
  BT : Bool → Set (Fin 2 → ℝ)
  qT : Bool → Fin 2 → ℝ
  cc : β → ℝ
  cT : β → ℝ
  CJq : β → ℝ
  CMq : β → ℝ
  CJt : β → ℝ
  CMt : β → ℝ
  cq : ∀ (s : Bool) (b : β) (i : Fin (S.mQ b)), CertTerm P (30 * P.d) (BQ s) (qQ s) (CJq b) (CMq b) (S.sQ b i)
  ct : ∀ (s : Bool) (b : β) (j : Fin (S.mT b)), CertTerm P 0 (BT s) (qT s) (CJt b) (CMt b) (S.sT b j)
  cq_c : ∀ s b i, (cq s b i).c = cc b
  ct_c : ∀ s b j, (ct s b j).c = cT b
  win_q : ∀ b, good b → ∀ i,
    WinOK (cq false b i).V (cq false b i).Bc (Set.Ioo q4 (q4 + 1)) (Set.Ioo q2 (q2 + 1)) false ∧
    WinOK (cq true b i).V (cq true b i).Bc (Set.Ioo qh (qh + 1)) (Set.Ioo q2 (q2 + 1)) false
  win_t : ∀ b, good b → ∀ j,
    WinOK (ct false b j).V (ct false b j).Bc (Set.Ioo q4 (q4 + 1)) (Set.Ioo q2 (q2 + 1)) true ∧
    WinOK (ct true b j).V (ct true b j).Bc (Set.Ioo qh (qh + 1)) (Set.Ioo q2 (q2 + 1)) true

/-- The certified source of a bundle: the certified terms and the remainders `RQ`, `RT` as `RemC`s on the two windows. -/
structure Src (P : WTParams) {β : Type*} (S : SepTerms β P.d) (RQ RT : β → ℝ → ℝ → Mom P.d → ℂ) (q2 q4 qh : ℝ)
    extends CertSrc P S q2 q4 qh where
  CRq : β → ℝ
  CRt : β → ℝ
  rq : ∀ (s : Bool) (b : β), RemC P (30 * P.d) (BQ s) (qQ s) (CRq b)
  rt : ∀ (s : Bool) (b : β), RemC P 0 (BT s) (qT s) (CRt b)
  hRQ : ∀ s b x y, ![x, y] ∈ (rq s b).Bc → ∀ k, RQ b x y k = (rq s b).f ![x, y] k
  hRT : ∀ s b x y, ![x, y] ∈ (rt s b).Bc → ∀ k, RT b x y k = (rt s b).f ![x, y] k
  win_rq : ∀ b, good b →
    WinOK Set.univ (rq false b).Bc (Set.Ioo q4 (q4 + 1)) (Set.Ioo q2 (q2 + 1)) false ∧
    WinOK Set.univ (rq true b).Bc (Set.Ioo qh (qh + 1)) (Set.Ioo q2 (q2 + 1)) false
  win_rt : ∀ b, good b →
    WinOK Set.univ (rt false b).Bc (Set.Ioo q4 (q4 + 1)) (Set.Ioo q2 (q2 + 1)) true ∧
    WinOK Set.univ (rt true b).Bc (Set.Ioo qh (qh + 1)) (Set.Ioo q2 (q2 + 1)) true

namespace CertSrc
variable {β : Type*} {S : SepTerms β P.d} {q2 q4 qh : ℝ} (src : CertSrc P S q2 q4 qh)

/-- The size of the certified couple of the index `b`. -/
noncomputable def szQ (b : β) : ℝ := |src.cc b| * src.CJq b * src.CMq b
/-- The size of the certified tree of the index `b`. -/
noncomputable def szT (b : β) : ℝ := |src.cT b| * src.CJt b * src.CMt b

end CertSrc

namespace Src
variable {β : Type*} [DecidableEq β] {S : SepTerms β P.d} {RQ RT : β → ℝ → ℝ → Mom P.d → ℂ} {q2 q4 qh : ℝ}
  (src : Src P S RQ RT q2 q4 qh)

/-- The product of the sizes entering the row bounds of the summand `c`. -/
noncomputable def sz {bs₁ bs₂ rA rB : Finset β} : Ch S bs₁ bs₂ rA rB → ℝ :=
  Sum.elim (fun c => Sum.elim (fun c : PIdx S bs₁ => src.szQ c.1.1 * src.szT c.1.1)
      (Sum.elim (fun c : PIdx S bs₁ => src.szQ c.1.1 * src.szT c.1.1)
      (Sum.elim (fun c : PIdx S bs₁ => src.szQ c.1.1 * src.szT c.1.1)
      (Sum.elim (fun c : PIdx S bs₂ => src.szQ c.1.1 * src.szT c.1.1)
      (Sum.elim (fun c : PIdx S bs₂ => src.szQ c.1.1 * src.szT c.1.1)
      (fun c : PIdx S bs₂ => src.szQ c.1.1 * src.szT c.1.1))))) c)
    (fun c => Sum.elim (fun c : RIdx S rA => Sum.elim (fun _ => src.szQ c.1.1 * src.CRt c.1.1)
        (Sum.elim (fun _ => src.CRq c.1.1 * src.szT c.1.1) (fun _ => src.CRq c.1.1 * src.CRt c.1.1)) c.2)
      (fun c : RIdx S rB => Sum.elim (fun _ => src.szQ c.1.1 * src.CRt c.1.1)
        (Sum.elim (fun _ => src.CRq c.1.1 * src.szT c.1.1) (fun _ => src.CRq c.1.1 * src.CRt c.1.1)) c.2) c)

end Src

/-- The spatial constant bounding every `spConst` and remainder constant. -/
noncomputable def Ksp (d : ℕ) : ℝ := (2 : ℝ) ^ (90 * d) * (d : ℝ) ^ (120 * d)

theorem one_le_Ksp {d : ℕ} (hd : 1 ≤ d) : 1 ≤ Ksp d := by
  unfold Ksp
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by exact_mod_cast hd))

theorem spConst_le {d wN wDec : ℕ} (hd : 1 ≤ d) (hwN : wN + 1 = 30 * d) (hwDec : wDec = 30 * d) (c βF βG : ℝ)
    (hF : 0 ≤ βF) (hG : 0 ≤ βG) :
    spConst d wN wDec c βF βG ≤ Ksp d * (|c| * βF * βG) := by
  unfold spConst Ksp
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : (2 : ℝ) ^ wN * (2 : ℝ) ^ wDec ≤ (2 : ℝ) ^ (90 * d) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (d : ℝ) ^ wN * (d : ℝ) ^ wN * (d : ℝ) ^ wN ≤ (d : ℝ) ^ (120 * d) := by
    rw [← pow_add, ← pow_add]; exact pow_le_pow_right₀ hd' (by omega)
  have h3 : 0 ≤ |c| * βF * βG := by positivity
  calc |c| * ((2 : ℝ) ^ wN * (d : ℝ) ^ wN * ((2 : ℝ) ^ 0 * (d : ℝ) ^ wN * βG) * ((2 : ℝ) ^ wDec * (d : ℝ) ^ wN * βF))
      = ((2 : ℝ) ^ wN * (2 : ℝ) ^ wDec * ((d : ℝ) ^ wN * (d : ℝ) ^ wN * (d : ℝ) ^ wN)) * (|c| * βF * βG) := by ring
    _ ≤ ((2 : ℝ) ^ (90 * d) * (d : ℝ) ^ (120 * d)) * (|c| * βF * βG) := by
        apply mul_le_mul_of_nonneg_right _ h3
        exact mul_le_mul h1 h2 (by positivity) (by positivity)

end WaveTurbulence.VineEstS5C.P4.W2
