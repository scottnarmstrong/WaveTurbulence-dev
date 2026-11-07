/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.Bot.Dict

/-! # BOT-DECOMP: `bundle_decomp_bot` (mirror of `P1.bundle_decomp` and `P4.bundle_decomp_mirror`)

The exact bottom bundle `psiBot` equals `botFrame * bFac * νA * (botPieces + botRem)` (pieces (a)-(c) of TARGET L1925-L1951 plus the remainder rows),
valid for `t₁ ∈ (L₄, L₄+1]`, `t₀ ∈ [L₂, L₂+1]` (`bundle_decomp_bot`), and, when the clock `s₁` instead of `t₁` is in the window (F-WINDOW: the other static layer
case), `psiBot = botFrame * bFac * νA * (- conj botPiecesM + botRem)` (`bundle_decomp_bot_mirror`, via `P4.replSum_mirror`).
Hypotheses: `BotSurj` (`botSurj_of_state`), `BotLayers` (`botLayers_of_state`), `RealityAll` (PL234).
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.VineEstS5C.P4.Bot
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.VineEstS5B2 WaveTurbulence.Links WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LGSpine
  WaveTurbulence.ConjCoh TTree WaveTurbulence.VineEstS4c WaveTurbulence.VineEstS5C

set_option linter.unusedSectionVars false

section
variable {w : ℕ} {ι : Type*} {d : ℕ} [Fintype ι] [DecidableEq ι] (p : ℕ) (kind : Bool) (pstar : ι)
  (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)

open Classical in
/-- The pieces (a)-(c) of TARGET L1925-L1951 for the approximants `Qf = botQfam`, `Tf = botTfam`, at `(t0, s1, t1, x, y)`. -/
noncomputable def botPieces (κ : KPar d) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  pieceA1 (botA p kind pstar A c0) (botTfam pstar κ A) (cswap (botQfam pstar κ A)) t0 s1 t1 x y -
    pieceA2 (botB p kind pstar A c0) (botQfam pstar κ A) (cconj (botTfam pstar κ A)) t0 s1 t1 x y +
  (if t0 < t1 ∧ t0 < s1 then
    pieceKQ (botA p kind pstar A c0) (botQfam pstar κ A) (botTfam pstar κ A) t0 s1 t1 x y +
      pieceTQ (botA p kind pstar A c0) (botQfam pstar κ A) (botTfam pstar κ A) t0 s1 t1 x +
      pieceKT (botB p kind pstar A c0) (botQfam pstar κ A) (botTfam pstar κ A) t0 s1 t1 x y +
      pieceTT (botB p kind pstar A c0) (botQfam pstar κ A) (botTfam pstar κ A) t0 s1 t1 x else 0)

/-- The remainder rows: `∑_{botA} remA - ∑_{botB} remB`. -/
noncomputable def botRem (κ : KPar d) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  ∑ b ∈ botA p kind pstar A c0, remA (botQfam pstar κ A) (botTfam pstar κ A) (botRemQ pstar κ (botQfam pstar κ A))
      (botRemT pstar κ (botTfam pstar κ A)) b t0 s1 t1 x y -
    ∑ b ∈ botB p kind pstar A c0, remB (botQfam pstar κ A) (botTfam pstar κ A) (botRemQ pstar κ (botQfam pstar κ A))
      (botRemT pstar κ (botTfam pstar κ A)) b t0 s1 t1 x y

open Classical in
/-- The pieces of the mirrored decomposition: the pieces of `botPieces` for `(botB, botA)` at `(t₀, t₁, s₁, y, x)` (before the conjugation and the sign). -/
noncomputable def botPiecesM (κ : KPar d) (t0 s1 t1 : ℝ) (x y : Mom d) : ℂ :=
  pieceA1 (botB p kind pstar A c0) (botTfam pstar κ A) (cswap (botQfam pstar κ A)) t0 t1 s1 y x -
    pieceA2 (botA p kind pstar A c0) (botQfam pstar κ A) (cconj (botTfam pstar κ A)) t0 t1 s1 y x +
  (if t0 < s1 ∧ t0 < t1 then
    pieceKQ (botB p kind pstar A c0) (botQfam pstar κ A) (botTfam pstar κ A) t0 t1 s1 y x +
      pieceTQ (botB p kind pstar A c0) (botQfam pstar κ A) (botTfam pstar κ A) t0 t1 s1 y +
      pieceKT (botA p kind pstar A c0) (botQfam pstar κ A) (botTfam pstar κ A) t0 t1 s1 y x +
      pieceTT (botA p kind pstar A c0) (botQfam pstar κ A) (botTfam pstar κ A) t0 t1 s1 y else 0)

variable {p kind pstar A c0}

open Classical in
/-- **BOT-DECOMP, goal 1.**  The exact bottom bundle equals the frame times `bFac` times `νA` times the pieces (a)-(c) plus the remainder rows (the
leading term (d) is cancelled by `hreal`). -/
theorem bundle_decomp_bot (hR : P1.RealityAll) (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ)
    (h1 : (zpQ4 A pstar : ℝ) < (botVars κ A c0 pstar x u).2.2.1)
    (h1' : (botVars κ A c0 pstar x u).2.2.1 ≤ zpQ4 A pstar + 1)
    (h0 : (zpQ2 A pstar : ℝ) ≤ (botVars κ A c0 pstar x u).1)
    (h0' : (botVars κ A c0 pstar x u).1 ≤ zpQ2 A pstar + 1) :
    psiBot p kind κ A c0 pstar x t u = botFrame κ A c0 pstar x u * bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u *
      (((nuOf A pstar : ℤˣ) : ℂ) *
      (botPieces p kind pstar A c0 κ (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1
          (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2 +
        botRem p kind pstar A c0 κ (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1
          (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2)) := by
  obtain ⟨τ, hbij, hrel⟩ := hZ.twin
  rw [psiBot_eq_repl p kind κ A c0 pstar (botQfam pstar κ A) (botTfam pstar κ A) τ hbij
    (fun G hG => ⟨(hrel G hG).1, (hrel G hG).2.1⟩) hZ.coherent x t u]
  congr 2
  generalize botVars κ A c0 pstar x u = v at *
  obtain ⟨t0, s1, t1, x', y'⟩ := v
  simp only at h1 h1' h0 h0' ⊢
  have hd := replSum_decomp_ext (botA p kind pstar A c0) (botB p kind pstar A c0) (botLq pstar) (botLt pstar) (zpQ4 A pstar)
    (botTrQ pstar) (botTrT pstar)
    (botEx pstar κ A) (botEt pstar κ A) (botQ0 pstar κ A) (botT0 pstar κ A) (cswap (botQfam pstar κ A))
    (cconj (botTfam pstar κ A))
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun b _ => b ∈ canonFinsetK p kind A c0 ∧ zpQ4 A pstar < botLq pstar b)
    (fun b _ => b ∈ canonFinsetK p kind A c0 ∧ zpQ4 A pstar < botLt pstar b)
    (fun b _ t s k ht => by simp [botEx, not_lt.mpr ht])
    (fun b _ t s k ht => by simp [botEt, not_lt.mpr ht])
    (fun b _ s k hb => bot_hQ0 p kind pstar A c0 hZ hL κ hb.1 hb.2 s k)
    (fun b _ s k hb => bot_hT0 p kind pstar A c0 hZ hL κ hb.1 hb.2 s k)
    (bot_hsub p kind pstar A c0)
    (fun b t s k => by simp [cswap, botQfam])
    (fun b t s k => by simp [cconj, botTfam])
    t0 s1 t1 x' y' h1'
    (fun _ b hb hgt _ => ⟨bot_mem_of_bs p kind pstar A c0 (by unfold botBsU; exact hb), hgt⟩)
    (fun _ b hb hgt _ => ⟨bot_mem_of_bs p kind pstar A c0 (by unfold botBsU; exact hb), hgt⟩)
    (fun hlt => bot_hreal p kind pstar A c0 hR hZ hL κ x' h1 h1' h0 h0' hlt)
  unfold botRem
  congr 1
  refine hd.trans ?_
  simp only [botPieces, pieceDef, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
  rfl

open Classical in
/-- **Mirrored bottom decomposition (F-WINDOW).**  If the clock `s₁` (instead of `t₁`) lies in the window `(L₄, L₄+1]`, then
`psiBot = botFrame * bFac * νA * (- conj botPiecesM + botRem)`. -/
theorem bundle_decomp_bot_mirror (hR : P1.RealityAll) (hZ : BotSurj p kind pstar A c0) (hL : BotLayers p kind pstar A c0) (κ : KPar d)
    (x : GNode A.skeleton.tree → (Fin d → ℤ)) (t : Fin 3 → ℝ) (u : GBranch A.skeleton.tree → ℝ)
    (h1 : (zpQ4 A pstar : ℝ) < (botVars κ A c0 pstar x u).2.1)
    (h1' : (botVars κ A c0 pstar x u).2.1 ≤ zpQ4 A pstar + 1)
    (h0 : (zpQ2 A pstar : ℝ) ≤ (botVars κ A c0 pstar x u).1)
    (h0' : (botVars κ A c0 pstar x u).1 ≤ zpQ2 A pstar + 1) :
    psiBot p kind κ A c0 pstar x t u = botFrame κ A c0 pstar x u * bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u *
      (((nuOf A pstar : ℤˣ) : ℂ) *
      (-(starRingEnd ℂ) (botPiecesM p kind pstar A c0 κ (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1
          (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2) +
        botRem p kind pstar A c0 κ (botVars κ A c0 pstar x u).1 (botVars κ A c0 pstar x u).2.1
          (botVars κ A c0 pstar x u).2.2.1 (botVars κ A c0 pstar x u).2.2.2.1 (botVars κ A c0 pstar x u).2.2.2.2)) := by
  obtain ⟨τ, hbij, hrel⟩ := hZ.twin
  rw [psiBot_eq_repl p kind κ A c0 pstar (botQfam pstar κ A) (botTfam pstar κ A) τ hbij
    (fun G hG => ⟨(hrel G hG).1, (hrel G hG).2.1⟩) hZ.coherent x t u]
  congr 2
  generalize botVars κ A c0 pstar x u = v at *
  obtain ⟨t0, s1, t1, x', y'⟩ := v
  simp only at h1 h1' h0 h0' ⊢
  have hmemU : ∀ b, (b ∈ botB p kind pstar A c0 ∨ b ∈ botA p kind pstar A c0) → b ∈ canonFinsetK p kind A c0 := fun b hb =>
    bot_mem_of_bs p kind pstar A c0 ((mem_botBsU p kind pstar A c0).mpr hb.symm)
  have hd := replSum_decomp_ext (botB p kind pstar A c0) (botA p kind pstar A c0) (botLq pstar) (botLt pstar) (zpQ4 A pstar)
    (botTrQ pstar) (botTrT pstar)
    (botEx pstar κ A) (botEt pstar κ A) (botQ0 pstar κ A) (botT0 pstar κ A) (cswap (botQfam pstar κ A))
    (cconj (botTfam pstar κ A))
    (fun _ _ _ _ => 0) (fun _ _ _ _ => 0)
    (fun b _ => b ∈ canonFinsetK p kind A c0 ∧ zpQ4 A pstar < botLq pstar b)
    (fun b _ => b ∈ canonFinsetK p kind A c0 ∧ zpQ4 A pstar < botLt pstar b)
    (fun b _ t s k ht => by simp [botEx, not_lt.mpr ht])
    (fun b _ t s k ht => by simp [botEt, not_lt.mpr ht])
    (fun b _ s k hb => bot_hQ0 p kind pstar A c0 hZ hL κ hb.1 hb.2 s k)
    (fun b _ s k hb => bot_hT0 p kind pstar A c0 hZ hL κ hb.1 hb.2 s k)
    (fun b hb hq ht => by
      have := bot_hsub p kind pstar A c0 b ((mem_botBsU p kind pstar A c0).mpr (mem_union_cl.mp hb).symm) hq ht
      exact ⟨this.2, this.1⟩)
    (fun b t s k => by simp [cswap, botQfam])
    (fun b t s k => by simp [cconj, botTfam])
    t0 t1 s1 y' x' h1'
    (fun _ b hb hgt _ => ⟨hmemU b (mem_union_cl.mp hb), hgt⟩)
    (fun _ b hb hgt _ => ⟨hmemU b (mem_union_cl.mp hb), hgt⟩)
    (fun hlt => by
      have hz := bot_hreal p kind pstar A c0 hR hZ hL κ y' h1 h1' h0 h0' hlt
      convert hz using 4 <;> first | rfl | (ext b; rw [mem_botBsU p kind pstar A c0]; simp [or_comm]))
  rw [replSum_mirror]
  unfold botRem
  congr 2
  congr 1
  refine hd.trans ?_
  simp only [botPiecesM, pieceDef, zero_mul, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]
  rfl

end
end WaveTurbulence.VineEstS5C.P4.Bot
