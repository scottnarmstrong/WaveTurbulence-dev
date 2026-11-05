/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceRealFold
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.MomentumFactors

/-! # Literal real resonant recursion for the actual type1 source fold -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree

/-- The actual real type1 source fold is twice the resonant integral of
its three actual real child folds. Only the original input norm and the
unmarked root are needed; no recursive Mstar identity is assumed. -/
theorem realCplFold_type1 {d w : ℕ} (hd : 3 ≤ d)
    (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl) {F : Mom d → ℝ} {B : ℝ}
    (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (Z : Finset (Fin w × Path)) (a b : Fin w × Path) (hab : Indep a b) (r : Mom d)
    (hroot : a ∉ Z) :
    realCplFold F (.type1 c Q₁ Q₂ Q₃) Z a b r =
    2*resIntegral (fun k₁ k₂ k₃ =>
      realCplFold F Q₁ Z (addrExt a [0]) (addrExt b [c.partner 0]) k₁ *
      realCplFold F Q₂ Z (addrExt b [1]) (addrExt a [1]) k₂ *
      realCplFold F Q₃ Z (addrExt a [2]) (addrExt b [c.partner 2]) k₃) r := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul,ofReal_realCplFold hd (.type1 c Q₁ Q₂ Q₃)
    (by omega) (by omega) hB hF Z a b hab r 0,
    addressAppAlong_type1_root_unmarked hd c Q₁ Q₂ Q₃ (by omega) (by omega) hB hF Z a b hab r hroot]
  simp only [Complex.ofReal_ofNat]
  rw [← deltaInner_source_momentum]
  apply congrArg NTSP.deltaInner
  funext x y
  rw [← ofReal_realCplFold hd Q₁ (by omega) (by omega) hB hF Z _ _ (hab.ext _ _) _ 0,
    ← ofReal_realCplFold hd Q₂ (by omega) (by omega) hB hF Z _ _ (hab.symm.ext _ _) _ 0,
    ← ofReal_realCplFold hd Q₃ (by omega) (by omega) hB hF Z _ _ (hab.ext _ _) _ 0]
  simp only [childVals,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Matrix.tail_cons,Complex.ofReal_mul]

end WaveTurbulence.RegAsymp
