/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.CodeEval

/-!
# DH21 Propositions 7.4 and 7.5 (the latter corrected by F61)

`Q` is a well-formed regular couple code with variables `𝒩^ch = chosenSet Q.links`. `Bt` is a family
satisfying the recursion (newexp1)/(newexp2) (`BtRec`, MCB2's definitional equations), so
`B̃_Q = Bt Q (0, []) (1, [])`. `G` is **any** expansion of DH21 (maincoef3) (the data of wt-wke's
`MCExp … ζ 𝒩^ch B̃_Q`, DH21 Prop 5.1). Then
`𝒥B̃_{Q,Z}(t, s) = ∫ G_Z(α, t, s) dα[𝒩^ch ∖ Z]` (DH21 (defintcal)) satisfies:
* `maincancel` (**DH21 Prop 7.4**): `𝒥B̃_{Q,Z} = 0` if `Q` is not dominant, for every `Z ⊆ 𝒩^ch`;
* `regcplcal` (**DH21 Prop 7.5, corrected**): `𝒥B̃_{Q,Z} = (-1)^{|Z|} 𝒥ℬ_Q` if `Q` is dominant and `Z`
  is special. Here `𝒥ℬ_Q = RegCpl.JB 0 Q` is B2's solution of (recurtype1)/(recurtype2). DH21 claims
  `𝒥B̃_{Q,Z}` is independent of `Z`. The factor `(-1)^{|Z|}` comes from `𝒥_{α[ ],μ} = -I_μ`
  (Lemma 5.8, F61).
The time arguments range over `[0, 1]`. The statements hold for every expansion `G`.
-/

@[expose] public section

namespace WaveTurbulence.Cancel

open TTree WaveTurbulence.Reg WaveTurbulence.ClassJR WaveTurbulence.Links Set

variable {Bt : RegCpl → Addr → Addr → TCoef}

/-- The regularized limit of `B̃_Q` at the root addresses. -/
theorem regCoef_root (hBt : BtRec Bt) {Q : RegCpl} (hwf : Q.wf = true) (Z : Finset Addr) :
    RegCoef zetaA Z (chosenSet Q.links) (Bt Q ((0 : Fin 2), []) ((1 : Fin 2), []))
      (cplJ Z Q ((0 : Fin 2), []) ((1 : Fin 2), [])) :=
  regCoef_cpl hBt Z Q _ _ hwf (chosen_nodup Q)

end WaveTurbulence.Cancel
