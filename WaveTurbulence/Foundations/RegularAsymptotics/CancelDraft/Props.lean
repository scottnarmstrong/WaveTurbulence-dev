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

/-- **DH21 Proposition 7.4** (`maincancel`). For a regular couple code that is not dominant, every
component `𝒥B̃_{Q,Z}` of every expansion (maincoef3) of `B̃_Q` vanishes. -/
theorem maincancel (hBt : BtRec Bt) {Q : RegCpl} (hwf : Q.wf = true) (hnd : Q.dominant = false)
    {θc ac bc A N : ℝ} (hθ : 0 ≤ θc) {Z : Finset Addr} (hZ : Z ⊆ chosenSet Q.links)
    {G : Finset Addr → TCoef}
    (hG : ∀ Z' ⊆ chosenSet Q.links, MCRep θc ac bc A N (↑(chosenSet Q.links \ Z')) (G Z'))
    (hF : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      Bt Q ((0 : Fin 2), []) ((1 : Fin 2), []) α t s =
        ∑ Z' ∈ (chosenSet Q.links).powerset, (∏ z ∈ Z', PhiZ zetaA z (α z)) * G Z' α t s)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (α₀ : Addr → ℝ) :
    mint (chosenSet Q.links \ Z) (fun α => G Z α t s) α₀ = 0 := by
  rw [mint_eq_of_MCExp hθ zetaA_pm hZ (regCoef_root hBt hwf Z) hG hF ht hs α₀]
  exact cplJ_eq_zero Z Q _ _ hnd t ht s hs

/-- **DH21 Proposition 7.5** (`regcplcal`), **corrected (F61)**. For a dominant regular couple code
and a special set `Z`, every expansion (maincoef3) of `B̃_Q` has
`𝒥B̃_{Q,Z} = (-1)^{|Z|} 𝒥ℬ_Q`, where `𝒥ℬ_Q = RegCpl.JB 0 Q` solves (recurtype1)/(recurtype2). -/
theorem regcplcal (hBt : BtRec Bt) {Q : RegCpl} (hwf : Q.wf = true) (hd : Q.dominant = true)
    {θc ac bc A N : ℝ} (hθ : 0 ≤ θc) {Z : Finset Addr} (hZ : IsSpecialSet Q.links Z)
    {G : Finset Addr → TCoef}
    (hG : ∀ Z' ⊆ chosenSet Q.links, MCRep θc ac bc A N (↑(chosenSet Q.links \ Z')) (G Z'))
    (hF : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      Bt Q ((0 : Fin 2), []) ((1 : Fin 2), []) α t s =
        ∑ Z' ∈ (chosenSet Q.links).powerset, (∏ z ∈ Z', PhiZ zetaA z (α z)) * G Z' α t s)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (α₀ : Addr → ℝ) :
    mint (chosenSet Q.links \ Z) (fun α => G Z α t s) α₀ = (-1) ^ Z.card * (Q.JB 0 t s : ℂ) := by
  have hZS := chosenSet_of_special hZ
  rw [mint_eq_of_MCExp hθ zetaA_pm hZS (regCoef_root hBt hwf Z) hG hF ht hs α₀]
  have hsp : ∀ z ∈ Z, z ∈ chosenSet (Q.linksAt ((0 : Fin 2), []) ((1 : Fin 2), [])) →
      z ∈ cplSpecial Q ((0 : Fin 2), []) ((1 : Fin 2), []) := fun z hz _ =>
    (isSpecialSet_iff Q Z).1 hZ z hz
  rw [cplJ_eq_JB Z Q _ _ hd (chosen_nodup Q) hsp t ht s hs]
  congr 2
  exact (Finset.inter_eq_left.2 hZS).symm ▸ rfl

/-- **`𝒥B̃_Q` is independent of the expansion**: the `Z = ∅` component of any expansion integrates to
`𝒥ℬ_Q` (dominant `Q`), and `𝒥B̃_{Q,Z} = (-1)^{|Z|} 𝒥B̃_{Q,∅}` for special `Z`. -/
theorem regcplcal_empty (hBt : BtRec Bt) {Q : RegCpl} (hwf : Q.wf = true) (hd : Q.dominant = true)
    {θc ac bc A N : ℝ} (hθ : 0 ≤ θc) {G : Finset Addr → TCoef}
    (hG : ∀ Z' ⊆ chosenSet Q.links, MCRep θc ac bc A N (↑(chosenSet Q.links \ Z')) (G Z'))
    (hF : ∀ α t s, t ∈ Icc (0 : ℝ) 1 → s ∈ Icc (0 : ℝ) 1 →
      Bt Q ((0 : Fin 2), []) ((1 : Fin 2), []) α t s =
        ∑ Z' ∈ (chosenSet Q.links).powerset, (∏ z ∈ Z', PhiZ zetaA z (α z)) * G Z' α t s)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) (α₀ : Addr → ℝ) :
    mint (chosenSet Q.links) (fun α => G ∅ α t s) α₀ = (Q.JB 0 t s : ℂ) := by
  have h := regcplcal hBt hwf hd hθ (Z := ∅) (fun z hz => absurd hz (Finset.notMem_empty z)) hG hF ht hs α₀
  simpa using h

end WaveTurbulence.Cancel
