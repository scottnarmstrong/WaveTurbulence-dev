/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Core.PhiQ

/-!
# N2 Lemma 1.14(c′): assembly from the ingredient step

* `IsSubObjU.rungCore_core`: rung data inside `U°` (all-in case; poles cut down to `S_U`);
* `phi_core_eq`: `Φ(U)°` in `G/[μ]R` is `U°/[μ]R` (all-in case);
* `phiType_of_ing`: the conclusion of `PhiTypeStatement` from any ingredient step (`IngConcl` for every member of
  `𝒱_enl` and rung data with no joint in the rung).
-/

@[expose] public section

namespace WaveTurbulence.TVine.Core

open TVine

universe u

variable {V : Type*} [DecidableEq V]

section

variable {G : UMultigraph V} {a b xm xp ym yp : V} {Km Kp : Finset V} {U : SubObj V}

/-- Rung data inside `U°` (rung and rails in `S_U`, no joint of `U` in the rung). -/
theorem IsSubObjU.rungCore_core (hR : RungCore G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U)
    (haS : a ∈ U.atoms) (hbS : b ∈ U.atoms) (hxm : xm ∈ U.atoms) (hxp : xp ∈ U.atoms) (hym : ym ∈ U.atoms)
    (hyp : yp ∈ U.atoms) (h1a : U.k₁ ≠ a) (h1b : U.k₁ ≠ b) (h2a : U.k₂ ≠ a) (h2b : U.k₂ ≠ b) :
    RungCore (U.core G) a b xm xp ym yp (Km ∩ U.atoms) (Kp ∩ U.atoms) := by
  have hRS := hR.restrict hU.atoms_subset haS hbS hxm hxp hym hyp
  unfold SubObj.core
  split
  · exact hRS.eraseBond h1a h1b h2a h2b
  · exact hRS

/-- `Φ(U)° = U°/[μ]R` (all-in case). -/
theorem phi_core_eq (hR : RungCore G a b xm xp ym yp Km Kp) (hU : IsSubObjU G U)
    (haS : a ∈ U.atoms) (hbS : b ∈ U.atoms) (hxm : xm ∈ U.atoms) (hxp : xp ∈ U.atoms) (hym : ym ∈ U.atoms)
    (hyp : yp ∈ U.atoms) (h1a : U.k₁ ≠ a) (h1b : U.k₁ ≠ b) (h2a : U.k₂ ≠ a) (h2b : U.k₂ ≠ b) (μ : Bool) :
    (U.phi a b).core (rungDel G a b xm xp ym yp μ) = rungDel (U.core G) a b xm xp ym yp μ := by
  have hedge : (U.phi a b).edges (rungDel G a b xm xp ym yp μ) = rungDel (U.edges G) a b xm xp ym yp μ :=
    induce_rungDel hR haS hbS hxm hxp hym hyp μ
  cases hh : U.hyper
  · have hc0 : U.core G = U.edges G := by simp [SubObj.core, hh]
    rw [hc0, ← hedge]; simp [SubObj.core, SubObj.phi, hh]
  · have hmE : (U.edges G).mult s(U.k₁, U.k₂) ≠ 0 := by
      rw [SubObj.edges, induce_mult_of_mem G hU.k₁_mem hU.k₂_mem]; exact hU.2.1 hh
    have hc0 : U.core G = eraseBond (U.edges G) s(U.k₁, U.k₂) := by simp [SubObj.core, hh]
    rw [hc0, ← eraseBond_rungDel _ h1a h1b h2a h2b hmE, ← hedge]; simp [SubObj.core, SubObj.phi, hh]

end

/-- **N2 Lemma 1.14(c′) from the ingredient step.** -/
theorem phiType_of_ing
    (hing : ∀ (k : EnlKind) (X : UMultigraph V) (p q a b xm xp ym yp : V) (Km Kp : Finset V) (μ : Bool),
      IsVineKindU k X p q → RungCore X a b xm xp ym yp Km Kp → a ≠ p → a ≠ q → b ≠ p → b ≠ q →
      IngConcl k X p q a b xm xp ym yp μ)
    (G : UMultigraph V) (j₁ j₂ a b xm xp ym yp : V) (Km Kp : Finset V) (U : SubObj V) (ks : List EnlKind)
    (μ : Bool) (hB : IsBlockU G j₁ j₂) (hl : G.Loopless) (hD : IsDeletableAt G j₁ j₂ a b xm xp ym yp Km Kp)
    (hVL : IsVineLikeU G U ks) (h1a : U.k₁ ≠ a) (h1b : U.k₁ ≠ b) (h2a : U.k₂ ≠ a) (h2b : U.k₂ ≠ b)
    (haS : a ∈ U.atoms) :
    IsVineLikeU (rungDel G a b xm xp ym yp μ) (U.phi a b) ks ∨
      ∃ i : Fin ks.length, ks.get i = .II ∧
        IsVineLikeU (rungDel G a b xm xp ym yp μ) (U.phi a b) (ks.set i .I) ∧
        GapCutAt (rungDel G a b xm xp ym yp μ) (U.phi a b) U.k₁ := by
  have hRO := hD.1
  have hRc := hRO.1.toCore
  obtain ⟨hU, hch⟩ := hVL
  obtain ⟨-, hbI, hxm, hxp, hym, hyp⟩ :=
    (phiAllInOut_holds G j₁ j₂ a b xm xp ym yp Km Kp U hB hl hRO hU h1a h1b h2a h2b).resolve_right
      (fun h => h.1 haS)
  have hbS : b ∈ U.atoms := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hbI)
  have hRH := hU.rungCore_core hRc haS hbS hxm hxp hym hyp h1a h1b h2a h2b
  have hHl : (U.core G).Loopless := fun v => Nat.le_zero.mp (hl v ▸ core_mult_le G U _)
  have hsub := phiSubObj_holds G j₁ j₂ a b xm xp ym yp Km Kp U μ hB hl hRO hU h1a h1b h2a h2b
  have hcore := phi_core_eq hRc hU haS hbS hxm hxp hym hyp h1a h1b h2a h2b μ
  have hing' : ∀ (k : EnlKind) (T : Finset V) (p q : V), IsVineKindU k (induce (U.core G) T) p q → a ∈ T →
      b ∈ T → xm ∈ T → xp ∈ T → ym ∈ T → yp ∈ T → a ≠ p → a ≠ q → b ≠ p → b ≠ q →
      IngConcl k (induce (U.core G) T) p q a b xm xp ym yp μ :=
    fun k T p q hv haT hbT hxmT hxpT hymT hypT hap haq hbp hbq =>
      hing k _ p q a b xm xp ym yp _ _ μ hv
        (hRH.restrict hv.isBlockU.verts_subset_of_induce haT hbT hxmT hxpT hymT hypT) hap haq hbp hbq
  rcases chain_rungDel hHl hRH μ hing' hch hU.2.2 haS h1a.symm h2a.symm h1b.symm h2b.symm with
    hc | ⟨i, hi, hc, P, p, hPS, hkP, hpP, haP, hbP, h2P, hcl, hpole⟩
  · left
    refine ⟨hsub, ?_⟩
    rw [hcore]; exact hc
  · right
    refine ⟨i, hi, ⟨hsub, by rw [hcore]; exact hc⟩, ?_⟩
    have hgap : GapCutAt G U U.k₁ := by
      rcases hpole with ⟨hPK, hx, hy⟩ | ⟨hPK, hx, hy⟩
      · exact gapCut_of_qPrefix hB hl hRc hU haS hbS h2a h2b hPS hkP hpP haP hbP h2P hcl
          (hPK.trans Finset.inter_subset_left) hx hy
      · exact gapCut_of_qPrefix hB hl hRc.swapPoles hU haS hbS h2a h2b hPS hkP hpP haP hbP h2P hcl
          (hPK.trans Finset.inter_subset_left) hx hy
    by_contra hng
    exact phiGap_holds G j₁ j₂ a b xm xp ym yp Km Kp U μ hB hl hRO hU h1a h1b h2a h2b hng hgap

end WaveTurbulence.TVine.Core
