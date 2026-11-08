/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.StemW2
public import WaveTurbulence.Foundations.Flower.MkSlotsS.EngBase
public import WaveTurbulence.Foundations.Flower.MkSlotsS.SelWeight

/-! # B3s-HELPER7 WP7 (part 1): the atom weight `zatomG` of `G_sb` and the general piece's atom weight

At a prescribed point `a` and a marked set `Mk` (the spliced garden `G_sb = (stSt a.prime.skeleton a.totalSigma Mk).G`;
at B4's class marking `Mk = classMk mkF a` it is the general piece's `(stA mkF a).G`, at B3's unit marking
`Mk = mk a.prime` it is the target of the members' shapes `memShape a mk y hy`):

* `coreRec a Mk c`: the core branch, in the reconstruction `recLG a` (source layering), of the `G_sb` atom `c`;
* **`zatomK`**, **`zatomG`**: the atom weight of `G_sb`, the product over the non-hinge atoms `c` of the general stem
  node weight `genNW (recLG a) …` at the core of `c`, read at the `G_sb` resonance factor `Ω_c` of a momentum
  assignment (`zatomG`: of the coset decoration, base `0`, of a decoration `z` of `G_sb`);
* `chiD_abs_div`: `chiD (|x| / r) = chiD (x / r)` (`chiD` is even);
* `genNW_coreRec_sel` (a residual selected atom: `radProd (radSigma) · chiDNorm · chiDNS(Ω/Rs)`),
  `genNW_coreRec_not_sel` (any other non-hinge atom: the engine's filter weight `filtW (filtGen c)`),
  `filtW_filtGen_hinge` (no filter at a hinge);
* **`zatomG_mul_sibInd`**: `zatomG z · sibIndOf … (coset z) = chiDNorm ^ #selRGen · pieceAtomW (pieceGen …) (coset z)`
  (hypotheses: the fine marking's `markI ⊆ mkF`, `1 ≤ L`, `L ≤ Rs j`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1MKGate
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice (stSt)
open WaveTurbulence.Flower.MkSlots (stA coreOf sibIndOf recLG)

namespace WaveTurbulence.Flower.MkSlotsI

variable {w : ℕ}

/-! ## The atom weight of `G_sb` -/

/-- The core branch, in the reconstruction `recLG a` of `a`, of a branch `c` of the spliced garden at the marked set
`Mk`. -/
abbrev coreRec (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (c : GBranch (stSt a.prime.skeleton a.totalSigma Mk).G.tree) : GBranch (recLG a).garden.tree :=
  a.prime.data.coreBranch a.prime.prime.1 ((stSt a.prime.skeleton a.totalSigma Mk).M.ob c)

/-- **The atom weight of `G_sb`** at a momentum assignment `k`: over the non-hinge atoms `c`, the general stem node
weight at the core of `c` in the reconstruction of `a`, read at the `G_sb` resonance factor `Ω_c(k)`. -/
def zatomK {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton))
    (k : GNode (stSt a.prime.skeleton a.totalSigma Mk).G.tree → Mom d) : ℂ :=
  ∏ c ∈ univ.filter (fun c => c ∉ (stSt a.prime.skeleton a.totalSigma Mk).hinges),
    genNW (recLG a) J L σ kSel Rs (coreRec a Mk c).toNode (omegaNode (stSt a.prime.skeleton a.totalSigma Mk).G k c)

/-- **The atom weight of `G_sb` on a decoration** `z` (coset decoration, base `0`). -/
def zatomG {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma Mk).G d roots 0) : ℂ :=
  zatomK J L σ kSel Rs a Mk (cosetDecoration (stSt a.prime.skeleton a.totalSigma Mk).G L 0 z.1)

theorem zatomG_eq {d : ℕ} (J : Finset (Fin w)) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (a : PrescribedPrimeGarden w) (Mk : Set (Stage1.CLVine a.prime.skeleton)) {roots : Fin w → (Fin d → ℤ)}
    (z : GenDecoration (stSt a.prime.skeleton a.totalSigma Mk).G d roots 0) :
    zatomG J L σ kSel Rs a Mk z =
      ∏ c ∈ univ.filter (fun c => c ∉ (stSt a.prime.skeleton a.totalSigma Mk).hinges),
        genNW (recLG a) J L σ kSel Rs (coreRec a Mk c).toNode
          (omegaNode (stSt a.prime.skeleton a.totalSigma Mk).G
            (cosetDecoration (stSt a.prime.skeleton a.totalSigma Mk).G L 0 z.1) c) := rfl

/-! ## `chiD` is even -/

theorem chiD_neg (u : ℝ) : chiD (-u) = chiD u := by
  have h : (fun y => chi0 (-y)) = chi0 := funext fun y => by simp only [chi0, abs_neg]
  have h2 := deriv_comp_neg (f := chi0) (x := u)
  rw [h] at h2
  unfold chiD
  rw [h2]
  ring

theorem chiD_abs_div (x r : ℝ) : chiD (|x| / r) = chiD (x / r) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg hx, neg_div, chiD_neg]

/-- At a residual selected vertex: `chiD (|x| / r) = chiDNorm · chiDNS (x / r)`. -/
theorem chiD_abs_div_eq (x r : ℝ) :
    ((chiD (|x| / r) : ℝ) : ℂ) = (chiDNorm : ℂ) * MkSlotsS.chiDNS (x / r) := by
  rw [chiD_abs_div, MkSlotsS.chiD_eq_chiDNorm_mul, MkSlotsS.chiDNS_apply]
  push_cast
  ring

/-! ## Transport of the selected set along `recLG a = a.layered` -/

theorem mem_selSetCap_congr {LG LG' : LayeredGarden w} (h : LG = LG') (J : Finset (Fin w))
    (kSel : Fin w → Option ℕ) {b : GBranch LG.garden.tree} {b' : GBranch LG'.garden.tree} (hb : b.1 = b'.1) :
    b ∈ selSetCap LG J kSel ↔ b' ∈ selSetCap LG' J kSel := by
  subst h
  rw [show b = b' from Subtype.ext hb]

section Rep

variable (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (mkF : Stage1Mk.MarkFn w) (a : PrescribedPrimeGarden w)

theorem coreRec_fst (c : GBranch (stA mkF a).G.tree) : (coreRec a (classMk mkF a) c).1.1 = c.1.1 :=
  MkSlots.coreOf_fst mkF a c

/-- The selected test at the core in the reconstruction is the residual selected set of the piece. -/
theorem coreRec_mem_selSetCap_iff (c : GBranch (stA mkF a).G.tree) :
    coreRec a (classMk mkF a) c ∈ selSetCap (recLG a) J kSel ↔ c ∈ MkSlotsG.selRGen J kSel mkF a := by
  rw [MkSlotsS.mem_selROf]
  exact mem_selSetCap_congr (VineAlign.sourceLayer_reconstructs a) J kSel rfl

end Rep

/-! ## The stem node weight at the cores of the representative -/

section Node

variable {R : ℕ} (J : Finset (Fin (2 * R))) (L : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
  (mkF : Stage1Mk.MarkFn (2 * R)) (a : PrescribedPrimeGarden (2 * R))

/-- **At a residual selected atom**: σ's filters and the selected filter `chiDNorm · chiDNS (Ω/Rs)` (no shell). -/
theorem genNW_coreRec_sel {c : GBranch (stA mkF a).G.tree} (hc : c ∈ MkSlotsG.selRGen J kSel mkF a) (x : ℝ) :
    genNW (recLG a) J L σ kSel Rs (coreRec a (classMk mkF a) c).toNode x =
      (MkSlotsT.radProd (MkSlotsT.radSigma L σ c) x : ℂ) *
        ((chiDNorm : ℂ) * MkSlotsS.chiDNS (x / Rs c.1.1)) := by
  set b := coreRec a (classMk mkF a) c
  have hb : b ∈ selSetCap (recLG a) J kSel := (coreRec_mem_selSetCap_iff J kSel mkF a c).2 hc
  have hcap : selCap (recLG a) J kSel b.1.1 = some b := MkSlotsS.selCap_of_mem_selSetCap hb
  have hst : b ∈ stemSetCap (recLG a) J b.1.1 := (MkSlotsS.selCap_spec hcap).2
  have hfst : b.1.1 = c.1.1 := coreRec_fst mkF a c
  have hshell : MkSlotsG.shellRad (recLG a) J kSel Rs b = [] := by
    unfold MkSlotsG.shellRad
    rw [ite_eq_right]
    rintro ⟨v, hv, hne⟩
    rw [hcap] at hv
    exact hne (Option.some.inj hv).symm
  have hrad : MkSlotsG.radRaw (recLG a) J L σ kSel Rs b = MkSlotsT.radSigma L σ c := by
    unfold MkSlotsG.radRaw
    rw [hshell, List.append_nil]
    unfold MkSlotsT.radSigma
    rw [hfst]
  rw [genNW_toNode, ite_eq_left ⟨_, hst⟩, ite_eq_left hb, hrad, chiD_abs_div_eq, hfst]

/-- **At a non-hinge atom that is not a residual selected atom**: the engine's filter weight of `filtGen`. -/
theorem genNW_coreRec_not_sel (hL : 1 ≤ L) (hRs : ∀ j, L ≤ Rs j) {c : GBranch (stA mkF a).G.tree}
    (hh : c ∉ (stA mkF a).hinges) (hc : c ∉ MkSlotsG.selRGen J kSel mkF a) (x : ℝ) :
    genNW (recLG a) J L σ kSel Rs (coreRec a (classMk mkF a) c).toNode x =
      MkSlotsT.filtW (MkSlotsG.filtGen J L σ kSel Rs mkF a c) x := by
  set b := coreRec a (classMk mkF a) c
  have hb : b ∉ selSetCap (recLG a) J kSel := fun h => hc ((coreRec_mem_selSetCap_iff J kSel mkF a c).1 h)
  have hh' : c ∉ (MkSlotsT.shapeRep mkF a).hinges (MkSlotsT.unitsRep_disj mkF a) := by
    rw [MkSlotsT.shapeRep_hinges]; exact hh
  rw [MkSlotsG.filtGen_not_sel hc, genNW_toNode]
  unfold MkSlotsT.filtStem
  by_cases hst : MkSlotsT.StemB a.prime.data a.prime.prime.1 (VineAlign.sourceLayer a)
      (VineAlign.sourceLayer_isLayering a) J
      (MkSlotsT.coreLG a.prime.data a.prime.prime.1 (VineAlign.sourceLayer a) (VineAlign.sourceLayer_isLayering a)
        ((MkSlotsT.shapeRep mkF a).br c))
  · have hst' : ∃ j, b ∈ stemSetCap (recLG a) J j := hst
    rw [ite_eq_left hst', ite_eq_right hb, mul_one, ite_eq_left ⟨hh', hst⟩, MkSlotsT.filtW_filtOfRad,
      MkSlotsG.radGen_eq_raw hL (fun j => hL.trans (hRs j))]
    rfl
  · have hst' : ¬ ∃ j, b ∈ stemSetCap (recLG a) J j := hst
    rw [ite_eq_right hst', ite_eq_right (fun h => hst h.2)]
    rfl

/-- **No filter at a hinge** (a hinge is never a residual selected atom). -/
theorem filtW_filtGen_hinge (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    {c : GBranch (stA mkF a).G.tree} (hh : c ∈ (stA mkF a).hinges) (x : ℝ) :
    MkSlotsT.filtW (MkSlotsG.filtGen J L σ kSel Rs mkF a c) x = 1 := by
  have hc : c ∉ MkSlotsG.selRGen J kSel mkF a := fun h => MkSlotsS.selROf_not_hinge pat t s hsub h hh
  have hh' : c ∈ (MkSlotsT.shapeRep mkF a).hinges (MkSlotsT.unitsRep_disj mkF a) := by
    rw [MkSlotsT.shapeRep_hinges]; exact hh
  rw [MkSlotsG.filtGen_not_sel hc, MkSlotsT.filtStem_hinge _ _ _ _ _ _ _ _ _ c hh']
  rfl

end Node

/-! ## The atom weight of the general piece -/

/-- **The atom weight of `G_sb` is the general piece's atom weight** (up to `chiDNorm ^ #selR`): on a decoration `z`
of `G_sb = (stA mkF a).G`, `zatomG z` times the dagger sibling indicator of the piece at the coset decoration is
`chiDNorm ^ #(selRGen …)` times the piece's atom weight `pieceAtomW (pieceGen …)` (filters `filtGen`: `(Rs, chiDNS)` at
a residual selected atom — `chiD = chiDNorm · chiDN` —, γ's `filtStem` with `radGen = radRaw` elsewhere, nothing at a
hinge; σ's filter at the residual selected atoms inside the indicator `indGen`). -/
theorem zatomG_mul_sibInd (P : WTParams) {R : ℕ} (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
    (kSel σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (mkF : Stage1Mk.MarkFn (2 * R))
    (a : PrescribedPrimeGarden (2 * R)) (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))
    (hsub : ∀ {LG : LayeredGarden (2 * R)} (B : PrimeData LG), markI J pat t s kSel B ⊆ mkF B)
    (hL : 1 ≤ P.L) (hRs : ∀ j, P.L ≤ Rs j) {roots : Fin (2 * R) → (Fin P.d → ℤ)}
    (z : GenDecoration (stA mkF a).G P.d roots 0) :
    zatomG J P.L σ kSel Rs a (classMk mkF a) z *
        ((sibIndOf J mkF a dag (MkSlotsG.flwGen J mkF a) (cosetDecoration (stA mkF a).G P.L 0 z.1) : ℝ) : ℂ) =
      (chiDNorm : ℂ) ^ (MkSlotsG.selRGen J kSel mkF a).card *
        MkSlotsS.pieceAtomW (MkSlotsG.pieceGen P J pat t s kSel σ Rs mkF a dag)
          (cosetDecoration (stA mkF a).G P.L 0 z.1) := by
  set k := cosetDecoration (stA mkF a).G P.L 0 z.1
  set selR := MkSlotsG.selRGen J kSel mkF a
  set H := (stA mkF a).hinges
  set F : GBranch (stA mkF a).G.tree → ℂ := fun c =>
    MkSlotsT.filtW (MkSlotsG.filtGen J P.L σ kSel Rs mkF a c) (omegaNode (stA mkF a).G k c)
  set Rr : GBranch (stA mkF a).G.tree → ℂ := fun c =>
    (MkSlotsT.radProd (MkSlotsT.radSigma P.L σ c) (omegaNode (stA mkF a).G k c) : ℂ)
  have hselH : ∀ c ∈ selR, c ∉ H := fun c hc => MkSlotsS.selROf_not_hinge pat t s hsub hc
  -- the atom weight, atom by atom
  have hg : ∀ c ∈ univ.filter (fun c => c ∉ H),
      genNW (recLG a) J P.L σ kSel Rs (coreRec a (classMk mkF a) c).toNode (omegaNode (stA mkF a).G k c) =
        F c * (if c ∈ selR then (chiDNorm : ℂ) * Rr c else 1) := by
    intro c hc
    have hcH : c ∉ H := (mem_filter.1 hc).2
    by_cases hs : c ∈ selR
    · rw [genNW_coreRec_sel J P.L σ kSel Rs mkF a hs, ite_eq_left hs]
      have hF : F c = MkSlotsS.chiDNS (omegaNode (stA mkF a).G k c / Rs c.1.1) := by
        show MkSlotsT.filtW (MkSlotsG.filtGen J P.L σ kSel Rs mkF a c) _ = _
        rw [MkSlotsG.filtGen_sel hs]
        rfl
      rw [hF]
      ring
    · rw [genNW_coreRec_not_sel J P.L σ kSel Rs mkF a hL hRs hcH hs, ite_eq_right hs, mul_one]
  have hz : zatomG J P.L σ kSel Rs a (classMk mkF a) z =
      (∏ c, F c) * ((chiDNorm : ℂ) ^ selR.card * ∏ c ∈ selR, Rr c) := by
    rw [zatomG_eq, Finset.prod_congr rfl hg, Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_filter_of_ne fun c _ hne => ?_
      intro hcH
      exact hne (filtW_filtGen_hinge J P.L σ kSel Rs mkF a pat t s hsub hcH _)
    · rw [Finset.prod_ite_mem, Finset.inter_eq_right.2 fun c hc => mem_filter.2 ⟨mem_univ _, hselH c hc⟩,
        Finset.prod_mul_distrib, Finset.prod_const]
  have hp : MkSlotsS.pieceAtomW (MkSlotsG.pieceGen P J pat t s kSel σ Rs mkF a dag) k =
      (∏ c, F c) * (((sibIndOf J mkF a dag (MkSlotsG.flwGen J mkF a) k : ℝ) : ℂ) * ∏ c ∈ selR, Rr c) := by
    unfold MkSlotsS.pieceAtomW
    rw [MkSlotsG.pieceGen_ind]
    unfold MkSlotsG.indGen
    push_cast
    rfl
  rw [hz, hp]
  ring

end WaveTurbulence.Flower.MkSlotsI
