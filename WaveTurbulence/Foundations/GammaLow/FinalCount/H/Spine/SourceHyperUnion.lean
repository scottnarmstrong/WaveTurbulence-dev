/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceHyperUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineBranchingEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainBlock
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainConnected
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainCounts
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainEnds
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineChainIngredients
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineEraseChainIngredient
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperAdjointVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineHyperGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLikeGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Molecule.VineSmallVC
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceCountingObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceSubproObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineData
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineGapObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Spine.SourceVineObjects
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.Spine.SourceHyperUnion`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 The one-joint union of two ordinary chain objects can be a hyper-block (the classification's
second alternative): it is then a designated hyper object whose adjoint is the union chain in the
erased molecule, and it inherits the SG gap of the first object. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem Src.Chain.ofVine {S : Finset V} {a b : V} {n : ℕ} (h : Src.Chain Src.γL M S a b n) :
    Src.Chain Src.γL M S a b n := by
  induction h with
  | single h => exact .single h
  | append h hV hI hne ih => exact .append ih hV hI hne

alias _root_.WaveTurbulence.GammaLow.FinalCount.Src.Chain.ofVine := _root_.WaveTurbulence.GammaLow.FinalCount.H.Src.Chain.ofVine
theorem hyper_union_object {P Q : Src.Object Src.γL M} {cj : V} {n m : ℕ}
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Src.Chain Src.γL M P.atoms P.upper cj n) (hQch : Src.Chain Src.γL M Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hPB : M.IsBlock P.atoms P.upper P.lower)
    (hQB : M.IsBlock Q.atoms Q.upper Q.lower)
    (hH : Mole.IsHyperBlock M (P.atoms ∪ Q.atoms) P.upper Q.lower) :
    ∃ U : Src.Object Src.γL M, U.atoms = P.atoms ∪ Q.atoms ∧ U.upper = P.upper ∧ U.lower = Q.lower ∧
      (∃ R, U.shape = .hyper R ∧ M.ends R.added = s(P.upper, Q.lower) ∧
        (Mole.eraseBond M R.added).IsBlock (P.atoms ∪ Q.atoms) P.upper Q.lower) ∧
      ∀ {d : ℕ} (L γ η : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) (k : Molecule.GapKind),
        (∃ r, M.IsBlockGap L w κ P.atoms P.upper r ∧ Molecule.gapKind L γ η r = k) →
        U.HasGapKind L γ η w κ k := by
  obtain ⟨e, he, hB⟩ := hH
  have hbP : Q.lower ∉ P.atoms := by
    intro h
    have : Q.lower ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨h, hQB.2.2.1⟩
    rw [hPQ] at this
    exact hQB.2.2.2.1 (hQu.trans (mem_singleton.mp this).symm)
  have haQ : P.upper ∉ Q.atoms := by
    intro h
    have : P.upper ∈ P.atoms ∩ Q.atoms := mem_inter.mpr ⟨hPB.2.1, h⟩
    rw [hPQ] at this
    exact hPB.2.2.2.1 ((mem_singleton.mp this).trans hPl.symm)
  have hends : (M.atom e = P.upper ∧ M.atom (M.mate e) = Q.lower) ∨
      (M.atom e = Q.lower ∧ M.atom (M.mate e) = P.upper) := by
    have := Sym2.eq_iff.mp he
    exact this
  have hextP : ¬ M.InGroup P.atoms e := by
    rintro ⟨h1, h2⟩
    rcases hends with ⟨_, h⟩ | ⟨h, _⟩
    · exact hbP (h ▸ h2)
    · exact hbP (h ▸ h1)
  have hextQ : ¬ M.InGroup Q.atoms e := by
    rintro ⟨h1, h2⟩
    rcases hends with ⟨h, _⟩ | ⟨_, h⟩
    · exact haQ (h ▸ h1)
    · exact haQ (h ▸ h2)
  let FP := Vine.eraseBond_local_embedding M e P.atoms hextP
  let FQ := Vine.eraseBond_local_embedding M e Q.atoms hextQ
  have hcP := Src.Chain.ofVine (FP.chain_ofL hPch.toVine subset_rfl)
  have hcQ := Src.Chain.ofVine (FQ.chain_ofL hQch.toVine subset_rfl)
  have hcU := chain_union_of_one_joint hcP hcQ hPQ
  let R : Src.HyperLikeRealization Src.γL M (P.atoms ∪ Q.atoms) P.upper Q.lower :=
    ⟨e, he, ⟨hB, _, hcU⟩⟩
  refine ⟨⟨P.atoms ∪ Q.atoms, P.upper, Q.lower, .hyper R⟩, rfl, rfl, rfl, ⟨R, rfl, he, hB⟩, ?_⟩
  intro d L γ η w κ k ⟨r, hr, hk⟩
  refine ⟨r, ?_, hk⟩
  have h1 : (Molecule.eraseBond M e).IsBlockGap L w (fun x => κ x.1) P.atoms P.upper r :=
    (FP.blockGap_iff P.atoms subset_rfl L w κ P.upper r).mpr hr
  exact blockGap_mono subset_union_left h1

end WaveTurbulence.GammaLow.FinalCount.H
