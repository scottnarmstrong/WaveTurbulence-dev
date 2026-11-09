/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Facts
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.LocalEmbed
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceChainSwap
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Counting
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceMaximalObjects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectFinite
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceObjectUnion
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.SourceOneJointUnion
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Src.Objects
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Base
public import WaveTurbulence.Foundations.Spine.SourceOneJointUnion
public import WaveTurbulence.Foundations.Spine.SourceVineObjectBridge
public import WaveTurbulence.Foundations.Molecule.VineLocalDartChains
public import WaveTurbulence.Foundations.Molecule.VineLocalDartGaps
public import WaveTurbulence.Foundations.Molecule.VineLocalDartErasure
/-! The one-joint union of two ordinary chain objects can be a hyper-block (the classification's
second alternative): it is then a designated hyper object whose adjoint is the union chain in the
erased molecule, and it inherits the SG gap of the first object. -/
public section
set_option autoImplicit false
-- Ported from main `Spine.SourceHyperUnion` (sha256 65263be59cf02e30852a5fd9a04a725f95ddf27cdbaa42b8ae3081101a645cb7) to L6's `𝒱_γ` carrier `FinalCount.Src` (family parameter `γv`).
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.LGSpine WaveTurbulence.GammaLow.FinalCount.Src
open WaveTurbulence.LGSpine.SourceVine (TripleAt HasChosenPair atomGapKind IsDyadicScale InternalParent disjointF_of_subset disjointF_union)
set_option linter.unusedSectionVars false
variable {γv : ℝ}
open Finset

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem hyper_union_object {P Q : Object γv M} {cj : V} {n m : ℕ}
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Chain γv M P.atoms P.upper cj n) (hQch : Chain γv M Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hPB : M.IsBlock P.atoms P.upper P.lower)
    (hQB : M.IsBlock Q.atoms Q.upper Q.lower)
    (hH : Mole.IsHyperBlock M (P.atoms ∪ Q.atoms) P.upper Q.lower) :
    ∃ U : Object γv M, U.atoms = P.atoms ∪ Q.atoms ∧ U.upper = P.upper ∧ U.lower = Q.lower ∧
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
  have hcP := embed_chain_of FP hPch subset_rfl
  have hcQ := embed_chain_of FQ hQch subset_rfl
  have hcU := chain_union_of_one_joint hcP hcQ hPQ
  let R : HyperLikeRealization γv M (P.atoms ∪ Q.atoms) P.upper Q.lower :=
    ⟨e, he, ⟨hB, _, hcU⟩⟩
  refine ⟨⟨P.atoms ∪ Q.atoms, P.upper, Q.lower, .hyper R⟩, rfl, rfl, rfl, ⟨R, rfl, he, hB⟩, ?_⟩
  intro d L γ η w κ k ⟨r, hr, hk⟩
  refine ⟨r, ?_, hk⟩
  have h1 : (Molecule.eraseBond M e).IsBlockGap L w (fun x => κ x.1) P.atoms P.upper r :=
    (FP.blockGap_iff P.atoms subset_rfl L w κ P.upper r).mpr hr
  exact blockGap_mono subset_union_left h1

end WaveTurbulence.GammaLow.Famc
