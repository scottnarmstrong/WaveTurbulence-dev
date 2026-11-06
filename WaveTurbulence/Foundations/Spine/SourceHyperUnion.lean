/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
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
namespace WaveTurbulence.LGSpine
open SourceVine Finset

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

theorem Chain.ofVine {S : Finset V} {a b : V} {n : ℕ} (h : Vine.Chain M S a b n) :
    Chain M S a b n := by
  induction h with
  | single h => exact .single h
  | append h hV hI hne ih => exact .append ih hV hI hne

theorem hyper_union_object {P Q : Object M} {cj : V} {n m : ℕ}
    (hPl : P.lower = cj) (hQu : Q.upper = cj)
    (hPch : Chain M P.atoms P.upper cj n) (hQch : Chain M Q.atoms cj Q.lower m)
    (hPQ : P.atoms ∩ Q.atoms = {cj}) (hPB : M.IsBlock P.atoms P.upper P.lower)
    (hQB : M.IsBlock Q.atoms Q.upper Q.lower)
    (hH : Mole.IsHyperBlock M (P.atoms ∪ Q.atoms) P.upper Q.lower) :
    ∃ U : Object M, U.atoms = P.atoms ∪ Q.atoms ∧ U.upper = P.upper ∧ U.lower = Q.lower ∧
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
  have hcP := Chain.ofVine (FP.chain_of hPch.toVine subset_rfl)
  have hcQ := Chain.ofVine (FQ.chain_of hQch.toVine subset_rfl)
  have hcU := chain_union_of_one_joint hcP hcQ hPQ
  let R : HyperLikeRealization M (P.atoms ∪ Q.atoms) P.upper Q.lower :=
    ⟨e, he, ⟨hB, _, hcU⟩⟩
  refine ⟨⟨P.atoms ∪ Q.atoms, P.upper, Q.lower, .hyper R⟩, rfl, rfl, rfl, ⟨R, rfl, he, hB⟩, ?_⟩
  intro d L γ η w κ k ⟨r, hr, hk⟩
  refine ⟨r, ?_, hk⟩
  have h1 : (Molecule.eraseBond M e).IsBlockGap L w (fun x => κ x.1) P.atoms P.upper r :=
    (FP.blockGap_iff P.atoms subset_rfl L w κ P.upper r).mpr hr
  exact blockGap_mono subset_union_left h1

end WaveTurbulence.LGSpine
