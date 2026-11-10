/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex2
public import WaveTurbulence.Foundations.FinalCount.G3SrcGaps
public import WaveTurbulence.Foundations.FinalCount.G3NewComp2
public import WaveTurbulence.Foundations.FinalCount.G3Step5c
/-! **FINALCOUNT-G3: excessprop1 (2) for Step 1** (DH23/TARGET Prop `excessprop1` (2), L2154--L2177), glued to VINE-COUNT
`prop94_vine_newcomp` (`ΔF = 1`, `ΔV_β = 2`, no new `α`-atom).

Step 1 either keeps the number of components (the `α`-case, `UStep1.excess`) or creates exactly one (`vine_F_cases`).  In the second case the
removed object is a single vine: a `DoubleShape` would stay connected outside (`doubleShape_F_le`, hypothesis `hconn`, the output of `subsetvc`).
`NewCompFixed` (L2174) is PROVED from the flux identity through the bridge (`newCompFixed_exists`), with `ν = |A| + (m - 2) ≤ |M_cur atoms|`;
the caller supplies `ν ≥ |atoms|` (`ν = n_sb ≤ (log L)^{C₂}`, L2175, via `UCtx.card_atoms_le`).  Named inputs: `hcls`, `hconn`, `hnl` (no loops;
`Good.noloop`), `hν`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.VineCount WaveTurbulence.LGSpine.SourceVine

variable {d : ℕ}

theorem newCompFixed_mono {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {K : VineCut M}
    {L γ δ ν ν' : ℝ} {w : Mom d} {Adm : (D → (Fin d → ℤ)) → Prop} (hL : 0 < L) (hδ : 0 < δ) (h : ν ≤ ν')
    (hN : NewCompFixed M K L γ δ ν w Adm) : NewCompFixed M K L γ δ ν' w Adm := by
  intro c β k0 hP
  obtain ⟨n₀, hn₀, e₀, hh⟩ := hN c β k0 hP
  refine ⟨n₀, hn₀, e₀, fun κ hκ => ⟨(hh κ hκ).1, (hh κ hκ).2.trans ?_⟩⟩
  have : 0 ≤ δ⁻¹ * L ^ (-2 * γ) := by positivity
  nlinarith

theorem gapAt_ne_of_SG {D : Type*} {L γ η : ℝ} {w : Mom d} {κ : D → (Fin d → ℤ)} {x₁ x₂ : D}
    (h : Molecule.gapKind L γ η (Molecule.gapAt L w κ x₁ x₂) = .SG) : κ x₁ ≠ κ x₂ := by
  intro e
  have : Molecule.gapAt L w κ x₁ x₂ = 0 := by
    unfold Molecule.gapAt Molecule.kvec; rw [e]; simp
  rw [this] at h
  unfold Molecule.gapKind at h
  simp at h

/-- A new component excludes the hyper shape: the deleted bond joins the fresh joints. -/
theorem vc_block_of_new {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} (K : VineCut M)
    (hnc : ¬ K.post.SameComponent K.fa K.fb) : M.IsBlock K.C.atoms K.C.upper K.C.lower := by
  have ha := K.in_a
  have hb := K.in_b
  unfold Object.ContainsDart at ha hb
  rcases hsh : K.C.shape with h | R
  · exact h.1
  · exfalso
    rw [hsh] at ha hb
    obtain ⟨a1, a1', -⟩ := ha.1
    obtain ⟨a2, a2', -⟩ := ha.2
    obtain ⟨b1, b1', -⟩ := hb.1
    obtain ⟨b2, b2', -⟩ := hb.2
    have hG : ∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D), z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) :=
      fun _ h => h
    have hnot : ∀ z, z ≠ R.added → z ≠ M.mate R.added → z ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) → True :=
      fun _ _ _ _ => trivial
    have hz : ∀ z, (z = R.added ∨ z = M.mate R.added) →
        z ∉ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset D) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      rcases hz with rfl | rfl
      · exact ⟨fun e => a1 e.symm, fun e => a2 e.symm, fun e => b1 e.symm, fun e => b2 e.symm⟩
      · exact ⟨fun e => a1' e.symm, fun e => a2' e.symm, fun e => b1' e.symm, fun e => b2' e.symm⟩
    have hends := R.ends_eq
    unfold Molecule.ends at hends
    rw [Sym2.eq_iff] at hends
    have key : ∃ z, (z = R.added ∨ z = M.mate R.added) ∧ M.atom z = K.C.upper ∧ M.atom (M.mate z) = K.C.lower := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨R.added, Or.inl rfl, h1, h2⟩
      · exact ⟨M.mate R.added, Or.inr rfl, h2, by rw [M.mate_mate]; exact h1⟩
    obtain ⟨z, hzc, hz1, hz2⟩ := key
    have hzm : (M.mate z = R.added ∨ M.mate z = M.mate R.added) := by
      rcases hzc with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (M.mate_mate _)
    have e1 := cutMol_atom_outside K hG (hz z hzc)
    have e2 := cutMol_atom_outside K hG (hz (M.mate z) hzm)
    rw [hz1] at e1; rw [hz2] at e2
    have h1 : hPost K K.C.upper = K.fa := by simp [hPost]
    have h2 : hPost K K.C.lower = K.fb := by simp [hPost, K.ab_ne.symm]
    rw [h1] at e1; rw [h2] at e2
    have hn1 : K.cutMol.atom z ∉ K.C.atoms := by
      rw [e1]; exact fun h => K.fa_fresh (objectAtoms_sub K.C h)
    exact hnc (Relation.EqvGen.rel _ _ (show K.post.Adj K.fa K.fb from ⟨⟨z, hn1⟩, e1, e2⟩))


end WaveTurbulence.FinalCountG3
