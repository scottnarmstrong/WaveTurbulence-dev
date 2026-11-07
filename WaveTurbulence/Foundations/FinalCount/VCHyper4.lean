/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VCHyper3
/-! # VINE-COUNT part 29: `vine_count_main` for a hyper object (the adjoint is a single vine). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc Icc)
open scoped ENNReal
namespace WaveTurbulence.VineCount
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine WaveTurbulence.FinalCount WaveTurbulence.CountLemmas

variable {d : ℕ}

/-- **The label count `𝔉` for a hyper object** (DH23 L1796--L1801) whose adjoint VC is a single vine, from `VINEPARAM`
(applied to the adjoint `eraseBond M R.added`): the labels of the deleted bond are not counted, the joints are not
used, so the bound is that of the single vine. -/
theorem hyper_count_main (hvp : VINEPARAM) (hd : 3 ≤ d) {γ : ℝ} (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ Cf C₂ : ℝ, 0 ≤ Cf ∧ 1 ≤ C₂ ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, Real.exp 1 ≤ L₀ ∧ ∀ L ≥ L₀,
      ∀ {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D) (K : VineCut M)
        (R : HyperLikeRealization M K.C.atoms K.C.upper K.C.lower) (_h : K.C.shape = .hyper R),
        M.IsMolecule → (∀ x ∈ M.atoms, M.deg x ≤ 4) →
        (∃ X, (Molecule.eraseBond M R.added).IsVine X K.C.atoms K.C.upper K.C.lower) →
        ∀ (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ), (∀ S, 0 ≤ P S) →
        DecScale M L w Adm (VCLadderScale K L w P) → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 2 → 1 ≤ ρ * L →
        (∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d), ParamOK M c k0 →
          ∃ r₀ : Mom d, ∀ κ ∈ decSet M L γ δ w Adm c β k0, ‖Molecule.gapAt L w κ K.x₁ K.x₂ - r₀‖ ≤ ρ) →
        VineCountInput' K L γ δ ρ Cf C₂ w Adm P 4 := by
  obtain ⟨Cf, C₂, hCf, hC₂, hset⟩ := vine_count_set hvp hd hγ
  refine ⟨Cf, C₂, hCf, hC₂, fun δ hδ => ?_⟩
  obtain ⟨L₀, hL₀, hL⟩ := hset δ hδ
  refine ⟨L₀, hL₀, fun L hLL V D _ _ _ M K R h hMol hM hvine w Adm P hP0 hscale ρ hρ0 hρ2 hρL hball => ?_⟩
  intro c β k0 hparam
  obtain ⟨r₀, hr₀⟩ := hball c β k0 hparam
  let g : (D → (Fin d → ℤ)) → ({x : D // x ≠ R.added ∧ x ≠ M.mate R.added} → (Fin d → ℤ)) := fun f y => f y.1
  have hMol' : (Molecule.eraseBond M R.added).IsMolecule :=
    Vine.eraseBond_isMolecule M hMol _ (added_nonloop K R h)
  have hM' : ∀ x ∈ (Molecule.eraseBond M R.added).atoms, (Molecule.eraseBond M R.added).deg x ≤ 4 :=
    fun x hx => (Vine.eraseBond_degree_le M R.added x).2.2.trans (hM x hx)
  have hT : ∀ κ' ∈ g '' decSet M L γ δ w Adm c β k0, GoodLabel (Molecule.eraseBond M R.added)
      (adjointCut K R h) L γ δ w P β (fun y => k0 y.1) r₀ ρ κ' := by
    rintro _ ⟨κ, hκ, rfl⟩
    exact good_of_hyper K R h hMol L γ δ w P β k0 r₀ ρ hκ.1 hparam.1 hκ.2.1 (hscale c κ hκ.1 hparam.1 hκ.2.2) (hr₀ κ hκ)
  have key := hL L hLL (Molecule.eraseBond M R.added) (adjointCut K R h) hMol' hM' hvine w P hP0 ρ hρ0 hρ2 hρL β
    (fun y => k0 y.1) r₀ (g '' decSet M L γ δ w Adm c β k0) hT
  have hcomm : ∀ κ, g (K.restrS κ) = (adjointCut K R h).restrS (g κ) := by
    intro κ
    funext y
    simp only [g, VineCut.restrS]
    rw [adj_cutMol_atom K R h y]
    rfl
  have hrestr : (adjointCut K R h).restrS '' (g '' decSet M L γ δ w Adm c β k0) =
      g '' (K.restrS '' decSet M L γ δ w Adm c β k0) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext κ
    exact (hcomm κ).symm
  have hzero : ∀ x : D, (x = R.added ∨ x = M.mate R.added) → ∀ κ : D → (Fin d → ℤ), K.restrS κ x = 0 := by
    intro x hx κ
    unfold VineCut.restrS
    rw [if_neg]
    rcases hx with rfl | rfl
    · exact cutMol_atom_added K R h
    · exact cutMol_atom_added_mate K R h
  have hinj : Set.InjOn g (K.restrS '' decSet M L γ δ w Adm c β k0) := by
    rintro _ ⟨κ1, -, rfl⟩ _ ⟨κ2, -, rfl⟩ hg
    funext x
    by_cases hx : x = R.added ∨ x = M.mate R.added
    · rw [hzero x hx κ1, hzero x hx κ2]
    · have hx' : x ≠ R.added ∧ x ≠ M.mate R.added := by tauto
      exact congrFun hg ⟨x, hx'⟩
  have e1 : (K.labelSet L γ δ w Adm c β k0).encard = (K.restrS '' decSet M L γ δ w Adm c β k0).encard := rfl
  rw [e1, ← hinj.encard_image, ← hrestr]
  have e2 : (adjointCut K R h).ladderProdVC L γ δ P = K.ladderProdVC L γ δ P := adj_ladderProdVC K R h L γ δ P
  have e3 : (adjointCut K R h).C.atoms.card = K.C.atoms.card := rfl
  rw [e2, e3] at key
  exact key

end WaveTurbulence.VineCount
