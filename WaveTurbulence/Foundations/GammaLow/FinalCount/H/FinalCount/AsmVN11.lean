/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN11
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN10
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.Gamma
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmVN11`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (VineNodeExists, part 11): equal post states remove the same atoms.**  `vinePost_atoms_eq`: if two vine cuts
`K, K'` of `h` (same `h`) give equal post states, then `K'.C.atoms = K.C.atoms`.  This reduces `VHard.hcls`/`hconn` (quantified over all
`K'` with the same post) to cuts along objects with the atoms of `U`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

theorem vinePost_atoms {h : HSt V D₀} (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ) :
    (h.vinePostL K R kp).s.M.atoms = (insert K.fb (insert K.fa h.s.M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl

theorem vinePost_atoms_eq {h : HSt V D₀} {K K' : Step1.VineCut Src.γL h.s.M} {R R' : ℝ} {kp kp' : ℕ}
    (he : h.vinePostL K R kp = h.vinePostL K' R' kp') : K'.C.atoms = K.C.atoms := by
  have h1 := congrArg (fun x : HSt V D₀ => x.s.M.atoms) he
  simp only [vinePost_atoms] at h1
  have hsub := (object_oh K.C).basic.1
  have hsub' := (object_oh K'.C).basic.1
  ext v
  by_cases hv : v ∈ h.s.M.atoms
  · have hfa : v ≠ K.fa := fun e => K.cut_a.2.1 (e ▸ hv)
    have hfb : v ≠ K.fb := fun e => K.cut_b.2.1 (by simp [e] at hv ⊢; exact Finset.mem_insert_of_mem (e ▸ hv))
    have hfa' : v ≠ K'.fa := fun e => K'.cut_a.2.1 (e ▸ hv)
    have hfb' : v ≠ K'.fb := fun e => K'.cut_b.2.1 (by simp [e] at hv ⊢; exact Finset.mem_insert_of_mem (e ▸ hv))
    have := Finset.ext_iff.mp h1 v
    simp only [Finset.mem_filter, Finset.mem_insert, hfa, hfb, hfa', hfb', false_or, hv, true_and] at this
    exact (not_iff_not.mp this).symm
  · exact ⟨fun h' => absurd (hsub' h') hv, fun h' => absurd (hsub h') hv⟩

/-- `VHard` from atom-level statements: `hcls`/`hconn` need only be proved for the cuts that remove the atoms of `K`. -/
theorem vhard_of_atoms {crit : V → Prop} {h : HSt V D₀} {K : Step1.VineCut Src.γL h.s.M}
    (hcls0 : ∀ K' : Step1.VineCut Src.γL h.s.M, K'.C.atoms = K.C.atoms → Step1.SingleVineVCGamma K' ∨ Nonempty (Step1.DoubleShape K'))
    (hconn0 : ∀ K' : Step1.VineCut Src.γL h.s.M, K'.C.atoms = K.C.atoms → Nonempty (Step1.DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G)
    (hrho : h.s.M.rho ≤ K.post.rho + 86)
    (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a) : VHard crit h K :=
  ⟨fun _ _ K' _ _ he => hcls0 K' (vinePost_atoms_eq he),
    fun _ _ K' _ _ he => hconn0 K' (vinePost_atoms_eq he), hrho, hint⟩

end WaveTurbulence.GammaLow.FinalCount.H
