/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN10
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 11): equal post states remove the same atoms.**  `vinePost_atoms_eq`: if two vine cuts
`K, K'` of `h` (same `h`) give equal post states, then `K'.C.atoms = K.C.atoms`.  This reduces `VHard.hcls`/`hconn` (quantified over all
`K'` with the same post) to cuts along objects with the atoms of `U`. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

theorem vinePost_atoms {h : HSt V D₀} (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) :
    (h.vinePost K R kp).s.M.atoms = (insert K.fb (insert K.fa h.s.M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl

theorem vinePost_atoms_eq {h : HSt V D₀} {K K' : VineCut h.s.M} {R R' : ℝ} {kp kp' : ℕ}
    (he : h.vinePost K R kp = h.vinePost K' R' kp') : K'.C.atoms = K.C.atoms := by
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
theorem vhard_of_atoms {crit : V → Prop} {h : HSt V D₀} {K : VineCut h.s.M}
    (hcls0 : ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → SingleVineVC K' ∨ Nonempty (DoubleShape K'))
    (hconn0 : ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → Nonempty (DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G)
    (hrho : h.s.M.rho ≤ K.post.rho + 86)
    (hint : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a) : VHard crit h K :=
  ⟨fun _ _ K' _ _ he => hcls0 K' (vinePost_atoms_eq he),
    fun _ _ K' _ _ he => hconn0 K' (vinePost_atoms_eq he), hrho, hint⟩

end WaveTurbulence.FinalCountAsm
