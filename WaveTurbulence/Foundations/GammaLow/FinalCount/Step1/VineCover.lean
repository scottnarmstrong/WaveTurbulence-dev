/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.VineCover
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Step1.VineBase
/-! **L6-STEP1 port of main `WaveTurbulence.Foundations.FinalCount.VineCover`** (sha256 in Step1/COPIED-SHA256SUMS): only the declarations that
depend on the Step-1 cut `VineCut`, re-stated over the `𝒱_γ` object carrier `Src.Object g M`; everything else is
main's, by import.

 Vine removal, part 2 (FINALCOUNT-G2): the exact cover of `𝔈(M)` by the label vector of the removed VC.
`𝔈(M) ≤ N · 𝔈(post)` where `N` bounds the number of restrictions `κ|_{VC darts}` (DH23 (fbyg) L1799: `𝔉`, the number
of choices for `(k_ℓ)_{ℓ ∈ VC}`); the parameters of `post` at the new atoms `fa, fb` are `c(joint) - (VC part)`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical Set
namespace WaveTurbulence.GammaLow.FinalCount.Step1
open WaveTurbulence.FinalCount
variable {g : ℝ}
open WaveTurbulence WaveTurbulence.LGSpine.SourceVine

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

namespace VineCut
open WaveTurbulence.FinalCount.VineCut
variable {M : Molecule V D} (K : VineCut g M)

theorem atom_x₁ : K.cutMol.atom K.x₁ = K.C.upper := by
  have h1 : K.m1.atom K.x₁ = K.C.upper := by
    show (M.cut K.C.upper K.fa K.x₁ K.x₂).atom K.x₁ = _
    rw [cut_atom, if_neg (fun h => h.2.1 rfl)]; exact K.cut_a.2.2.1
  change (K.m1.cut K.C.lower K.fb K.y₁ K.y₂).atom K.x₁ = _
  rw [cut_atom, h1, if_neg (fun h => K.ab_ne h.1)]

theorem atom_x₂ : K.cutMol.atom K.x₂ = K.C.upper := by
  have h1 : K.m1.atom K.x₂ = K.C.upper := by
    show (M.cut K.C.upper K.fa K.x₁ K.x₂).atom K.x₂ = _
    rw [cut_atom, if_neg (fun h => h.2.2 rfl)]; exact K.cut_a.2.2.2.1
  change (K.m1.cut K.C.lower K.fb K.y₁ K.y₂).atom K.x₂ = _
  rw [cut_atom, h1, if_neg (fun h => K.ab_ne h.1)]

theorem atom_y₁ : K.cutMol.atom K.y₁ = K.C.lower := by
  change (K.m1.cut K.C.lower K.fb K.y₁ K.y₂).atom K.y₁ = _
  rw [cut_atom, if_neg (fun h => h.2.1 rfl)]; exact K.cut_b.2.2.1

theorem atom_y₂ : K.cutMol.atom K.y₂ = K.C.lower := by
  change (K.m1.cut K.C.lower K.fb K.y₁ K.y₂).atom K.y₂ = _
  rw [cut_atom, if_neg (fun h => h.2.2 rfl)]; exact K.cut_b.2.2.2.1

/-- The label restriction to the darts of the removed atoms. -/
noncomputable def restrS (κ : D → (Fin d → ℤ)) : D → (Fin d → ℤ) :=
  fun x => if K.cutMol.atom x ∈ K.C.atoms then κ x else 0

/-- The VC part of `c(a)`, `Γ(a)` at the upper joint, for the labels `i`. -/
noncomputable def jointC (L : ℝ) (w : Mom d) (i : D → (Fin d → ℤ)) (p q : D) : Mom d :=
  M.dartSign p • Molecule.kvec L w i p + M.dartSign q • Molecule.kvec L w i q

noncomputable def jointE (L : ℝ) (w : Mom d) (i : D → (Fin d → ℤ)) (p q : D) : ℝ :=
  M.dartSign p * ‖Molecule.kvec L w i p‖ ^ 2 + M.dartSign q * ‖Molecule.kvec L w i q‖ ^ 2

/-- The parameter triple of `post` for the labels `i`. -/
noncomputable def postParams (L : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d)
    (i : D → (Fin d → ℤ)) :
    (V → Mom d) × (V → ℝ) × (PDart K.cutMol (fun a => a ∉ K.C.atoms) → Mom d) :=
  (fun z => if z = K.fa then c K.C.upper - jointC (M := M) L w i K.x₁ K.x₂
      else if z = K.fb then c K.C.lower - jointC (M := M) L w i K.y₁ K.y₂ else c z,
   fun z => if z = K.fa then β K.C.upper - jointE (M := M) L w i K.x₁ K.x₂
      else if z = K.fb then β K.C.lower - jointE (M := M) L w i K.y₁ K.y₂ else β z,
   fun x => k0 x.1)

theorem deg_fa : K.cutMol.deg K.fa + 2 = M.deg K.C.upper := by
  have := K.sum_a (fun _ => (1 : ℕ))
  simpa [Molecule.deg] using this.symm

theorem deg_fb : K.cutMol.deg K.fb + 2 = M.deg K.C.lower := by
  have := K.sum_b (fun _ => (1 : ℕ))
  simpa [Molecule.deg] using this.symm

theorem postParams_ok (hM : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L : ℝ) (w : Mom d) (c : V → Mom d) (β : V → ℝ)
    (k0 : D → Mom d) (hP : ParamOK M c k0) (i : D → (Fin d → ℤ)) :
    ParamOK K.post (K.postParams L w c β k0 i).1 (K.postParams L w c β k0 i).2.2 := by
  refine ⟨fun z hz hdeg => ?_, fun x => hP.2 x.1⟩
  have hz' : z ∈ K.cutMol.atoms ∧ z ∉ K.C.atoms := Finset.mem_filter.mp hz
  have hdeg' : K.cutMol.deg z = 4 := by
    have := restrictP_deg K.cutMol (fun a => a ∉ K.C.atoms) K.closed hz'.2
    exact this ▸ hdeg
  by_cases hfa : z = K.fa
  · subst hfa
    have := K.deg_fa; have := hM _ K.a_atom; omega
  by_cases hfb : z = K.fb
  · subst hfb
    have := K.deg_fb; have := hM _ K.b_atom; omega
  have hzM : z ∈ M.atoms := by
    have := hz'.1
    rw [show K.cutMol.atoms = insert K.fb (insert K.fa M.atoms) from rfl] at this
    simp only [Finset.mem_insert] at this
    rcases this with h | h | h
    · exact absurd h hfb
    · exact absurd h hfa
    · exact h
  have hza : z ≠ K.C.upper := fun e => hz'.2 (e ▸ K.a_mem)
  have hzb : z ≠ K.C.lower := fun e => hz'.2 (e ▸ K.b_mem)
  have e : (K.postParams L w c β k0 i).1 z = c z := by
    unfold postParams; simp only [if_neg hfa, if_neg hfb]
  show (K.postParams L w c β k0 i).1 z = 0
  rw [e]
  refine hP.1 z hzM ?_
  unfold Molecule.deg at hdeg' ⊢
  rwa [K.dartsAt_other hzM hza hzb] at hdeg'

end VineCut
end WaveTurbulence.GammaLow.FinalCount.Step1
