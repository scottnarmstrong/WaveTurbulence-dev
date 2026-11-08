/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKDefs.Count
public import WaveTurbulence.Foundations.FinalCount.LowGardenOne

/-! # C1c MK-GARDEN / Single: the one-atom garden and the `m = 0` reductions (independent of the pool repair)

A one-atom garden has no survivor (an object has distinct joints, both among its atoms), so `S.m = 0` and the count is
main's `lowGarden_single_atom`. -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.FinalMKGarden
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.FinalCountAsm WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

theorem surv_m_eq_zero_of_one_atom {w : ℕ} {G : Garden w} (S : SurvivorData G)
    (hone : G.molecule.atoms.card = 1) : S.m = 0 := by
  by_contra hm
  have i : Fin S.m := ⟨0, Nat.pos_of_ne_zero hm⟩
  have hu := object_mem_of_joint (S.surv i) (Or.inl rfl)
  have hl := object_mem_of_joint (S.surv i) (Or.inr rfl)
  have hs := objectAtoms_sub (S.surv i)
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hone
  rw [ha] at hs
  have h1 := Finset.mem_singleton.1 (hs hu)
  have h2 := Finset.mem_singleton.1 (hs hl)
  exact WaveTurbulence.Subpro.Object.upper_ne_lower' (S.surv i) (h1.trans h2.symm)

theorem numCriticalSGMK_of_m_zero {w d : ℕ} {G : Garden w} (C : CountingChoices G d) (S : SurvivorData G)
    (hm : S.m = 0) : numCriticalSGMK C S = C.numCriticalSG := by
  unfold numCriticalSGMK CountingChoices.numCriticalSG CriticalSGMK
  congr 1
  ext v
  have hE : ∀ i : Fin S.m, False := fun i => by have := i.2; omega
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, fun i => (hE i).elim⟩⟩

/-- The one-atom garden, with survivors (there are none). -/
theorem allGardenMK_single_atom {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ} (hγ1 : γ < 1) (hη : 0 < η) (hη40 : η ≤ 1 / 40)
    {R : ℕ} (G : Garden (2 * R)) (hp : G.IsPlain) (hR : 1 ≤ R) (D : SplicedKernelData G d)
    (C : CountingChoices G d) (S : SurvivorData G)
    (hD : D.hinges = C.subpro.hinges) (hg : CountingGeometry G C) (hone : G.molecule.atoms.card = 1)
    {L : ℝ} (hL : 1 ≤ L) {C1 δ : ℝ} (hC1 : 1 ≤ C1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop)
    (hA : ∀ κ, Adm κ → splicedCountingAdmissibleMK G D C S L γ η base roots κ) :
    G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
      ENNReal.ofReal (L ^ (2 * (S.m : ℝ)) * L ^ (-4 * η ^ 6 * (G.molecule.rho + numCriticalSGMK C S)) *
        L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40))) := by
  have hm := surv_m_eq_zero_of_one_atom S hone
  have h := FinalCountAsm.lowGarden_single_atom hd hγ1 hη hη40 G hp hR D C hD hg hone hL hC1 hδ hδ1 base roots Adm
    (fun κ hκ => admissible_of_MK_zero D C S hm L γ η base roots κ (hA κ hκ))
  rw [numCriticalSGMK_of_m_zero C S hm, hm]
  simpa using h

end WaveTurbulence.Flower.FinalMKGarden
