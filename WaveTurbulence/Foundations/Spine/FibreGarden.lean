/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderCtx
public import WaveTurbulence.Foundations.Spine.FibreBij
public import WaveTurbulence.Foundations.Spine.NodeLocal
/-! # Changing the interior chain of a local ladder decoration (S3b LADDER-DECAY)

Garden level: from a local ladder decoration and new chart data with the same flux, build a local
ladder decoration with the new chain and the same labels off the interior atoms. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

/-- The `Xint` labelling of a decoration. -/
noncomputable def toXint (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (k : DecLab L base roots hP) : Xint C (Fin d → ℤ) :=
  ⟨k.1, k.2.1, (C.interior_cons hP hL base roots k).1, (C.interior_cons hP hL base roots k).2⟩

/-- Conservation (with the garden source) for the labelling with a swapped chain. -/
theorem swap_isDecoration (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (k : DecLab L base roots hP)
    (L' : {L : ChainLab n (Fin d → ℤ) // C.signs.IsSol L})
    (h1 : L'.1.a 0 = (C.xintEquiv (C.toXint hP hL base roots k)).2.1.a 0)
    (h2 : L'.1.b 0 = (C.xintEquiv (C.toXint hP hL base roots k)).2.1.b 0)
    (h3 : L'.1.a (Fin.last n) = (C.xintEquiv (C.toXint hP hL base roots k)).2.1.a (Fin.last n))
    (h4 : L'.1.b (Fin.last n) = (C.xintEquiv (C.toXint hP hL base roots k)).2.1.b (Fin.last n)) :
    G.molecule.IsDecoration L base (Mole.gardenSource G hP (rootVec L base roots))
      (C.swapChain (C.toXint hP hL base roots k) L').1 := by
  set κ' := C.swapChain (C.toXint hP hL base roots k) L' with hκ'
  have hend := fun x hx => C.swapChain_end (C.toXint hP hL base roots k) L' h1 h2 h3 h4 x hx
  refine ⟨κ'.2.1, ?_⟩
  intro a ha
  by_cases hai : a ∈ intAtoms u v
  · unfold intAtoms at hai
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hai
    rcases hai with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [gardenSource_eq_zero_of_deg_four G hP _ _ (C.deg_u i)]
      exact real_conservation _ (C.LD.uDart i) (C.LD.uDart_injective C.hinj i) (C.dartsAt_u i)
        (C.out_count _ (C.hat_u _) _ (C.LD.uDart_injective C.hinj i) (C.dartsAt_u i)) L base _ (κ'.2.2.1 i)
    · rw [gardenSource_eq_zero_of_deg_four G hP _ _ (C.deg_v i)]
      exact real_conservation _ (C.LD.vDart i) (C.LD.vDart_injective C.hinj i) (C.dartsAt_v i)
        (C.out_count _ (C.hat_v _) _ (C.LD.vDart_injective C.hinj i) (C.dartsAt_v i)) L base _ (κ'.2.2.2 i)
  · have := k.2.2 a ha
    rw [← this]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have hxa : G.molecule.atom x = a := (Finset.mem_filter.mp hx).2
    have := hend x (by rw [hxa]; exact hai)
    simp only [Molecule.kvec]
    rw [this]; rfl


/-- **Fibre element.** Given a decoration and a new chart with the same flux, a decoration with
the new chain, equal labels off the interior atoms. -/
theorem exists_fibre_element (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (zs : GenDecoration G d roots 0) (P : Fin n → (Fin d → ℤ) × (Fin d → ℤ))
    (hPc : ∑ k, (C.signs.tau P k 2 - C.signs.tau P k 3) =
      ∑ k, (C.signs.tau (C.signs.pairs (C.chainOf (bondIndex G zs.1))) k 2 -
        C.signs.tau (C.signs.pairs (C.chainOf (bondIndex G zs.1))) k 3)) :
    ∃ z' : GenDecoration G d roots 0,
      C.chainOf (bondIndex G z'.1) = C.signs.inv ((C.chainOf (bondIndex G zs.1)).a 0)
        ((C.chainOf (bondIndex G zs.1)).b 0) P ∧
      ∀ x, G.molecule.atom x ∉ intAtoms u v → bondIndex G z'.1 x = bondIndex G zs.1 x := by
  set k := decEquiv L base roots hP hL hn zs with hk
  have hkk : k.1 = bondIndex G zs.1 := rfl
  have hsol : C.signs.IsSol (C.chainOf k.1) :=
    (C.xintEquiv (C.toXint hP hL base roots k)).2.2
  rw [← hkk] at hPc
  obtain ⟨e1, e2, e3, e4⟩ := C.end_rails k.1 hsol P hPc
  set L' : {L : ChainLab n (Fin d → ℤ) // C.signs.IsSol L} :=
    ⟨C.signs.inv ((C.chainOf k.1).a 0) ((C.chainOf k.1).b 0) P, C.signs.isSol_inv _ _ _⟩ with hL'
  have hdec := C.swap_isDecoration hP hL base roots k L' e1 e2 e3 e4
  set k' : DecLab L base roots hP := ⟨(C.swapChain (C.toXint hP hL base roots k) L').1, hdec⟩ with hk'
  refine ⟨(decEquiv L base roots hP hL hn).symm k', ?_, ?_⟩
  · have hb : bondIndex G ((decEquiv L base roots hP hL hn).symm k').1 = k'.1 := by
      have := congrArg Subtype.val ((decEquiv L base roots hP hL hn).apply_symm_apply k')
      exact this
    rw [hb, ← hkk]
    have := C.chain_swapChain (C.toXint hP hL base roots k) L'
    exact congrArg Subtype.val this
  · intro x hx
    have hb : bondIndex G ((decEquiv L base roots hP hL hn).symm k').1 = k'.1 := by
      have := congrArg Subtype.val ((decEquiv L base roots hP hL hn).apply_symm_apply k')
      exact this
    rw [hb]
    exact C.swapChain_end (C.toXint hP hL base roots k) L' e1 e2 e3 e4 x hx

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay
