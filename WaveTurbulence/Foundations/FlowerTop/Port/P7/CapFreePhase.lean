/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapIdentity
/-! FLOWER-P7: the cap with FREE root times `s : Fin 2 → ℝ` (kind `L0`, no `∂_t`): phases and the chain lemma of the
time domain. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

/-- The phase of the two roots at the times `s`. -/
noncomputable def rootPhaseS (L γ δ : ℝ) (k : Mom d) (s : Fin 2 → ℝ) (n : Fin (2 * 3) → (Fin d → ℤ)) : ℂ :=
  ∏ j : Fin 2, Complex.exp ((Real.pi * (((![1, -1] : Fin 2 → ℤˣ) j : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
    rootOmega L k (n (idx j 0)) (n (idx j 1)) (n (idx j 2)) * s j : ℝ) * Complex.I)

theorem rootPhaseS_const (L γ δ : ℝ) (k : Mom d) (t : ℝ) (n : Fin (2 * 3) → (Fin d → ℤ)) :
    rootPhaseS L γ δ k (fun _ => t) n = rootPhase L γ δ k t n := rfl

/-- The times of the cap: the roots at `s`, the other branching nodes from `σ`. -/
noncomputable def extendCapS (T : Fin (2 * 3) → TTree) (s : Fin 2 → ℝ) (σ : GBranch T → ℝ) :
    GBranch (capTree T) → ℝ :=
  fun b => ((capBranchEquiv T).symm b).elim s σ

theorem extendCapS_root (T : Fin (2 * 3) → TTree) (s : Fin 2 → ℝ) (σ : GBranch T → ℝ) (j : Fin 2) :
    extendCapS T s σ (rootBranch T j) = s j := by
  unfold extendCapS
  have : (capBranchEquiv T).symm (rootBranch T j) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]; rfl

theorem extendCapS_lift (T : Fin (2 * 3) → TTree) (s : Fin 2 → ℝ) (σ : GBranch T → ℝ) (a : GBranch T) :
    extendCapS T s σ (liftBranch a) = σ a := by
  unfold extendCapS
  have : (capBranchEquiv T).symm (liftBranch a) = Sum.inr a := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]; rfl

theorem phaseProd_capS (L γ δ : ℝ) (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (k : Mom d)
    (s : Fin 2 → ℝ) (κ' : GNode G.tree → (Fin d → ℤ)) (σ : GBranch G.tree → ℝ) :
    phaseProdOff L γ δ (capGarden G hsig) ∅
        (cosetDecoration (capGarden G hsig) L k (upperDec (T := G.tree) κ')) (extendCapS G.tree s σ) =
      rootPhaseS L γ δ k s (fun c => κ' (GNode.root G.tree c)) *
        phaseProdOff L γ δ G ∅ (cosetDecoration G L k κ') σ := by
  unfold phaseProdOff
  simp only [Finset.notMem_empty, if_false]
  rw [prod_cap_branch]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [extendCapS_root, sign_cap_root, omega_cap_root]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [extendCapS_lift, liftBranch_toNode, sign_cap_lift, omega_cap_lift]

/-- A branching node of a nonempty address has a parent. -/
theorem exists_parent_branch {w : ℕ} {T : Fin w → TTree} (b : GBranch T) (hne : b.1.2 ≠ []) :
    ∃ b0 : GBranch T, b.IsChildOf b0 := by
  obtain ⟨⟨j, path⟩, hb⟩ := b
  rcases List.eq_nil_or_concat path with h | ⟨a, i, h⟩
  · exact absurd h hne
  · have h' : path = a ++ [i] := by simpa using h
    subst h'
    have h1 : a ++ [i] ∈ (T j).nodes := TTree.branching_subset_nodes _ hb
    have h2 : a ∈ (T j).branching := TTree.branching_of_append_mem (T j) h1
    exact ⟨⟨(j, a), h2⟩, rfl, i, rfl⟩

/-- In the time domain (nothing designated) every branching node is earlier than the root of its tree, strictly
unless it is the root. -/
theorem domain_lt_root {w : ℕ} (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (τ : GBranch LG.garden.tree → ℝ) (hτ : τ ∈ kDomainFix LG up (fun _ => none)) :
    ∀ (n : ℕ) (b : GBranch LG.garden.tree), b.1.2.length = n + 1 →
      ∃ r : GBranch LG.garden.tree, r.1.1 = b.1.1 ∧ r.1.2 = [] ∧ τ b < τ r := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hb
    have hne : b.1.2 ≠ [] := by intro h; rw [h] at hb; simp at hb
    obtain ⟨b0, hb0⟩ := exists_parent_branch b hne
    have hlt : τ b < τ b0 := (hτ b0).2 b hb0 (Or.inl rfl)
    have hlen : b0.1.2.length + 1 = b.1.2.length := by
      obtain ⟨-, i, hi⟩ := hb0
      rw [hi]; simp
    by_cases h0 : b0.1.2 = []
    · exact ⟨b0, hb0.1.symm, h0, hlt⟩
    · have hl : 1 ≤ b0.1.2.length := by
        rcases Nat.eq_zero_or_pos b0.1.2.length with h | h
        · exact absurd (List.length_eq_zero_iff.1 h) h0
        · exact h
      obtain ⟨r, hr1, hr2, hr3⟩ := ih (b0.1.2.length - 1) (by omega) b0 (by omega)
      exact ⟨r, hr1.trans hb0.1.symm, hr2, hlt.trans hr3⟩

end WaveTurbulence.FlowerP7
