/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Fin

/-! # Counting solutions of triangular constraint systems

Let `B` be a finite index type with a rank `rank : B → ℕ`, and suppose that the constraint on the
coordinate `x b` says `x b ∈ N b x` with `N b x` a finset of cardinality `≤ M` depending on `x` only
through the coordinates of strictly smaller rank.  Then the set of solutions has at most `M ^ |B|`
elements.  (This is the counting behind the node centres of TARGET `treelemma`.)
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.RepAnalytic

theorem exists_injOn_fin {D : Type*} (s : Finset D) {M : ℕ} (h : s.card ≤ M) (hM : 0 < M) :
    ∃ g : D → Fin M, Set.InjOn g s := by
  classical
  refine ⟨fun v => if hv : v ∈ s then Fin.castLE h (s.equivFin ⟨v, hv⟩) else ⟨0, hM⟩, ?_⟩
  intro v hv w hw hvw
  simp only [Finset.mem_coe] at hv hw
  simp only [hv, hw, dite_true] at hvw
  have := s.equivFin.injective (Fin.castLE_injective h hvw)
  exact congrArg Subtype.val this

/-- **Triangular counting.** -/
theorem ncard_solutions_le {B D : Type*} [Fintype B] [DecidableEq B] (rank : B → ℕ) (M : ℕ) (hM : 0 < M)
    (N : B → (B → D) → Finset D) (hcard : ∀ b x, (N b x).card ≤ M)
    (hdep : ∀ b x y, (∀ b', rank b' < rank b → x b' = y b') → N b x = N b y) :
    {x : B → D | ∀ b, x b ∈ N b x}.Finite ∧
      {x : B → D | ∀ b, x b ∈ N b x}.ncard ≤ M ^ Fintype.card B := by
  classical
  have hex : ∀ s : Finset D, ∃ g : D → Fin M, s.card ≤ M → Set.InjOn g s := by
    intro s
    by_cases h : s.card ≤ M
    · obtain ⟨g, hg⟩ := exists_injOn_fin s h hM
      exact ⟨g, fun _ => hg⟩
    · exact ⟨fun _ => ⟨0, hM⟩, fun h' => absurd h' h⟩
  choose G hG using hex
  let Φ : (B → D) → (B → Fin M) := fun x b => G (N b x) (x b)
  have hinj : Set.InjOn Φ {x : B → D | ∀ b, x b ∈ N b x} := by
    intro x hx y hy hxy
    suffices hs : ∀ r, ∀ b, rank b = r → x b = y b from funext fun b => hs _ b rfl
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
    intro b hr
    have hlow : ∀ b', rank b' < rank b → x b' = y b' := fun b' hb' =>
      ih (rank b') (hr ▸ hb') b' rfl
    have hN : N b x = N b y := hdep b x y hlow
    have h1 : G (N b x) (x b) = G (N b x) (y b) := by
      have := congrFun hxy b
      simp only [Φ] at this
      rwa [← hN] at this
    exact hG (N b x) (hcard b x) (hx b) (hN ▸ hy b) h1
  have hfin : Set.Finite (Set.univ : Set (B → Fin M)) := Set.finite_univ
  refine ⟨Set.Finite.of_injOn (fun x _ => Set.mem_univ _) hinj hfin, ?_⟩
  calc {x : B → D | ∀ b, x b ∈ N b x}.ncard ≤ (Set.univ : Set (B → Fin M)).ncard :=
        Set.ncard_le_ncard_of_injOn Φ (fun x _ => Set.mem_univ _) hinj hfin
    _ = M ^ Fintype.card B := by
        rw [Set.ncard_univ, Nat.card_eq_fintype_card]
        simp

end WaveTurbulence.RepAnalytic
