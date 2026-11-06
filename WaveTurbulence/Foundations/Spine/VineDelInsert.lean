/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.VineDelPaths
import Mathlib.Tactic
/-! # Lifting filtered paths through rung insertion -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Vine

/-- The first (upper) inserted rail atoms. -/
@[expose] def usOf (T : VineTemplate) (k : ℕ) : List ℕ := (List.range k).map (T.n + ·)
/-- The second inserted rail atoms. -/
@[expose] def vsOf (T : VineTemplate) (k : ℕ) : List ℕ := (List.range k).map (T.n + k + ·)

theorem rung_mem (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0) {i : ℕ}
    (hi : i < k) : (T.n + i, T.n + k + i) ∈ (insertRungs T s k).bonds := by
  simp only [insertRungs, hk, ite_false, List.mem_append]
  right
  rw [List.mem_flatMap]
  refine ⟨(T.n + i, T.n + k + i), ?_, by simp⟩
  rw [List.zip_map']
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

theorem lift_edge (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0)
    (P : ℕ → Prop) (f : ℕ × ℕ → Bool) {p q : ℕ} (he : (p, q) ∈ T.bonds) (hp : P p) (hq : P q)
    (h1 : (p, q) = s.1 → (∀ x ∈ usOf T k, P x) ∧ ∀ e ∈ railBonds s.1.1 (usOf T k) s.1.2, f e = true)
    (h2 : (p, q) = s.2 → (∀ x ∈ vsOf T k, P x) ∧ ∀ e ∈ railBonds s.2.1 (vsOf T k) s.2.2, f e = true)
    (h3 : (p, q) ≠ s.1 → (p, q) ≠ s.2 → f (p, q) = true) :
    Relation.EqvGen (FAdj P f (insertRungs T s k).bonds) p q := by
  by_cases e1 : (p, q) = s.1
  · obtain ⟨hu, hf⟩ := h1 e1
    have hpq : p = s.1.1 ∧ q = s.1.2 := ⟨congrArg Prod.fst e1, congrArg Prod.snd e1⟩
    obtain ⟨rfl, rfl⟩ := hpq
    have := rail_fpath P f _ (usOf T k) _ hp hq hu hf
    exact fpath_mono (fun _ h => h) (fun _ h => h) (fun _ h => first_rail_mem T s hk h) this
  · by_cases e2 : (p, q) = s.2
    · obtain ⟨hu, hf⟩ := h2 e2
      have hpq : p = s.2.1 ∧ q = s.2.2 := ⟨congrArg Prod.fst e2, congrArg Prod.snd e2⟩
      obtain ⟨rfl, rfl⟩ := hpq
      have := rail_fpath P f _ (vsOf T k) _ hp hq hu hf
      exact fpath_mono (fun _ h => h) (fun _ h => h) (fun _ h => second_rail_mem T s hk h) this
    · exact fpath_edge hp hq (mem_insertRungs_bonds he e1 e2 k) (h3 e1 e2)

theorem lift_path (T : VineTemplate) (s : (ℕ × ℕ) × (ℕ × ℕ)) {k : ℕ} (hk : k ≠ 0)
    (P0 P : ℕ → Prop) (hPQ : ∀ x, P0 x → P x) (f g : ℕ × ℕ → Bool)
    (fg : ∀ e, f e = true → g e = true)
    (h1 : f s.1 = true → (∀ x ∈ usOf T k, P x) ∧ ∀ e ∈ railBonds s.1.1 (usOf T k) s.1.2, g e = true)
    (h2 : f s.2 = true → (∀ x ∈ vsOf T k, P x) ∧ ∀ e ∈ railBonds s.2.1 (vsOf T k) s.2.2, g e = true)
    {p q : ℕ} (hp : Relation.EqvGen (FAdj P0 f T.bonds) p q) :
    Relation.EqvGen (FAdj P g (insertRungs T s k).bonds) p q := by
  induction hp with
  | rel u v huv =>
    rcases huv.2.2 with ⟨he, hf⟩ | ⟨he, hf⟩
    · exact lift_edge T s hk P g he (hPQ _ huv.1) (hPQ _ huv.2.1) (fun e1 => h1 (e1 ▸ hf)) (fun e2 => h2 (e2 ▸ hf))
        (fun _ _ => fg _ hf)
    · exact Relation.EqvGen.symm _ _ (lift_edge T s hk P g he (hPQ _ huv.2.1) (hPQ _ huv.1) (fun e1 => h1 (e1 ▸ hf))
        (fun e2 => h2 (e2 ▸ hf)) (fun _ _ => fg _ hf))
  | refl u => exact Relation.EqvGen.refl _
  | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans u v w _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end WaveTurbulence.LGSpine
