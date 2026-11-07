/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.ClassCount.ChainFam2
import Mathlib.Tactic

/-!
# CLASSCOUNT: total bound for a chain of classified ingredients

For the classification list `Ls` (one entry `(good, c, T)` per ingredient), `chain_total`: the layering sum over a
family distinct on the chain is at most
`(∏_{good} c) (∏_{bad} K^𝔇 2^𝔇 T) 2^{#good} (𝔇+1) K^𝔇 2^𝔇`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ClassCount
open Finset WaveTurbulence WaveTurbulence.Vine WaveTurbulence.LayerCnt

/-- The product factor of a classification list. -/
noncomputable def AL (𝔇 : ℕ) (K : ℝ) : List (Bool × ℝ × ℝ) → ℝ
  | [] => 1
  | e :: L => (if e.1 = true then e.2.1 else K ^ 𝔇 * 2 ^ 𝔇 * e.2.2) * AL 𝔇 K L

/-- The number of good ingredients. -/
def ngoodL : List (Bool × ℝ × ℝ) → ℕ
  | [] => 0
  | e :: L => (if e.1 = true then 1 else 0) + ngoodL L

theorem phi_lead_le {𝔇 : ℕ} {K : ℝ} (hK : 1 ≤ K) :
    ∀ L : List Link, (∀ l ∈ L, l.Ok 𝔇 K) →
      phi 𝔇 K L * 2 ^ lead L ≤ AL 𝔇 K (L.map Link.proj) * 2 ^ ngoodL (L.map Link.proj)
  | [], _ => by simp [phi, lead, AL, ngoodL]
  | l :: L, h => by
    have hl := h l (List.mem_cons_self ..)
    have hL : ∀ l' ∈ L, l'.Ok 𝔇 K := fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have ih := phi_lead_le hK L hL
    have hphi := phi_nonneg (𝔇 := 𝔇) hK L hL
    have hK0 : 0 < K := by linarith
    simp only [List.map_cons, AL, ngoodL, Link.proj]
    have e1 : phi 𝔇 K (l :: L) = if l.good = true then l.c * phi 𝔇 K L
        else K ^ 𝔇 * nu (lead L) 𝔇 * l.T * phi 𝔇 K L := rfl
    have e2 : lead (l :: L) = if l.good = true then lead L + 1 else 0 := rfl
    rw [e1, e2]
    by_cases hg : l.good = true
    · rw [if_pos hg, if_pos hg, if_pos hg, if_pos hg]
      have hc0 : 0 ≤ l.c := (hl.2.1 hg).1
      calc l.c * phi 𝔇 K L * 2 ^ (lead L + 1) = l.c * (phi 𝔇 K L * 2 ^ lead L) * 2 := by ring
        _ ≤ l.c * (AL 𝔇 K (L.map Link.proj) * 2 ^ ngoodL (L.map Link.proj)) * 2 := by
            gcongr
        _ = l.c * AL 𝔇 K (L.map Link.proj) * 2 ^ (1 + ngoodL (L.map Link.proj)) := by ring
    · have hg' : l.good = false := by simpa using hg
      rw [if_neg hg, if_neg hg, if_neg hg, if_neg hg, pow_zero, mul_one]
      have hT := link_T_nonneg hl hg'
      have hnu : nu (lead L) 𝔇 ≤ 2 ^ (𝔇 + lead L) := nu_le _ _
      have hKp : 0 ≤ K ^ 𝔇 := by positivity
      calc K ^ 𝔇 * nu (lead L) 𝔇 * l.T * phi 𝔇 K L
          ≤ K ^ 𝔇 * 2 ^ (𝔇 + lead L) * l.T * phi 𝔇 K L := by gcongr
        _ = K ^ 𝔇 * 2 ^ 𝔇 * l.T * (phi 𝔇 K L * 2 ^ lead L) := by ring
        _ ≤ K ^ 𝔇 * 2 ^ 𝔇 * l.T * (AL 𝔇 K (L.map Link.proj) * 2 ^ ngoodL (L.map Link.proj)) := by
            gcongr
        _ = _ := by ring

variable {V D : Type*} [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **The chain total.**  The list `Ts` of ingredient triples depends only on the chain. -/
theorem chain_total (M : Molecule V D) (hM : M.IsMolecule) {U : Finset V} {a b : V} {n : ℕ}
    (hC : Chain M U a b n) :
    ∃ Ts : List (Finset V × V × V), Ts.length = n ∧
      (∀ t ∈ Ts, ChainIngredient M U a b n t.1 t.2.1 t.2.2) ∧
      (Ts.map (fun t => t.1.erase t.2.1)).Pairwise Disjoint ∧
      ∀ {B : ℝ} (hB : 0 ≤ B) (𝔇 : ℕ) {K : ℝ} (hK : 1 ≤ K) (𝓖 : Finset (V → ℕ)) (h𝔇 : ∀ f ∈ 𝓖, ∀ x, f x ≤ 𝔇)
        (cls : Finset V → V → V → Bool × ℝ × ℝ) (U₀ : Finset V) (Inv : Finset V → V → V → Prop)
        (Ext : Finset V → V → V → Prop)
        (hInvStep : ∀ {S T : Finset V} {a b c : V} {n : ℕ}, Chain M S a b n → IsSomeVine M T b c → S ∩ T = {b} →
          M.IsBlock (S ∪ T) a c → Inv (S ∪ T) a c → Inv S a b)
        (hing : ∀ T x y, Ext T x y → (∃ U' a' b' n', U' ⊆ U₀ ∧ M.IsBlock U' a' b' ∧ Inv U' a' b' ∧
          ChainIngredient M U' a' b' n' T x y) → ∀ 𝓗 ⊆ 𝓖, (linkOf M B T x y 𝓗 (cls T x y)).Ok 𝔇 K),
        (∀ t ∈ Ts, Ext t.1 t.2.1 t.2.2) → U ⊆ U₀ → M.IsBlock U a b → Inv U a b →
        ∀ 𝓗 ⊆ 𝓖, DistinctOn U 𝓗 →
          ∑ f ∈ 𝓗, bw M B U f ≤ AL 𝔇 K (Ts.map (fun t => cls t.1 t.2.1 t.2.2)) *
            2 ^ ngoodL (Ts.map (fun t => cls t.1 t.2.1 t.2.2)) * (((𝔇 + 1 : ℕ) : ℝ) * (K ^ 𝔇 * 2 ^ 𝔇)) := by
  obtain ⟨Ts, hlen, hmem, hdisj, hmain⟩ := chain_fam M hM hC
  refine ⟨Ts, hlen, hmem, hdisj, ?_⟩
  intro B hB 𝔇 K hK 𝓖 h𝔇 cls U₀ Inv Ext hInvStep hing hExt hUU hU hInv 𝓗 h𝓗 hdist
  obtain ⟨L, hLmap, hLok, hLb⟩ := hmain hB 𝔇 K 𝓖 h𝔇 cls U₀ Inv Ext hInvStep hing hExt hUU hU hInv 𝓗 h𝓗 hdist
  have hmaps : ∀ f ∈ 𝓗, f b ∈ Finset.range (𝔇 + 1) := fun f hf =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le (h𝔇 f (h𝓗 hf) b))
  have hK0 : 0 < K := by linarith
  calc ∑ f ∈ 𝓗, bw M B U f
      = ∑ z ∈ Finset.range (𝔇 + 1), ∑ f ∈ 𝓗.filter (fun f => f b = z), bw M B U f :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ ≤ ∑ z ∈ Finset.range (𝔇 + 1), chainV 𝔇 L (fun _ => 1) z := Finset.sum_le_sum fun z _ => hLb z
    _ ≤ phi 𝔇 K L * ((𝔇 + 1 : ℕ) * (K ^ 𝔇 * 2 ^ (𝔇 + lead L))) := chain_bound_one hK L hLok
    _ = (phi 𝔇 K L * 2 ^ lead L) * (((𝔇 + 1 : ℕ) : ℝ) * (K ^ 𝔇 * 2 ^ 𝔇)) := by ring
    _ ≤ (AL 𝔇 K (L.map Link.proj) * 2 ^ ngoodL (L.map Link.proj)) *
          (((𝔇 + 1 : ℕ) : ℝ) * (K ^ 𝔇 * 2 ^ 𝔇)) := by
        exact mul_le_mul_of_nonneg_right (phi_lead_le hK L hLok) (by positivity)
    _ = _ := by rw [hLmap]

end WaveTurbulence.ClassCount
