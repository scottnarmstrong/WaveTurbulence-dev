/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepTriv1
public import WaveTurbulence.Foundations.Stage1.Represents.RepTriv2
import Mathlib.Tactic

/-!
# S2 REPRESENTS: trivial couple and trivial tree slots

A trivial couple kernel is the single input profile; a trivial tree kernel is `1`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open WaveTurbulence WaveTurbulence.RepAnalytic WaveTurbulence.LGSpine WaveTurbulence.VineEstS3.FS
open scoped ENNReal

open Classical in
/-- The explicit constant of the profile superposition (depends only on `d`). -/
noncomputable def profC (d : ℕ) : ℝ := if h : 1 ≤ d then (cenSup_profile h).choose else 1

theorem profC_spec {d : ℕ} (hd : 1 ≤ d) : 0 < profC d ∧ ∀ (Bx : Set (Fin 2 → ℝ)) (H : Mom d → ℝ) (B : ℝ), 0 ≤ B →
      SNormR (40 * d) (40 * d) H ≤ ENNReal.ofReal B →
      CenSup (30 * d) Bx (fun _ k => (H k : ℂ)) (ENNReal.ofReal (profC d * B)) := by
  have e : profC d = (cenSup_profile hd).choose := by unfold profC; simp only [hd, ↓reduceDIte]
  rw [e]; exact (cenSup_profile hd).choose_spec

theorem couple_slot_triv {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ C = profC d ∧ ∀ (L γ δ : ℝ) (Bx : Set (Fin 2 → ℝ)) (LG : LayeredGarden 2),
      RegCpl.triv.Decodes LG.garden → ∀ (H : LeafProfiles 2 d) (B : (Fin 2 × TTree.Path) → NNReal),
      LeafwiseControlled LG H B →
      CenSup (30 * d) Bx (fun ts k => coupleLeaves L γ δ LG H (ts 0) (ts 1) k)
        (ENNReal.ofReal (C * leafSizeProduct LG B)) := by
  obtain ⟨hC, h⟩ := profC_spec hd
  refine ⟨profC d, hC, rfl, fun L γ δ Bx LG hQ H B hctrl => ?_⟩
  obtain ⟨ℓ0, -, hin, hk⟩ := coupleLeaves_triv L γ δ LG H hQ 0 0 (0 : Mom d)
  have hmem : ℓ0 ∈ inputLeaves LG.garden := by rw [hin]; exact Finset.mem_singleton_self _
  have hsz : leafSizeProduct LG B = (B ℓ0.1 : ℝ) := by
    unfold leafSizeProduct; rw [hin, Finset.prod_singleton]
  rw [hsz]
  refine (h Bx (H ℓ0.1) (B ℓ0.1 : ℝ) (NNReal.coe_nonneg _) (hctrl ℓ0 hmem)).congr ?_
  intro ts _ k
  obtain ⟨ℓ1, -, hin1, hk1⟩ := coupleLeaves_triv L γ δ LG H hQ (ts 0) (ts 1) k
  have : ℓ1 = ℓ0 := Finset.singleton_injective (hin1.symm.trans hin)
  subst this
  exact hk1.symm

theorem tree_slot_nil {d : ℕ} (Bx : Set (Fin 2 → ℝ)) (L γ δ : ℝ) (LG : LayeredGarden 1)
    (hX : RegChain.nil.DecodesTree LG.garden) (H : LeafProfiles 1 d) (B : (Fin 1 × TTree.Path) → NNReal) :
    Sup (30 * d) Bx (fun ts k => treeLeaves L γ δ LG H (ts 0) (ts 1) k)
      (ENNReal.ofReal (leafSizeProduct LG B)) := by
  have hsz : leafSizeProduct LG B = 1 := by
    unfold leafSizeProduct; rw [(treeLeaves_nil L γ δ LG H hX 0 0 (0 : Mom d)).1, Finset.prod_empty]
  rw [hsz, ENNReal.ofReal_one]
  refine (sup_one (d := d) (30 * d) Bx).congr ?_
  intro ts _ k
  exact ((treeLeaves_nil L γ δ LG H hX (ts 0) (ts 1) k).2).symm

end WaveTurbulence.Represents
