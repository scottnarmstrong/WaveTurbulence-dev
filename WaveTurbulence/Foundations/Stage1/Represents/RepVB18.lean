/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepVB17
public import WaveTurbulence.Foundations.Stage1.Represents.RepVN6
import Mathlib.Tactic

/-!
# S2 REPRESENTS, VINE-B♯ integration: the slot mode family of `G_sb` from the slot representation of the skeleton

`SlotFam.comapIota`: the family `s' ↦ fam (ι s')` of the slots of `G_sb` (VINE-B♯'s slot embedding).
`slotPackage_of_rep`: from a moment-carrying `SlotRepM` of the skeleton `S` (`slots_existM`) the mode family of `G_sb` with
the superposition identity of the outer slot kernels, the weighted moments and the masses of the outer slots.
`coreTimeDomainW_subset_spliced`: the open core domain lies in the closed spliced domain, so `SlotRepM.hbox` applies.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.VineB WaveTurbulence.RegRed
  WaveTurbulence.RedSplice WaveTurbulence.VineEstS3.FS WaveTurbulence.RegRedLeaf WaveTurbulence.RepAnalytic
open scoped ENNReal

variable {w d : ℕ} {S : Garden w} {J : Type} [Fintype J] [DecidableEq J] {blk : J → CLBlock S} {Gsb : Garden w}

/-- The slot mode family of `G_sb`: the family of the skeleton read at the embedded slots. -/
noncomputable def SlotFam.comapIota (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain)
    (fam : SlotFam S d) : SlotFam Gsb d where
  Λ s' := fam.Λ (Φ.iota hS hSb s')
  cnt s' := fam.cnt (Φ.iota hS hSb s')
  w s' := fam.w (Φ.iota hS hSb s')
  m s' := fam.m (Φ.iota hS hSb s')
  n s' := fam.n (Φ.iota hS hSb s')
  a s' := fam.a (Φ.iota hS hSb s')
  w_nn s' := fam.w_nn (Φ.iota hS hSb s')
  w_sum s' := fam.w_sum (Φ.iota hS hSb s')
  a_one s' := fam.a_one (Φ.iota hS hSb s')
  a_snorm s' := fam.a_snorm (Φ.iota hS hSb s')
  a_supp p l k := fam.a_supp (pairOfLeaf S hS (Φ.leaf (p.firstLeaf hSb))) l k

theorem coreTimeDomainW_subset_spliced (G : Garden w) (layer : GBranch G.tree → ℕ) (top : Fin w → ℝ) :
    coreTimeDomainW layer top ⊆ splicedTimeDomain G layer top := by
  intro τ h
  have hc := clock_iff (tree := G.tree) top τ
  exact ⟨fun v => ⟨(h v).1.le, (h v).2.1.le⟩, (hc.1 (fun b => (h b).2.2.2)).1, (hc.1 (fun b => (h b).2.2.2)).2⟩

open scoped Classical in
theorem slotPackage_of_rep (Φ : SpliceShape blk Gsb) (hS : S.IsPlain) (hSb : Gsb.IsPlain) {θ : ℝ}
    {layer0 : GBranch S.tree → ℕ} {tt : Fin w → ℝ} (Rep : SlotRepM θ S hS d layer0 tt) :
    ∃ fam : SlotFam Gsb d,
      (∀ s', ∀ ts ∈ Rep.Box (Φ.iota hS hSb s'), ∀ x, HasSum
        (fun l => (fam.w s' l : ℂ) * fam.a s' l x * fsPhase (fam.m s' l) ts) (Rep.Fn (Φ.iota hS hSb s') ts x)) ∧
      ∀ s', ∑' l, maxBracketPow θ (half (fam.m s' l)) * ENNReal.ofReal (fam.w s' l) ≤ Rep.μ (Φ.iota hS hSb s') := by
  obtain ⟨famS, h1, h2⟩ := exists_famM Rep
  exact ⟨SlotFam.comapIota Φ hS hSb famS, fun s' ts hts x => h1 _ ts hts x, fun s' => h2 _⟩

end WaveTurbulence.Represents
