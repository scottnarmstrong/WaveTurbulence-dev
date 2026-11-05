/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Carrier

/-! # The unique actual leaf partner in valid source forest data -/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton
open TTree

/-- The unique edge incident to a given actual leaf. -/
noncomputable def edgeAt {w : ℕ} (R : Raw w) (hR : R.Valid) (ℓ : GLeaf R.tree) : Pair w :=
  Classical.choose (hR.2 ℓ)

theorem edgeAt_spec {w : ℕ} (R : Raw w) (hR : R.Valid) (ℓ : GLeaf R.tree) :
    edgeAt R hR ℓ ∈ R.pairs ∧ ((edgeAt R hR ℓ).1 = ℓ.1 ∨ (edgeAt R hR ℓ).2 = ℓ.1) :=
  (Classical.choose_spec (hR.2 ℓ)).1

theorem edgeAt_unique {w : ℕ} (R : Raw w) (hR : R.Valid) (ℓ : GLeaf R.tree)
    (p : Pair w) (hp : p ∈ R.pairs) (he : p.1 = ℓ.1 ∨ p.2 = ℓ.1) : p = edgeAt R hR ℓ :=
  (Classical.choose_spec (hR.2 ℓ)).2 p ⟨hp,he⟩

/-- Opposite signs exclude a self-edge. -/
theorem valid_pair_ne {w : ℕ} (R : Raw w) (hR : R.Valid) (p : Pair w) (hp : p ∈ R.pairs) :
    p.1 ≠ p.2 := by
  intro he
  have hs := hR.1 p hp
  have h : (1 : ℤˣ) = -1 := hs.2.2.1.symm.trans ((congrArg (nodeSign R.sig) he).trans hs.2.2.2)
  exact (by decide : (1 : ℤˣ) ≠ -1) h

/-- The other endpoint, with its actual leaf membership proof. -/
noncomputable def rawPartner {w : ℕ} (R : Raw w) (hR : R.Valid) (ℓ : GLeaf R.tree) : GLeaf R.tree :=
  let p := edgeAt R hR ℓ
  let hp := hR.1 p (edgeAt_spec R hR ℓ).1
  if p.1 = ℓ.1 then ⟨p.2,hp.2.1⟩ else ⟨p.1,hp.1⟩

theorem rawPartner_val {w : ℕ} (R : Raw w) (hR : R.Valid) (ℓ : GLeaf R.tree) :
    (rawPartner R hR ℓ).1 =
      if (edgeAt R hR ℓ).1 = ℓ.1 then (edgeAt R hR ℓ).2 else (edgeAt R hR ℓ).1 := by
  by_cases h : (edgeAt R hR ℓ).1 = ℓ.1
  · simp [rawPartner,h]
  · simp [rawPartner,h]

/-- The same incident edge is recovered at its other endpoint. -/
theorem edgeAt_partner {w : ℕ} (R : Raw w) (hR : R.Valid) (ℓ : GLeaf R.tree) :
    edgeAt R hR (rawPartner R hR ℓ) = edgeAt R hR ℓ := by
  symm
  apply edgeAt_unique R hR _ _ (edgeAt_spec R hR ℓ).1
  rw [rawPartner_val]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- The actual source partner map is a fixed-point-free involution. -/
theorem rawPartner_involutive {w : ℕ} (R : Raw w) (hR : R.Valid) :
    Function.Involutive (rawPartner R hR) := by
  intro ℓ
  apply Subtype.ext
  rw [rawPartner_val,edgeAt_partner,rawPartner_val]
  have he := (edgeAt_spec R hR ℓ).2
  have hn := valid_pair_ne R hR _ (edgeAt_spec R hR ℓ).1
  by_cases h : (edgeAt R hR ℓ).1 = ℓ.1
  · rw [ite_eq_left h,ite_eq_right hn]
    exact h
  · rw [ite_eq_right h,ite_eq_left rfl]
    exact he.resolve_left h

theorem rawPartner_ne {w : ℕ} (R : Raw w) (hR : R.Valid) (ℓ : GLeaf R.tree) :
    rawPartner R hR ℓ ≠ ℓ := by
  intro he
  have hv := congrArg Subtype.val he
  rw [rawPartner_val] at hv
  have hn := valid_pair_ne R hR _ (edgeAt_spec R hR ℓ).1
  split_ifs at hv with h
  · exact hn (h.trans hv.symm)
  · exact h hv

theorem rawPartner_sign {w : ℕ} (R : Raw w) (hR : R.Valid) (ℓ : GLeaf R.tree) :
    nodeSign R.sig (rawPartner R hR ℓ).1 = -nodeSign R.sig ℓ.1 := by
  rw [rawPartner_val]
  have hp := hR.1 _ (edgeAt_spec R hR ℓ).1
  have he := (edgeAt_spec R hR ℓ).2
  by_cases h : (edgeAt R hR ℓ).1 = ℓ.1
  · rw [ite_eq_left h,← h,hp.2.2.1,hp.2.2.2]
  · have hl := he.resolve_left h
    rw [ite_eq_right h,← hl,hp.2.2.1,hp.2.2.2,neg_neg]

/-- A valid raw matching constructs its actual plain garden, with no choice of matching. -/
noncomputable def gardenOfRaw {w : ℕ} (R : Raw w) (hR : R.Valid) : Garden w where
  sig := R.sig
  tree := R.tree
  pair := rawPartner R hR
  mark _ := none
  pair_pair := rawPartner_involutive R hR
  pair_eq_iff ℓ := by simp only [ne_eq,not_true_eq_false,iff_false]; exact rawPartner_ne R hR ℓ
  pair_sign ℓ _ := rawPartner_sign R hR ℓ

theorem gardenOfRaw_plain {w : ℕ} (R : Raw w) (hR : R.Valid) : (gardenOfRaw R hR).IsPlain :=
  fun _ => rfl

end WaveTurbulence.Reg.Skeleton
