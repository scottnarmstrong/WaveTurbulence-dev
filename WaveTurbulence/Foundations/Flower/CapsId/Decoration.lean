/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsId.Garden
/-! # A2 CAPS-ID: decorations of the capped garden (supplement Lemma 2.1(3))

Restriction and extension give a bijection between the flower decorations of `G` with roots `nr` and flowers
`n'` and the ordinary decorations of `capGarden G` with original roots `nr` and all cap roots `n'`
(`capDecEquiv`). It needs exactly one flower per tree (`OneFlower`); the value `m` prescribed at flowers of the
capped garden is then void. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsId
open TTree Finset WaveTurbulence.FlowerP7

variable {w d : ℕ}

/-- The capped roots: original roots `nr`, every cap root `n'`. -/
def capRoots {V : Type*} (nr : Fin w → V) (n' : V) : Fin (2 * w) → V :=
  fun c => Sum.elim nr (fun _ => n') ((capσ w).symm c)

@[simp] theorem capRoots_inl {V : Type*} (nr : Fin w → V) (n' : V) (j : Fin w) :
    capRoots nr n' (capσ w (.inl j)) = nr j := by simp [capRoots]

@[simp] theorem capRoots_inr {V : Type*} (nr : Fin w → V) (n' : V) (j : Fin w) :
    capRoots nr n' (capσ w (.inr j)) = n' := by simp [capRoots]

/-- Extension of an original labelling by the value `n'` at every cap. -/
def capLabel {V : Type*} (G : Garden w) (κ : GNode G.tree → V) (n' : V) : GNode (capGarden G).tree → V :=
  fun x => Sum.elim κ (fun _ => n') ((cNode G).symm x)

@[simp] theorem capLabel_embN {V : Type*} (G : Garden w) (κ : GNode G.tree → V) (n' : V) (a : GNode G.tree) :
    capLabel G κ n' (embN G a) = κ a := by simp [capLabel]

@[simp] theorem capLabel_capN {V : Type*} (G : Garden w) (κ : GNode G.tree → V) (n' : V) (j : Fin w) :
    capLabel G κ n' (capN G j) = n' := by simp [capLabel]

/-- A chosen flower is fixed by the original pairing. -/
theorem pair_of_flowerOf {G : Garden w} {ℓ : GLeaf G.tree} (h : flowerOf G ℓ.1.1 = some ℓ) : G.pair ℓ = ℓ := by
  have hfl := (flowerOf_spec h).2
  apply (G.pair_eq_iff ℓ).2
  unfold Garden.IsFlower at hfl
  rw [hfl]; exact Option.some_ne_none _

/-- Restriction of a capped decoration is a decoration. -/
theorem isDecoration_restrict {V : Type*} [AddCommGroup V] (G : Garden w) (κ : GNode (capGarden G).tree → V)
    (h : IsDecoration (capGarden G) κ) : IsDecoration G (fun a => κ (embN G a)) := by
  refine ⟨fun b => ?_, fun ℓ => ?_⟩
  · have := h.1 (cBranch G b)
    simpa only [cBranch_toNode, cBranch_child] using this
  · by_cases hc : flowerOf G ℓ.1.1 = some ℓ
    · simp only [pair_of_flowerOf hc]
    · have := h.2 (embL G ℓ)
      rw [capGarden_pair_embL, ite_eq_right hc, embL_toNode, embL_toNode] at this
      exact this

/-- Extension of a decoration (with value `n'` at the flowers) by `n'` at the caps is a decoration. -/
theorem isDecoration_capLabel {V : Type*} [AddCommGroup V] (G : Garden w) (κ : GNode G.tree → V) (n' : V)
    (h : IsDecoration G κ) (hfl : ∀ ℓ : GLeaf G.tree, G.IsFlower ℓ → κ ℓ.toNode = n') :
    IsDecoration (capGarden G) (capLabel G κ n') := by
  refine ⟨fun b => ?_, fun x => ?_⟩
  · obtain ⟨b, rfl⟩ := (cBranch G).surjective b
    simpa only [cBranch_toNode, cBranch_child, capLabel_embN] using h.1 b
  · rcases leaf_cases G x with ⟨ℓ, rfl⟩ | ⟨j, rfl⟩
    · rw [capGarden_pair_embL]
      by_cases hc : flowerOf G ℓ.1.1 = some ℓ
      · rw [ite_eq_left hc, embL_toNode, capL_toNode, capLabel_embN, capLabel_capN]
        exact hfl ℓ (flowerOf_spec hc).2
      · rw [ite_eq_right hc, embL_toNode, embL_toNode, capLabel_embN, capLabel_embN]
        exact h.2 ℓ
    · rw [capGarden_pair_capL]
      rcases hf : flowerOf G j with _ | ℓ
      · rfl
      · show capLabel G κ n' (capL G j).toNode = capLabel G κ n' (embL G ℓ).toNode
        rw [embL_toNode, capL_toNode, capLabel_embN, capLabel_capN]
        exact (hfl ℓ (flowerOf_spec hf).2).symm

/-- **Lemma 2.1(3)**: the decoration bijection. Capped decorations with original roots `nr` and cap roots `n'`
correspond to flower decorations with roots `nr` and flowers `n'` (by restriction; the inverse extends by `n'`). -/
def capDecEquiv (G : Garden w) (hF : OneFlower G) (d : ℕ) (nr : Fin w → (Fin d → ℤ)) (n' m : Fin d → ℤ) :
    GenDecoration (capGarden G) d (capRoots nr n') m ≃ GenDecoration G d nr n' where
  toFun κ := ⟨fun a => κ.1 (embN G a), isDecoration_restrict G κ.1 κ.2.1,
    fun j => by
      have := κ.2.2.1 (capσ w (.inl j))
      rw [← embN_root, capRoots_inl] at this
      exact this,
    fun ℓ hℓ => by
      have h1 := κ.2.1.2 (embL G ℓ)
      rw [capGarden_pair_flower G hF hℓ, embL_toNode, capL_toNode] at h1
      have h2 := κ.2.2.1 (capσ w (.inr ℓ.1.1))
      rw [← capN_eq_root, capRoots_inr] at h2
      exact h1.trans h2⟩
  invFun κ := ⟨capLabel G κ.1 n', isDecoration_capLabel G κ.1 n' κ.2.1 κ.2.2.2,
    fun c => by
      obtain ⟨s, rfl⟩ := (capσ w).surjective c
      rcases s with j | j
      · rw [← embN_root, capLabel_embN, capRoots_inl]
        exact κ.2.2.1 j
      · rw [← capN_eq_root, capLabel_capN, capRoots_inr],
    fun x hx => absurd hx (capGarden_not_isFlower G hF x)⟩
  left_inv κ := by
    apply Subtype.ext
    funext x
    rcases node_cases G x with ⟨a, rfl⟩ | ⟨j, rfl⟩
    · simp only [capLabel_embN]
    · simp only [capLabel_capN]
      have := κ.2.2.1 (capσ w (.inr j))
      rw [← capN_eq_root, capRoots_inr] at this
      exact this.symm
  right_inv κ := by
    apply Subtype.ext
    funext a
    simp only [capLabel_embN]

@[simp] theorem capDecEquiv_apply (G : Garden w) (hF : OneFlower G) (nr : Fin w → (Fin d → ℤ))
    (n' m : Fin d → ℤ) (κ : GenDecoration (capGarden G) d (capRoots nr n') m) :
    (capDecEquiv G hF d nr n' m κ).1 = fun a => κ.1 (embN G a) := rfl

@[simp] theorem capDecEquiv_symm_apply (G : Garden w) (hF : OneFlower G) (nr : Fin w → (Fin d → ℤ))
    (n' m : Fin d → ℤ) (κ : GenDecoration G d nr n') :
    ((capDecEquiv G hF d nr n' m).symm κ).1 = capLabel G κ.1 n' := rfl

end WaveTurbulence.Flower.CapsId
