/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.OpD
import Mathlib.Tactic

/-! # Operation (d) at the level of decorations (finalcount-g8, F6-1)

`OpDAt` fixes the post admissibility to `lgAdmOff post`, so it cannot carry a condition `W` on the pulled-back
decoration. This is the decoration-level version, following MOLEPROP4-T `TwoExit.countEFree_le_adm`: the post
decorations are restricted to the images (`postAdmOff`) of `Adm`-decorations that satisfy `W g` under the transport with
multiplier `g`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **Goodness of the multiplier `g`**: large gaps of the post decoration off `Bs \ Y`. -/
def PostGoodOff {d : ℕ} (Bs : Finset V) (L γ η' : ℝ) (κ : D → (Fin d → ℤ)) (g : ℤ) : Prop :=
  ∀ z₁ z₂ : Degen.RetainedDart N T.Y ⊕ Bool, T.post.atom z₁ = T.post.atom z₂ → T.post.atom z₁ ∉ Bs \ T.Y →
    T.post.out z₁ ≠ T.post.out z₂ →
    L ^ (-γ + η') ≤ ‖Molecule.kvec L (0 : Mom d) (T.postLabels κ g) z₁ - Molecule.kvec L (0 : Mom d) (T.postLabels κ g) z₂‖

/-- **The transported admissibility** (chain version): the post decorations with LG off `Bs \ Y` and cell scales `P'`
that are images of `Adm`-decorations satisfying `W g`. -/
def postAdmOff {d : ℕ} (Bs : Finset V) (Adm : (D → (Fin d → ℤ)) → Prop) (W : ℤ → (D → (Fin d → ℤ)) → Prop)
    (L γ η' : ℝ) (P' : Finset V → ℝ) (g : ℤ) (κ' : Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) : Prop :=
  lgAdmOff T.post (Bs \ T.Y) L γ η' P' κ' ∧
    ∃ κ, Adm κ ∧ (∀ x, κ (N.mate x) = κ x) ∧ W g κ ∧ T.postLabels κ g = κ'

/-- Existence of a good multiplier (from `exists_post_largeGap_off`). -/
theorem exists_postGoodOff {d : ℕ} {L γ η : ℝ} (hL : 1 ≤ L) (hL11 : 11 ≤ L ^ (η / 2)) {κ : D → (Fin d → ℤ)}
    (hb : ∀ z, κ (N.mate z) = κ z) (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2) (Bs : Finset V)
    (hcB : T.c ∉ Bs) (hdB : T.d ∉ Bs)
    (hLG : ∀ x y : D, N.atom x = N.atom y → N.atom x ∉ Bs → N.out x ≠ N.out y →
      L ^ (-γ + η) ≤ ‖Molecule.kvec L (0 : Mom d) κ x - Molecule.kvec L (0 : Mom d) κ y‖) :
    ∃ g ∈ Icc (0 : ℤ) 4, T.PostGoodOff Bs L γ (η / 2) κ g :=
  T.exists_post_largeGap_off hL hL11 hb hcap Bs hcB hdB hLG

/-- **The counting inequality of a two-exit (Y2) removal.** -/
theorem countEFree_le_chainW (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hch : ∀ b ∈ T.Y, N.outdeg b = 1 ∧ N.indeg b = 1) (hconnY : ∀ a ∈ T.Y, ∀ b ∈ T.Y, (piece N T.Y).SameComponent a b)
    (Bs : Finset V)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) {d : ℕ} {L γ δ η : ℝ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (P : Finset V → ℝ)
    (Adm : (D → (Fin d → ℤ)) → Prop) (hAdm : ∀ κ, Adm κ → lgAdmOff N Bs L γ η P κ)
    (W : ℤ → (D → (Fin d → ℤ)) → Prop)
    (hW : ∀ κ, Adm κ → (∀ x, κ (N.mate x) = κ x) → ∃ g ∈ Icc (0 : ℤ) 4, T.PostGoodOff Bs L γ (η / 2) κ g ∧ W g κ) :
    MoleProp.countEFree N L γ δ (0 : Mom d) Adm ≤
      (5 * T.windowK ^ 2 * (T.scaleFamily L P).card : ℕ∞) *
        ⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ T.scaleFamily L P,
          MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g) := by
  classical
  have hLp : 0 < L := by linarith
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτdef
  have hτ : 0 < τ := by positivity
  set K := T.windowK
  have hK : 1 ≤ K := by unfold K windowK; omega
  set G := ⨆ g ∈ Icc (0 : ℤ) 4, ⨆ P' ∈ T.scaleFamily L P,
    MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g)
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ Adm κ}
  have hAfin : A.Finite := (Mole.finite_restricted N hLp γ δ 0 β k0).subset fun _ h => h.2.1
  let Ag : ℤ → Set (D → (Fin d → ℤ)) := fun g =>
    {κ | κ ∈ A ∧ T.PostGoodOff Bs L γ (η / 2) κ g ∧ W g κ}
  -- every decoration has a good multiplier
  have hcover : A ⊆ ⋃ g ∈ Icc (0 : ℤ) 4, Ag g := by
    intro κ hκ
    obtain ⟨g, hg, hLG, hWg⟩ := hW κ hκ.2.2 hκ.1.1
    exact Set.mem_biUnion hg ⟨hκ, hLG, hWg⟩
  -- the post problems
  let E : (ℕ × ℕ) × (Finset V → ℝ) → ℤ → Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) :=
    fun t g => {κ' | T.post.IsDecoration L 0 (T.postCharges c g) κ' ∧
      T.post.IsRestricted L γ δ 0 (T.postEnergy β c g τ t.1.1 t.1.2) (T.postCenters k0 c g) κ' ∧
      T.postAdmOff Bs Adm W L γ (η / 2) t.2 g κ'}
  let idx : Finset ((ℕ × ℕ) × (Finset V → ℝ)) := (range K ×ˢ range K) ×ˢ T.scaleFamily L P
  have hk0' : ∀ g (z : Degen.RetainedDart N T.Y ⊕ Bool),
      T.postCenters k0 c g (T.post.mate z) = T.postCenters k0 c g z := by
    intro g z; rcases z with z | t
    · exact hk0 z.val
    · rfl
  have hE : ∀ g ∈ Icc (0 : ℤ) 4, ∀ t ∈ idx, (E t g).encard ≤ G := by
    intro g hg t ht
    refine (MoleProp.encard_le_countEFree T.post L γ δ 0 _ (T.postCharges c g)
      (T.postEnergy β c g τ t.1.1 t.1.2) (T.postCenters k0 c g) (hk0' g)).trans ?_
    refine le_iSup₂_of_le (f := fun g' (_ : g' ∈ Icc (0 : ℤ) 4) => ⨆ P' ∈ T.scaleFamily L P,
      MoleProp.countEFree T.post L γ δ (0 : Mom d) (T.postAdmOff Bs Adm W L γ (η / 2) P' g')) g hg ?_
    exact le_iSup₂_of_le (f := fun P' _ => MoleProp.countEFree T.post L γ δ (0 : Mom d)
      (T.postAdmOff Bs Adm W L γ (η / 2) P' g)) t.2 (mem_product.mp ht).2 le_rfl
  have hidx : (idx.card : ℕ∞) = K * K * (T.scaleFamily L P).card := by
    simp only [idx, card_product, card_range]; push_cast; ring
  -- the bound for one multiplier
  have hg_bound : ∀ g ∈ Icc (0 : ℤ) 4, (Ag g).encard ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G := by
    intro g hg
    have hAgfin : (Ag g).Finite := hAfin.subset fun _ h => h.1
    let B : Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) := ⋃ t ∈ idx, E t g
    have hmaps : ∀ κ ∈ Ag g, T.postLabels κ g ∈ B := by
      intro κ hκ
      obtain ⟨⟨hdec, hres, hadm⟩, hLG, hWg⟩ := hκ
      obtain ⟨jc, hjc, hwc⟩ := exists_window hτ hK (T.gamma_c_window hdec hres hg)
      obtain ⟨jd, hjd, hwd⟩ := exists_window hτ hK (T.gamma_d_window hdec hres hg)
      obtain ⟨P', hP', hcgr⟩ := T.exists_scaleFamily_cgr hloop hdeg hopen hL hdec.1 (hAdm κ hadm).2 g
      refine Set.mem_biUnion (x := ((jc, jd), P')) (mem_product.mpr ⟨mem_product.mpr ⟨hjc, hjd⟩, hP'⟩) ?_
      refine ⟨T.post_isDecoration hdec g, ⟨?_, ?_⟩, ⟨hLG, hcgr⟩, κ, hadm, hdec.1, hWg, rfl⟩
      · intro v hv
        rw [T.post_atoms] at hv
        obtain ⟨hvN, hvY⟩ := mem_sdiff.mp hv
        unfold postEnergy
        by_cases hc : v = T.c
        · subst hc; simpa only [ite_true] using hwc
        · by_cases hd : v = T.d
          · subst hd; simpa only [hc, ite_false, ite_true] using hwd
          · simp only [hc, hd, ite_false]
            rw [T.post_gamma L 0 hdec.1 g hvY]
            simp only [hc, hd, ite_false, add_zero]
            exact hres.1 v hvN
      · rintro (z | t)
        · exact hres.2 z.val
        · change ‖Molecule.kvec L 0 (T.postLabels κ g) (Sum.inr t) - (k0 T.y + (g : ℝ) • T.exitCharge c)‖ ≤ 1
          rw [T.kvec_postLabels_new, T.kvec_x_sub_y hdec]
          have : Molecule.kvec L 0 κ T.y + (g : ℝ) • T.exitCharge c - (k0 T.y + (g : ℝ) • T.exitCharge c) =
              Molecule.kvec L 0 κ T.y - k0 T.y := by abel
          rw [this]; exact hres.2 T.y
    have hfib : ∀ κ' ∈ B, {κ | κ ∈ Ag g ∧ T.postLabels κ g = κ'}.encard ≤ 1 := by
      intro κ' _
      refine Set.encard_le_one_iff.mpr fun κ₁ κ₂ h₁ h₂ => ?_
      obtain ⟨⟨hA1, _⟩, hp1⟩ := h₁
      obtain ⟨⟨hA2, _⟩, hp2⟩ := h₂
      obtain ⟨hdec, hres, hadm⟩ := hA1
      obtain ⟨hdec₀, _, _⟩ := hA2
      have hpost : T.postLabels κ₁ g = T.postLabels κ₂ g := hp1.trans hp2.symm
      have hdiff : κ₁ T.x - κ₁ T.y = κ₂ T.x - κ₂ T.y := by
        apply latticePoint_injective hLp.ne'
        have h1 := T.kvec_x_sub_y hdec
        have h2 := T.kvec_x_sub_y hdec₀
        simp only [Molecule.kvec, zero_add] at h1 h2
        rw [latticePoint_sub', latticePoint_sub', h1, h2]
      have hnew := congrFun hpost (Sum.inr true)
      simp only [postLabels, Sum.elim_inr] at hnew
      rw [hdiff] at hnew
      have hy : κ₁ T.y = κ₂ T.y := add_right_cancel hnew
      have hx : κ₁ T.x = κ₂ T.x := by
        have := hdiff; rw [hy] at this; exact sub_left_injective this
      have hag := FinalCountG8.chain_agree N T.sub hch hconnY hLp.ne' hdec hdec₀ (z0 := T.x) T.atom_x hx
      funext z
      by_cases h1 : N.atom z ∈ T.Y
      · exact hag z h1
      · by_cases h2 : N.atom (N.mate z) ∈ T.Y
        · have := hag (N.mate z) h2
          rwa [hdec.1, hdec₀.1] at this
        · exact congrFun hpost (Sum.inl ⟨z, h1, h2⟩)
    have hB : B.encard ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G := by
      refine (encard_biUnion_le idx fun t => E t g).trans ?_
      calc ∑ t ∈ idx, (E t g).encard ≤ ∑ _t ∈ idx, G := sum_le_sum fun t ht => hE g hg t ht
        _ = (idx.card : ℕ∞) * G := by rw [sum_const, nsmul_eq_mul]
        _ = _ := by rw [hidx]
    calc (Ag g).encard ≤ B.encard * 1 := encard_le_mul_of_fiber hAgfin (fun κ => T.postLabels κ g) B hmaps 1 hfib
      _ ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G := by rw [mul_one]; exact hB
  calc A.encard ≤ (⋃ g ∈ Icc (0 : ℤ) 4, Ag g).encard := Set.encard_mono hcover
    _ ≤ ∑ g ∈ Icc (0 : ℤ) 4, (Ag g).encard := encard_biUnion_le _ _
    _ ≤ ∑ _g ∈ Icc (0 : ℤ) 4, (K * K * (T.scaleFamily L P).card : ℕ∞) * G := sum_le_sum hg_bound
    _ = 5 * ((K * K * (T.scaleFamily L P).card : ℕ∞) * G) := by
        rw [sum_const, nsmul_eq_mul]; rfl
    _ = (5 * K ^ 2 * (T.scaleFamily L P).card : ℕ∞) * G := by ring


end TwoExit
end WaveTurbulence.MoleProp4
