/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitScaleFamily
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitWindows
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitLG
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Fibers
public import WaveTurbulence.Foundations.FinalCount.MoleProp.DeletionFibers
import Mathlib.Tactic

/-! # Counting through the (Y2) post molecule (DH23 L1954)

"Once a decoration of `𝕄′` is fixed, then `k_{ℓ₁}` and `k_{ℓ₂}` are also fixed, and we can go from bottom to top".
For every decoration of `N` (LG with parameter `η`, cell gaps `P`), some `g ∈ {0,…,4}` gives a transported
decoration of the post molecule which is LG with `η/2`, restricted for one of `K²` energy parameters (`K = 1 + 4|Y|`),
and satisfies the cell-gap restriction for one of the scale functions of `scaleFamily`. Given the transported
decoration, the labels outside `Y` and the exits are fixed, so the remaining labels are counted by the piece `N[Y]`.

`countEFree N ≤ 5 K² |scaleFamily| · countEFree N[Y] · sup_{P'} countEFree post`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

theorem encard_biUnion_le {α ι : Type*} (s : Finset ι) (f : ι → Set α) :
    (⋃ i ∈ s, f i).encard ≤ ∑ i ∈ s, (f i).encard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (Set.encard_union_le _ _).trans (add_le_add le_rfl ih)

theorem latticePoint_injective {d : ℕ} {L : ℝ} (hL : L ≠ 0) : Function.Injective (latticePoint (d := d) L) := by
  intro m n h
  funext i
  have := congrArg (fun v : Mom d => v i) h
  simp only [latticePoint] at this
  have h2 : (m i : ℝ) = n i := by
    have := this
    field_simp at this
    exact this
  exact_mod_cast h2

/-- The large-gap and cell-gap admissibility of DH23 L1829–L1831. -/
def lgAdm (M : Molecule V D) {d : ℕ} (L γ η : ℝ) (P : Finset V → ℝ) (κ : D → (Fin d → ℤ)) : Prop :=
  MoleProp.LargeGap M L γ η 0 κ ∧ MoleProp.CellGapRestriction M L 0 P (MoleProp.GapScale L) κ

namespace TwoExit
variable {N : Molecule V D} (T : TwoExit N)

/-- **The counting inequality of a two-exit (Y2) removal.** -/
theorem countEFree_le (hcap : ∀ v ∈ N.atoms, N.outdeg v ≤ 2 ∧ N.indeg v ≤ 2)
    (hloop : ∀ z, N.atom z ≠ N.atom (N.mate z)) (hdeg : ∀ a ∈ N.atoms, N.deg a ≤ 4)
    (hopen : ∀ S ∈ MoleProp.ladderCells T.post, T.c ∈ S → GoodCell T.post S) {d : ℕ} {L γ δ η : ℝ}
    (hL : 1 ≤ L) (hL11 : 11 ≤ L ^ (η / 2)) (hδ : 0 < δ) (P : Finset V → ℝ) :
    MoleProp.countEFree N L γ δ (0 : Mom d) (lgAdm N L γ η P) ≤
      (5 * T.windowK ^ 2 * (T.scaleFamily L P).card : ℕ∞) *
        MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d)
          (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) (lgAdm (d := d) N L γ η P)) *
        ⨆ P' ∈ T.scaleFamily L P, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ (η / 2) P') := by
  classical
  have hLp : 0 < L := by linarith
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτdef
  have hτ : 0 < τ := by positivity
  set K := T.windowK
  have hK : 1 ≤ K := by unfold K windowK; omega
  set F := MoleProp.countEFree (piece N T.Y) L γ δ (0 : Mom d)
    (MoleProp.erasedFreeAdmissibility N (N.atoms \ T.Y) (lgAdm (d := d) N L γ η P)) with hFdef
  set G := ⨆ P' ∈ T.scaleFamily L P, MoleProp.countEFree T.post L γ δ (0 : Mom d) (lgAdm T.post L γ (η / 2) P')
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | N.IsDecoration L 0 c κ ∧ N.IsRestricted L γ δ 0 β k0 κ ∧ lgAdm N L γ η P κ}
  have hAfin : A.Finite := (Mole.finite_restricted N hLp γ δ 0 β k0).subset fun _ h => h.2.1
  let Ag : ℤ → Set (D → (Fin d → ℤ)) := fun g =>
    {κ | κ ∈ A ∧ MoleProp.LargeGap T.post L γ (η / 2) 0 (T.postLabels κ g)}
  -- every decoration has a good multiplier
  have hcover : A ⊆ ⋃ g ∈ Icc (0 : ℤ) 4, Ag g := by
    intro κ hκ
    obtain ⟨g, hg, hLG⟩ := T.exists_post_largeGap hL hL11 hκ.1.1 hcap hκ.2.2.1
    exact Set.mem_biUnion hg ⟨hκ, hLG⟩
  -- the post problems
  let E : (ℕ × ℕ) × (Finset V → ℝ) → ℤ → Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) :=
    fun t g => {κ' | T.post.IsDecoration L 0 (T.postCharges c g) κ' ∧
      T.post.IsRestricted L γ δ 0 (T.postEnergy β c g τ t.1.1 t.1.2) (T.postCenters k0 c g) κ' ∧
      lgAdm T.post L γ (η / 2) t.2 κ'}
  let idx : Finset ((ℕ × ℕ) × (Finset V → ℝ)) := (range K ×ˢ range K) ×ˢ T.scaleFamily L P
  have hk0' : ∀ g (z : Degen.RetainedDart N T.Y ⊕ Bool),
      T.postCenters k0 c g (T.post.mate z) = T.postCenters k0 c g z := by
    intro g z; rcases z with z | t
    · exact hk0 z.val
    · rfl
  have hE : ∀ g, ∀ t ∈ idx, (E t g).encard ≤ G := by
    intro g t ht
    refine (MoleProp.encard_le_countEFree T.post L γ δ 0 _ (T.postCharges c g)
      (T.postEnergy β c g τ t.1.1 t.1.2) (T.postCenters k0 c g) (hk0' g)).trans ?_
    exact le_iSup₂_of_le (f := fun P' _ => MoleProp.countEFree T.post L γ δ (0 : Mom d)
      (lgAdm T.post L γ (η / 2) P')) t.2 (mem_product.mp ht).2 le_rfl
  have hidx : (idx.card : ℕ∞) = K * K * (T.scaleFamily L P).card := by
    simp only [idx, card_product, card_range]; push_cast; ring
  -- the bound for one multiplier
  have hg_bound : ∀ g ∈ Icc (0 : ℤ) 4, (Ag g).encard ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G * F := by
    intro g hg
    have hAgfin : (Ag g).Finite := hAfin.subset fun _ h => h.1
    let B : Set (Degen.RetainedDart N T.Y ⊕ Bool → (Fin d → ℤ)) := ⋃ t ∈ idx, E t g
    have hmaps : ∀ κ ∈ Ag g, T.postLabels κ g ∈ B := by
      intro κ hκ
      obtain ⟨⟨hdec, hres, hadm⟩, hLG⟩ := hκ
      obtain ⟨jc, hjc, hwc⟩ := exists_window hτ hK (T.gamma_c_window hdec hres hg)
      obtain ⟨jd, hjd, hwd⟩ := exists_window hτ hK (T.gamma_d_window hdec hres hg)
      obtain ⟨P', hP', hcgr⟩ := T.exists_scaleFamily_cgr hloop hdeg hopen hL hdec.1 hadm.2 g
      refine Set.mem_biUnion (x := ((jc, jd), P')) (mem_product.mpr ⟨mem_product.mpr ⟨hjc, hjd⟩, hP'⟩) ?_
      refine ⟨T.post_isDecoration hdec g, ⟨?_, ?_⟩, hLG, hcgr⟩
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
    have hfib : ∀ κ' ∈ B, {κ | κ ∈ Ag g ∧ T.postLabels κ g = κ'}.encard ≤ F := by
      intro κ' _
      by_cases hne : {κ | κ ∈ Ag g ∧ T.postLabels κ g = κ'}.Nonempty
      · obtain ⟨κ₀, ⟨hκ₀, hκ₀'⟩⟩ := hne
        refine (Set.encard_mono ?_).trans (MoleProp.fixed_deleted_fiber_encard_le N (N.atoms \ T.Y) L γ δ 0
          (lgAdm N L γ η P) c β k0 hk0 (MoleProp.deletedLabels N (N.atoms \ T.Y) κ₀))
        rintro κ ⟨⟨⟨hdec, hres, hadm⟩, _⟩, hκ'⟩
        refine ⟨hdec, hres, hadm, ?_⟩
        have hpost : T.postLabels κ g = T.postLabels κ₀ g := hκ'.trans hκ₀'.symm
        have hdec₀ := hκ₀.1.1
        -- the exits agree
        have hdiff : κ T.x - κ T.y = κ₀ T.x - κ₀ T.y := by
          apply latticePoint_injective hLp.ne'
          have h1 := T.kvec_x_sub_y hdec
          have h2 := T.kvec_x_sub_y hdec₀
          simp only [Molecule.kvec, zero_add] at h1 h2
          rw [latticePoint_sub', latticePoint_sub', h1, h2]
        have hnew := congrFun hpost (Sum.inr true)
        simp only [postLabels, Sum.elim_inr] at hnew
        rw [hdiff] at hnew
        have hy : κ T.y = κ₀ T.y := add_right_cancel hnew
        have hx : κ T.x = κ₀ T.x := by
          have := hdiff; rw [hy] at this; exact sub_left_injective this
        funext ⟨z, hz⟩
        simp only [MoleProp.deletedLabels]
        rcases T.dart_cases z with h | h | rfl | rfl | rfl | rfl
        · exfalso; apply hz
          exact ⟨fun h' => (mem_sdiff.mp h').2 h.1, fun h' => (mem_sdiff.mp h').2 h.2⟩
        · exact congrFun hpost (Sum.inl ⟨z, h.1, h.2⟩)
        · exact hx
        · exact hy
        · rw [hdec.1, hdec₀.1]; exact hx
        · rw [hdec.1, hdec₀.1]; exact hy
      · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.encard_empty]; exact bot_le
    have hB : B.encard ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G := by
      refine (encard_biUnion_le idx fun t => E t g).trans ?_
      calc ∑ t ∈ idx, (E t g).encard ≤ ∑ _t ∈ idx, G := sum_le_sum fun t ht => hE g t ht
        _ = (idx.card : ℕ∞) * G := by rw [sum_const, nsmul_eq_mul]
        _ = _ := by rw [hidx]
    calc (Ag g).encard ≤ B.encard * F := encard_le_mul_of_fiber hAgfin (fun κ => T.postLabels κ g) B hmaps F hfib
      _ ≤ (K * K * (T.scaleFamily L P).card : ℕ∞) * G * F := mul_le_mul_left hB F
  calc A.encard ≤ (⋃ g ∈ Icc (0 : ℤ) 4, Ag g).encard := Set.encard_mono hcover
    _ ≤ ∑ g ∈ Icc (0 : ℤ) 4, (Ag g).encard := encard_biUnion_le _ _
    _ ≤ ∑ _g ∈ Icc (0 : ℤ) 4, (K * K * (T.scaleFamily L P).card : ℕ∞) * G * F := sum_le_sum hg_bound
    _ = 5 * ((K * K * (T.scaleFamily L P).card : ℕ∞) * G * F) := by
        rw [sum_const, nsmul_eq_mul]; rfl
    _ = (5 * K ^ 2 * (T.scaleFamily L P).card : ℕ∞) * F * G := by ring

end TwoExit
end WaveTurbulence.MoleProp4
