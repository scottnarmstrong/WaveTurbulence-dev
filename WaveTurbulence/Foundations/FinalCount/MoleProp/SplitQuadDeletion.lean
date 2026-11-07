/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp.SplitQuadEquations
public import WaveTurbulence.Foundations.FinalCount.MoleProp.FiniteImages
import Mathlib.Tactic

/-! # Actual four-label deletion from a mixed old cut

The old cut fixes both integer differences. Its energy equation and the
actual atom energy equation give the two inflated windows. Large gaps
come from the actual opposite incident darts of one source decoration.
-/

@[expose] public section
set_option autoImplicit false
open Finset
namespace WaveTurbulence.MoleProp

theorem split_quad_deletion_bound (d : ℕ) (hdim : 3 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1-γ)/2) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ L ≥ R, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
    ∀ {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D],
    ∀ (M : Molecule V D) (v : V), v ∈ M.atoms →
    ∀ x y r s : D, x ≠ y → x ≠ r → y ≠ r → s ∉ ({x,y,r} : Finset D) →
      M.dartsAt v = {x,y,r,s} →
      M.out x = false → M.out y = true → M.out r = false → M.out s = true →
    ∀ U : Finset V, U ⊆ M.atoms →
      Degen.boundaryDarts M U = {M.mate x,M.mate y} →
    ∀ Adm : (D → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → LargeGap M L γ η (0 : Mom d) κ) →
      countEFree M L γ δ (0 : Mom d) Adm ≤
        (⌈C*((U.card : ℝ)+1)^2*(δ⁻¹)^2*L^(2*((d : ℝ)-γ-η))⌉₊ : ℕ∞) *
          countEFree (Degen.eraseAtoms M {v}) L γ δ (0 : Mom d)
            (erasedFreeAdmissibility M {v} Adm) := by
  classical
  obtain ⟨C,R,hC,hB⟩ := split_quad_local_count_bound d hdim γ hγ η hη hηmax
  refine ⟨C,max R 1,hC,?_⟩
  intro L hL δ hδ V D _ _ _ M v hv x y r s hxy hxr hyr hs hstar hxo hyo hro hso U hU hcut Adm hAdm
  have hLR : R ≤ L := (le_max_left R 1).trans hL
  have hLp : 0 < L := zero_lt_one.trans_le ((le_max_right R 1).trans hL)
  have hτ : 0 ≤ δ⁻¹*L^(-2*γ) := mul_nonneg (inv_nonneg.mpr hδ.1.le) (Real.rpow_nonneg hLp.le _)
  let e : Fin 4 → D := ![x,y,r,s]
  have hcover : ∀ z : DeletedDart M {v}, ∃ i, z.val = e i ∨ z.val = M.mate (e i) := by
    intro z
    have hz : M.atom z.val = v ∨ M.atom (M.mate z.val) = v := by
      simpa only [mem_singleton,not_and_or,not_not] using z.property
    rcases hz with hz | hz
    · have hm : z.val ∈ M.dartsAt v := (Mole.mem_dartsAt M v z.val).mpr hz
      rw [hstar] at hm
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with h | h | h | h
      · exact ⟨0,Or.inl h⟩
      · exact ⟨1,Or.inl h⟩
      · exact ⟨2,Or.inl h⟩
      · exact ⟨3,Or.inl h⟩
    · have hm : M.mate z.val ∈ M.dartsAt v := (Mole.mem_dartsAt M v (M.mate z.val)).mpr hz
      rw [hstar] at hm
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with h | h | h | h
      · exact ⟨0,Or.inr ((M.mate_mate z.val).symm.trans (congrArg M.mate h))⟩
      · exact ⟨1,Or.inr ((M.mate_mate z.val).symm.trans (congrArg M.mate h))⟩
      · exact ⟨2,Or.inr ((M.mate_mate z.val).symm.trans (congrArg M.mate h))⟩
      · exact ⟨3,Or.inr ((M.mate_mate z.val).symm.trans (congrArg M.mate h))⟩
  have hax : M.atom x = v := (Mole.mem_dartsAt M v x).mp (by rw [hstar]; simp)
  have hay : M.atom y = v := (Mole.mem_dartsAt M v y).mp (by rw [hstar]; simp)
  have har : M.atom r = v := (Mole.mem_dartsAt M v r).mp (by rw [hstar]; simp)
  have has : M.atom s = v := (Mole.mem_dartsAt M v s).mp (by rw [hstar]; simp)
  conv_lhs => unfold countEFree
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  let A := {κ | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
  have hf : A.Finite := (Mole.finite_restricted M hLp γ δ (0 : Mom d) β k0).subset (fun _ h => h.2.1)
  let F := hf.toFinset
  have hmem (κ) : κ ∈ F ↔ κ ∈ A := hf.mem_toFinset
  by_cases hne : A.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hne
    let q1 := κ0 x-κ0 y
    let q2 := κ0 r-κ0 s
    have hg1 : L^(-γ+η) ≤ ‖latticePoint L q1‖ := by
      have hg := hAdm κ0 hκ0.2.2 x y (hax.trans hay.symm) (by rw [hxo,hyo]; decide)
      simpa only [q1,WeylSums.latticePoint_sub_eq,Molecule.kvec,zero_add] using hg
    have hg2 : L^(-γ+η) ≤ ‖latticePoint L q2‖ := by
      have hg := hAdm κ0 hκ0.2.2 r s (har.trans has.symm) (by rw [hro,hso]; decide)
      simpa only [q2,WeylSums.latticePoint_sub_eq,Molecule.kvec,zero_add] using hg
    let centers : Fin 4 → Mom d := ![k0 x,k0 y,k0 r,k0 s]
    let Q := F.image (localLabels M e)
    have hQS : ∀ k ∈ Q, SplitQuadSource L q1 q2 (∑ a ∈ U, β a)
        (-β v-∑ a ∈ U, β a) (((U.card : ℝ)+1)*(δ⁻¹*L^(-2*γ))) centers k := by
      intro k hk
      obtain ⟨κ,hκ,rfl⟩ := mem_image.mp hk
      have hκA := (hmem κ).mp hκ
      have hm := split_quad_integer_momentum_eq M hLp.ne' hv hxy hxr hyr hs hstar hxo hyo hro hso U hU hcut hκA.1 hκ0.1
      have he := split_quad_energy M hτ hv hxy hxr hyr hs hstar hxo hyo hro hso U hU hcut hκA.1 hκA.2.1
      refine ⟨hm.1,hm.2,?_,he⟩
      intro i
      fin_cases i
      · change ‖latticePoint L (κ x)-k0 x‖ ≤ 1
        simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 x
      · change ‖latticePoint L (κ y)-k0 y‖ ≤ 1
        simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 y
      · change ‖latticePoint L (κ r)-k0 r‖ ≤ 1
        simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 r
      · change ‖latticePoint L (κ s)-k0 s‖ ≤ 1
        simpa only [Molecule.kvec,zero_add] using hκA.2.1.2 s
    have hQB := hB L hLR δ hδ ((U.card : ℝ)+1) (by have hn : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _; linarith only [hn]) q1 q2
      (∑ a ∈ U, β a) (-β v-∑ a ∈ U, β a) centers hg1 hg2 Q hQS
    have hlocal := card_deletedLabels_image_le_localLabels_image M {v} e hcover F
      (fun κ hκ => ((hmem κ).mp hκ).1.1)
    have hImage : (deletedLabels M {v} '' A).ncard = (F.image (deletedLabels M {v})).card := by
      have he : deletedLabels M {v} '' A = (F.image (deletedLabels M {v}) : Set _) := by
        rw [Finset.coe_image,hf.coe_toFinset]
      rw [he,Set.ncard_coe_finset]
    have hreal : ((deletedLabels M {v} '' A).ncard : ℝ) ≤ C*((U.card : ℝ)+1)^2*(δ⁻¹)^2*L^(2*((d : ℝ)-γ-η)) := by
      rw [hImage]
      have hh : ((F.image (deletedLabels M {v})).card : ℝ) ≤ Q.card := by exact_mod_cast hlocal
      exact hh.trans hQB
    have hnat : (deletedLabels M {v} '' A).ncard ≤ ⌈C*((U.card : ℝ)+1)^2*(δ⁻¹)^2*L^(2*((d : ℝ)-γ-η))⌉₊ := by
      exact_mod_cast hreal.trans (Nat.le_ceil _)
    have hEN : ((deletedLabels M {v} '' A).ncard : ℕ∞) ≤ (⌈C*((U.card : ℝ)+1)^2*(δ⁻¹)^2*L^(2*((d : ℝ)-γ-η))⌉₊ : ℕ∞) := by exact_mod_cast hnat
    exact (encard_le_deletedImage_mul_post M {v} hLp γ δ (0 : Mom d) Adm c β k0 hk0).trans
      (mul_le_mul_of_nonneg_right hEN bot_le)
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change A.encard ≤ _
    rw [he,Set.encard_empty]
    exact bot_le

end WaveTurbulence.MoleProp
