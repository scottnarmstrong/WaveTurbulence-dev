/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.G8R.CoreCaseI
import Mathlib.Tactic

/-! # Core cases III and IV: a double bond away from `ℓ`

DH23 L1975–L1977. A double bond `v₁ = v₂` with `v₁, v₂` not at the ends of `ℓ`. The decorations split by the small-gap
condition `SmallPairGap` across the pair:
* (III) small gap: the first alternative — remove `v₁, v₂` (`Δχ = −4`, deviation `L^{−γ₀+dη}`), Prop 10.1 on the rest;
* (IV) no small gap: merge `v₁, v₂` (deviation `L^{−η/2}`) and use the split of the merged molecule for the same `ℓ`
  (induction). The merged decoration is LG; `merge (𝕄 ∖ ℓ) ≅ (merge 𝕄) ∖ ℓ`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
universe u v

/-- G6's Prop 10.1 at a fixed `L`. -/
def Prop101At (d : ℕ) (L γ δ η C1 : ℝ) : Prop :=
  1 ≤ Real.log L → ∀ {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D),
    M.IsMolecule → ∀ (Adm : (D → (Fin d → ℤ)) → Prop) (P : Finset V → ℝ),
      (∀ κ, Adm κ → MoleProp.LargeGap M L γ η (0 : Mom d) κ) →
      (∀ κ, Adm κ → MoleProp.CellGapRestriction M L (0 : Mom d) P (MoleProp.GapScale L) κ) →
      (∀ S ∈ MoleProp.ladderCells M, 0 ≤ P S) → MoleProp.countAFree M L γ δ C1 (0 : Mom d) Adm P ≤ 1

theorem prop101At_of_G6 (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (η : ℝ) (hη : 0 < η)
    (hηmax : η ≤ min γ (1 - γ) / 2) :
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C1 ≥ Cstar, ∀ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ R : ℝ, ∀ L ≥ R,
      Prop101At.{u, v} d L γ δ η C1 := by
  obtain ⟨Cs, hCs, h⟩ := MoleProp.proposition_one_normalized_bound.{u, v} d hd γ hγ η hη hηmax
  refine ⟨Cs, hCs, fun C1 hC1 δ hδ => ?_⟩
  obtain ⟨R, hR⟩ := h C1 hC1 δ hδ
  exact ⟨R, fun L hL hlog V D _ _ _ M => hR L hL hlog M⟩

variable {V : Type u} {D : Type v} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- **Cases III/IV: a double bond away from `ℓ`**, given the split of the merged molecule. -/
theorem case_merge {d : ℕ} {L γ δ η C1 K₁ B₁ K₂ B₂ : ℝ} (hL : 0 < L) (hlog : 1 ≤ Real.log L)
    (hsg : SmallGapPairAt.{u, v} d L γ δ η C1 K₁ B₁) (hmg : MergeAt.{u, v} d L γ δ η C1 K₂ B₂)
    (h101 : Prop101At.{u, v} d L γ δ η C1) {M : Molecule V D} (hM : IsCore M) (e : D)
    (hnoII : ∀ S ⊆ M.atoms, ∀ a ∈ S, ∀ b ∈ M.atoms, b ∉ S → (crossDarts M S).card ≠ 2)
    {v₁ v₂ : V} (hv₁ : v₁ ∈ M.atoms) (hv₂ : v₂ ∈ M.atoms) (hne : v₁ ≠ v₂) (hbb : M.bondsBetween v₁ v₂ = 2)
    (hp1 : M.atom e ≠ v₁) (hp2 : M.atom e ≠ v₂) (hq1 : M.atom (M.mate e) ≠ v₁) (hq2 : M.atom (M.mate e) ≠ v₂)
    (he : M.ends e ≠ s(v₁, v₂)) {ε₁ ε₂ : ℝ} (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hε₁ : 0 ≤ ε₁)
    (hgood1 : ∀ S' ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), GoodCell (mergePair M v₁ v₂ hv₁ hne) S')
    (hgood2 : ∀ S' ∈ MoleProp.ladderCells (mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne),
      GoodCell (mergePair (MoleProp.eraseBond M e) v₁ v₂ hv₁ hne) S')
    (hIH : SplitBound (mergePair M v₁ v₂ hv₁ hne) ⟨e, he⟩ d L γ δ η C1 ε₁ ε₂) :
    SplitBound M e d L γ δ η C1
      (K₁ * Real.log L ^ B₁ * L ^ (-(min γ (1 - γ) - d * η)) + K₂ * Real.log L ^ B₂ * L ^ (-(η / 2)) * ε₁)
      (K₂ * Real.log L ^ B₂ * L ^ (-(η / 2)) * ε₂) := by
  classical
  obtain ⟨Q₂, hQ1, hQ2⟩ := hIH
  have hlogp : 0 < Real.log L := zero_lt_one.trans_le hlog
  have hc1 : 0 ≤ K₁ * Real.log L ^ B₁ * L ^ (-(min γ (1 - γ) - d * η)) :=
    mul_nonneg (mul_nonneg hK₁ (Real.rpow_nonneg hlogp.le _)) (Real.rpow_nonneg hL.le _)
  have hc2 : 0 ≤ K₂ * Real.log L ^ B₂ * L ^ (-(η / 2)) :=
    mul_nonneg (mul_nonneg hK₂ (Real.rpow_nonneg hlogp.le _)) (Real.rpow_nonneg hL.le _)
  -- the rest after removing the pair is connected and a molecule
  have hc4 : (crossDarts M {v₁, v₂}).card = 4 := by
    have h := card_cross_pair M hM.loop hne
    rw [hbb, hM.reg _ hv₁, hM.reg _ hv₂] at h
    omega
  have hRconn := erase_pair_connected hM hnoII hc4
  obtain ⟨x, hx⟩ : (crossDarts M {v₁, v₂}).Nonempty := card_pos.mp (by omega)
  obtain ⟨hx1, hx2⟩ := mem_crossDarts.mp hx
  have hzR : M.atom (M.mate x) ∈ (Degen.eraseAtoms M {v₁, v₂}).atoms := mem_sdiff.mpr ⟨M.atom_mem _, hx2⟩
  have hz3 : (Degen.eraseAtoms M {v₁, v₂}).deg (M.atom (M.mate x)) ≠ 4 := by
    have h := deg_eraseAtoms_add (N := M) {v₁, v₂} (v := M.atom (M.mate x)) hx2
    have hmem : M.mate x ∈ Degen.removedDartsAt M {v₁, v₂} (M.atom (M.mate x)) := by
      unfold Degen.removedDartsAt Molecule.dartsAt
      simp only [mem_filter, mem_univ, true_and]
      rw [M.mate_mate]; exact hx1
    have := card_pos.mpr ⟨_, hmem⟩
    have := hM.reg _ (M.atom_mem (M.mate x))
    omega
  have hmolR := isMolecule_of_connected _ (caps_eraseAtoms {v₁, v₂} hM.cap) hRconn hzR hz3
  have hAR : AFreeSup (Degen.eraseAtoms M {v₁, v₂}) d L γ δ η C1 ≤ 1 :=
    iSup₂_le fun P hP => h101 hlog _ hmolR _ P (fun κ h => h.1) (fun κ h => h.2) hP
  -- the split
  let mergeL : (D → (Fin d → ℤ)) → (OffPair M v₁ v₂ → (Fin d → ℤ)) := fun κ y => κ y.val
  refine ⟨fun κ => ¬ SmallPairGap M v₁ v₂ L γ η κ ∧ Q₂ (mergeL κ), fun P hP => ?_, fun P hP => ?_⟩
  · -- first alternative: small gap, or merge and the first alternative of the merged molecule
    have hsplit := (countAFree_mono_adm M (L := L) (γ := γ) (δ := δ) (C1 := C1) (A := fun κ => lgAdm M L γ η P κ ∧
        ¬ (¬ SmallPairGap M v₁ v₂ L γ η κ ∧ Q₂ (mergeL κ)))
      (B := fun κ => (lgAdm M L γ η P κ ∧ SmallPairGap M v₁ v₂ L γ η κ) ∨
        (lgAdm M L γ η P κ ∧ ¬ SmallPairGap M v₁ v₂ L γ η κ ∧ ¬ Q₂ (mergeL κ))) (P := P) (fun κ h => by
          by_cases hs : SmallPairGap M v₁ v₂ L γ η κ
          · exact Or.inl ⟨h.1, hs⟩
          · exact Or.inr ⟨h.1, hs, fun hq => h.2 ⟨hs, hq⟩⟩)).trans
        (countAFree_or_le M (L := L) (γ := γ) (δ := δ) (C1 := C1) _ _)
    have h1 := hsg M hM.cap hM.loop v₁ hv₁ v₂ hv₂ hne hbb (hM.reg _ hv₁) (hM.reg _ hv₂) hM.conn hRconn P hP
      (fun κ => lgAdm M L γ η P κ ∧ SmallPairGap M v₁ v₂ L γ η κ) (fun κ h => h)
    have h2 := hmg M hM.cap hM.loop v₁ v₂ hv₁ hv₂ hne hbb (hM.reg _ hv₁) (hM.reg _ hv₂) hM.conn hgood1 P hP
      (fun κ => lgAdm M L γ η P κ ∧ ¬ SmallPairGap M v₁ v₂ L γ η κ ∧ ¬ Q₂ (mergeL κ)) (fun κ h => ⟨h.1, h.2.1⟩)
    have hsup : AFreeSupAdm (mergePair M v₁ v₂ hv₁ hne) d L γ δ C1
        (fun P' κ' => lgAdm (mergePair M v₁ v₂ hv₁ hne) L γ η P' κ' ∧ mergeAdm M v₁ v₂
          (fun κ => lgAdm M L γ η P κ ∧ ¬ SmallPairGap M v₁ v₂ L γ η κ ∧ ¬ Q₂ (mergeL κ)) κ') ≤
        ENNReal.ofReal ε₁ := by
      refine iSup₂_le fun P' hP' => (countAFree_mono_adm _ fun κ' h => ⟨h.1, ?_⟩).trans (hQ1 P' hP')
      obtain ⟨κ, ⟨_, _, hnq⟩, _, hκ'⟩ := h.2
      have : κ' = mergeL κ := funext hκ'
      rw [this]; exact hnq
    refine hsplit.trans ((add_le_add (h1.trans (mul_le_mul' le_rfl hAR)) (h2.trans (mul_le_mul' le_rfl hsup))).trans ?_)
    rw [mul_one, ← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add hc1 (mul_nonneg hc2 hε₁)]
  · -- second alternative: merge `𝕄 ∖ ℓ` and use the second alternative of the merged molecule
    have hNbb : (MoleProp.eraseBond M e).bondsBetween v₁ v₂ = 2 := by
      rw [bondsBetween_eraseBond_of_ne M e he]; exact hbb
    have hNd1 : (MoleProp.eraseBond M e).deg v₁ = 4 := by
      rw [deg_eraseBond_of_ne M e hp1 hq1]; exact hM.reg _ hv₁
    have hNd2 : (MoleProp.eraseBond M e).deg v₂ = 4 := by
      rw [deg_eraseBond_of_ne M e hp2 hq2]; exact hM.reg _ hv₂
    set AN : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop := fun κ =>
      lgAdm (MoleProp.eraseBond M e) L γ η P κ ∧ MoleProp.erasedBondAdmissibility M e
        (fun κ0 => MoleProp.LargeGap M L γ η 0 κ0 ∧ (¬ SmallPairGap M v₁ v₂ L γ η κ0 ∧ Q₂ (mergeL κ0))) κ with hAN
    have h2 := hmg (MoleProp.eraseBond M e) (caps_eraseBond M e hM.cap) (hM.eraseBond_loop e) v₁ v₂ hv₁ hv₂ hne hNbb
      hNd1 hNd2 (hM.eraseBond_conn e) hgood2 P hP AN (fun κ h => ⟨h.1, by
        obtain ⟨κ0, ⟨_, hnsg, _⟩, _, hκ⟩ := h.2
        intro hs; apply hnsg; rw [← hκ] at hs; exact smallPairGap_of_eraseBond hs⟩)
    refine h2.trans ((mul_le_mul' le_rfl (iSup₂_le (a := ENNReal.ofReal ε₂) fun P' hP' => ?_)).trans ?_)
    · -- relabel `merge (𝕄 ∖ ℓ)` as `(merge 𝕄) ∖ ℓ`
      obtain ⟨ha, hm, ho⟩ := mergeErase_compat M hv₁ hne e he
      have hA := mergeErase_atoms M hv₁ hne e he
      have hcells := ladderCells_eq_of_dart_equiv' _ _ (mergeEraseEquiv M hv₁ hne e he) hA ha hm ho
      have hP'' : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond (mergePair M v₁ v₂ hv₁ hne) ⟨e, he⟩), 0 ≤ P' S := by
        rw [← hcells]; exact hP'
      refine le_trans ?_ (hQ2 P' hP'')
      refine MoleProp.countAFree_le_of_dart_equiv _ _ (mergeEraseEquiv M hv₁ hne e he) hA ha hm ho L γ δ C1 0 _ _
        (fun κ' h => ⟨lgAdm_relabel _ _ _ hA ha hm ho h.1, ?_⟩) P'
      obtain ⟨κN, hAN', _, hκ'⟩ := h.2
      obtain ⟨κ0, ⟨hLG0, hnsg0, hq0⟩, hsym0, hκN⟩ := hAN'.2
      refine ⟨mergeL κ0, ⟨Merge.largeGap hLG0 hnsg0, hq0⟩, fun y => hsym0 y.val, ?_⟩
      funext z
      change κ0 z.val.val = κ' ((mergeEraseEquiv M hv₁ hne e he).symm z)
      rw [hκ', ← hκN]
      rfl
    · rw [← ENNReal.ofReal_mul hc2]

end WaveTurbulence.MoleProp4
