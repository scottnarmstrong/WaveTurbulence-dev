/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MergeScale
public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.TwoExitCount
import Mathlib.Tactic

/-! # Counting through the merged molecule (DH23 L1977)

`𝔈(M; Adm) ≤ 2 |scaleFam| · Φ · sup_{P'} 𝔈(merge M; lgAdm ∧ mergeAdm)` where `Φ` bounds the number of decorations of `M`
with a given restriction to the merged molecule (the pair `(p₁, p₂)` of the double bond). The factor `2` is the splitting
of the energy window of the merged atom (`Γ_{v₁} + Γ_{v₂}`, radius `2τ`) into two windows of radius `τ`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.FinalCountG8
open WaveTurbulence.MoleProp4
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

namespace MergeSum
variable {M : Molecule V D} {v₁ v₂ : V} {hv₁ : v₁ ∈ M.atoms} {hne : v₁ ≠ v₂}

theorem countEFree_le_merge (hv₂ : v₂ ∈ M.atoms)
    (hloopN : ∀ z, (mergePair M v₁ v₂ hv₁ hne).atom z ≠ (mergePair M v₁ v₂ hv₁ hne).atom
      ((mergePair M v₁ v₂ hv₁ hne).mate z))
    (hdegN : ∀ a ∈ (mergePair M v₁ v₂ hv₁ hne).atoms, (mergePair M v₁ v₂ hv₁ hne).deg a ≤ 4)
    (hopen : ∀ S ∈ MoleProp.ladderCells (mergePair M v₁ v₂ hv₁ hne), v₁ ∈ S →
      GoodCell (mergePair M v₁ v₂ hv₁ hne) S)
    {d : ℕ} {L γ δ η : ℝ} (hL : 1 ≤ L) (hδ : 0 < δ) (P : Finset V → ℝ) (Adm : (D → (Fin d → ℤ)) → Prop)
    (hAdm : ∀ κ, Adm κ → lgAdm M L γ η P κ ∧ ¬ SmallPairGap M v₁ v₂ L γ η κ) (Φ : ℕ∞)
    (hfib : ∀ (c : V → Mom d) (β : V → ℝ) (k0 : D → Mom d) (κ₀ : D → (Fin d → ℤ)),
      M.IsDecoration L (0 : Mom d) c κ₀ → M.IsRestricted L γ δ (0 : Mom d) β k0 κ₀ → Adm κ₀ →
      {κ | (M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ) ∧
        (fun y : OffPair M v₁ v₂ => κ y.val) = fun y => κ₀ y.val}.encard ≤ Φ) :
    MoleProp.countEFree M L γ δ (0 : Mom d) Adm ≤
      (2 * (scaleFam M v₁ v₂ hv₁ hne L P).card : ℕ∞) * Φ *
        ⨆ P' ∈ scaleFam M v₁ v₂ hv₁ hne L P, MoleProp.countEFree (mergePair M v₁ v₂ hv₁ hne) L γ δ (0 : Mom d)
          (fun κ' => lgAdm (mergePair M v₁ v₂ hv₁ hne) L γ η P' κ' ∧ mergeAdm M v₁ v₂ Adm κ') := by
  classical
  have hLp : 0 < L := by linarith
  set N := mergePair M v₁ v₂ hv₁ hne with hN
  set τ := δ⁻¹ * L ^ (-2 * γ) with hτ
  have hτ0 : 0 < τ := by positivity
  set fam := scaleFam M v₁ v₂ hv₁ hne L P with hfam
  set G := ⨆ P' ∈ fam, MoleProp.countEFree N L γ δ (0 : Mom d)
    (fun κ' => lgAdm N L γ η P' κ' ∧ mergeAdm M v₁ v₂ Adm κ') with hG
  conv_lhs => rw [MoleProp.countEFree]
  refine iSup_le fun c => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  set A := {κ : D → (Fin d → ℤ) | M.IsDecoration L (0 : Mom d) c κ ∧ M.IsRestricted L γ δ (0 : Mom d) β k0 κ ∧ Adm κ}
    with hA
  have hAfin : A.Finite := (Mole.finite_restricted M hLp γ δ 0 β k0).subset fun _ h => h.2.1
  -- the two windows
  let As : ℝ → Set (D → (Fin d → ℤ)) := fun s =>
    {κ | κ ∈ A ∧ |M.Gamma L 0 κ v₁ + M.Gamma L 0 κ v₂ - (β v₁ + β v₂ + s * τ)| ≤ τ}
  have hcover : A ⊆ As (-1) ∪ As 1 := by
    intro κ hκ
    have h1 := hκ.2.1.1 v₁ hv₁
    have h2 := hκ.2.1.1 v₂ hv₂
    rw [abs_le] at h1 h2
    by_cases hs : 0 ≤ M.Gamma L 0 κ v₁ + M.Gamma L 0 κ v₂ - (β v₁ + β v₂)
    · right
      refine ⟨hκ, ?_⟩
      rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
    · left
      refine ⟨hκ, ?_⟩
      rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]
  let E : ℝ → (Finset V → ℝ) → Set (OffPair M v₁ v₂ → (Fin d → ℤ)) := fun s P' =>
    {κ' | N.IsDecoration L 0 (mcharges v₁ v₂ c) κ' ∧
      N.IsRestricted L γ δ 0 (fun v => if v = v₁ then β v₁ + β v₂ + s * τ else β v) (fun y => k0 y.val) κ' ∧
      (lgAdm N L γ η P' κ' ∧ mergeAdm M v₁ v₂ Adm κ')}
  have hk0' : ∀ z : OffPair M v₁ v₂, k0 (N.mate z).val = k0 z.val := fun z => hk0 z.val
  have hE : ∀ s, ∀ P' ∈ fam, (E s P').encard ≤ G := by
    intro s P' hP'
    refine (MoleProp.encard_le_countEFree N L γ δ 0 _ (mcharges v₁ v₂ c) _ (fun y => k0 y.val) hk0').trans ?_
    exact le_iSup₂_of_le (f := fun P'' (_ : P'' ∈ fam) => MoleProp.countEFree N L γ δ (0 : Mom d)
      (fun κ' => lgAdm N L γ η P'' κ' ∧ mergeAdm M v₁ v₂ Adm κ')) P' hP' le_rfl
  have hbound : ∀ s, (As s).encard ≤ (fam.card : ℕ∞) * G * Φ := by
    intro s
    set Bs : Set (OffPair M v₁ v₂ → (Fin d → ℤ)) := ⋃ P' ∈ fam, E s P' with hBs
    have hmaps : ∀ κ ∈ As s, (fun y : OffPair M v₁ v₂ => κ y.val) ∈ Bs := by
      intro κ hκ
      obtain ⟨⟨hdec, hres, hadm⟩, hwin⟩ := hκ
      obtain ⟨hLG, hCGR⟩ := (hAdm κ hadm).1
      obtain ⟨P', hP', hcgr⟩ := exists_mergeFam_cgr hloopN hdegN hopen hL hdec.1 hCGR
      refine Set.mem_biUnion hP' ⟨merge_isDecoration hv₂ hdec, ⟨?_, ?_⟩,
        ⟨Merge.largeGap hLG (hAdm κ hadm).2, hcgr⟩, ⟨κ, hadm, hdec.1, fun y => rfl⟩⟩
      · intro v hv
        by_cases h1 : v = v₁
        · subst h1
          simp only [if_true]
          rw [merge_gamma_v₁ hdec.1]
          exact hwin
        · simp only [h1, if_false]
          rw [merge_gamma_far hv h1]
          exact hres.1 v (mem_erase.mp hv).2
      · intro z
        exact hres.2 z.val
    have hAs : (As s).Finite := hAfin.subset fun _ h => h.1
    have hB : Bs.encard ≤ (fam.card : ℕ∞) * G := by
      refine (encard_biUnion_le fam (E s)).trans ?_
      calc ∑ P' ∈ fam, (E s P').encard ≤ ∑ _P' ∈ fam, G := sum_le_sum fun P' hP' => hE s P' hP'
        _ = _ := by rw [sum_const, nsmul_eq_mul]
    calc (As s).encard ≤ Bs.encard * Φ := by
          refine encard_le_mul_of_fiber hAs (fun κ => fun y : OffPair M v₁ v₂ => κ y.val) Bs hmaps Φ ?_
          intro b hb
          by_cases hne' : {a | a ∈ As s ∧ (fun y : OffPair M v₁ v₂ => a y.val) = b}.Nonempty
          · obtain ⟨κ₀, hκ₀, rfl⟩ := hne'
            refine le_trans (Set.encard_mono ?_) (hfib c β k0 κ₀ hκ₀.1.1 hκ₀.1.2.1 hκ₀.1.2.2)
            rintro κ ⟨hκ, hκeq⟩
            exact ⟨hκ.1, hκeq⟩
          · rw [Set.not_nonempty_iff_eq_empty.mp hne', Set.encard_empty]; exact bot_le
      _ ≤ (fam.card : ℕ∞) * G * Φ := mul_le_mul_left hB Φ
  calc A.encard ≤ (As (-1) ∪ As 1).encard := Set.encard_mono hcover
    _ ≤ (As (-1)).encard + (As 1).encard := Set.encard_union_le _ _
    _ ≤ (fam.card : ℕ∞) * G * Φ + (fam.card : ℕ∞) * G * Φ := add_le_add (hbound _) (hbound _)
    _ = (2 * fam.card : ℕ∞) * Φ * G := by ring

end MergeSum
end WaveTurbulence.FinalCountG8
