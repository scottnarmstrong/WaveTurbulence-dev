/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBBridgeCut
public import WaveTurbulence.Foundations.FinalCount.AppBErasedBondDecorations
import Mathlib.Tactic

/-! # DH23 BR-N: the exact unnormalized counting reduction -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open scoped ENNReal
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]

/-- Retain all old requirements and the fixed actual bridge label. -/
def appbBridgePostAdmissibility (M : Molecule V D) (e : D) {d : ℕ}
    (Adm : (D → (Fin d → ℤ)) → Prop) (q : Fin d → ℤ)
    (κ' : {x : D // x ≠ e ∧ x ≠ M.mate e} → (Fin d → ℤ)) : Prop :=
  ∃ κ : D → (Fin d → ℤ), Adm κ ∧ κ e = q ∧ (∀ x, κ (M.mate x) = κ x) ∧
    (fun x : {x : D // x ≠ e ∧ x ≠ M.mate e} => κ x.val) = κ'

/-- DH23 brprop / DH21 Lemma 9.14: an actual bridge label is fixed by the
old conservation parameters, so deleting it costs no local-label factor.
The post predicate retains every inherited requirement. -/
theorem appb_bridge_countE_exists_post (M : Molecule V D) (e : D) (hb : Degen.IsBridge M e)
    {d : ℕ} {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (w : Mom d)
    (Adm : (D → (Fin d → ℤ)) → Prop) :
    ∃ q : Fin d → ℤ, appbCountE M L γ δ w Adm ≤
      appbCountE (eraseBond M e) L γ δ w (appbBridgePostAdmissibility M e Adm q) := by
  classical
  obtain ⟨p,hp⟩ := appbCountE_attained M hL γ δ w Adm
  let S := p.decorations L γ δ w Adm
  by_cases hn : S.Nonempty
  · obtain ⟨κ0,hκ0⟩ := hn
    let q := κ0 e
    have hfixed {κ : D → (Fin d → ℤ)} (hκ : κ ∈ S) : κ e = q :=
      appb_bridge_label_unique M e hb hL.ne' hκ.1 hκ0.1
    let T := (appbErasedBondParameters M e p L w q).decorations L γ δ w
      (appbBridgePostAdmissibility M e Adm q)
    let restrict : (D → (Fin d → ℤ)) → ({x : D // x ≠ e ∧ x ≠ M.mate e} → (Fin d → ℤ)) :=
      fun κ x => κ x.val
    have hmap : Set.MapsTo restrict S T := by
      intro κ hκ
      obtain ⟨hd,hr,ha⟩ := hκ
      have hq : κ e = q := hfixed ⟨hd,hr,ha⟩
      exact ⟨appb_isDecoration_eraseBond M e hd hq,
        appb_isRestricted_eraseBond M e hd.1 hr hq,κ,ha,hq,hd.1,rfl⟩
    have hinj : Set.InjOn restrict S := by
      intro κ hκ κ' hκ' heq
      funext x
      by_cases he : x = e
      · subst x
        exact (hfixed hκ).trans (hfixed hκ').symm
      · by_cases hm : x = M.mate e
        · rw [hm,hκ.1.1 e,hκ'.1.1 e]
          exact (hfixed hκ).trans (hfixed hκ').symm
        · exact congrFun heq ⟨x,he,hm⟩
    refine ⟨q,?_⟩
    calc
      appbCountE M L γ δ w Adm = S.encard := hp.symm
      _ ≤ T.encard := Set.encard_le_encard_of_injOn hmap hinj
      _ ≤ _ := by
        rw [appbCountE_eq_iSup]
        exact le_iSup_of_le (appbErasedBondParameters M e p L w q) le_rfl
  · have he : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    refine ⟨0,?_⟩
    rw [← hp]
    change S.encard ≤ _
    rw [he,Set.encard_empty]
    exact bot_le

end WaveTurbulence.Mole
