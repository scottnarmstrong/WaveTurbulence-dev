/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.LayerCnt.CutExpand
import Mathlib.Tactic

/-! # Cut groups of every expanded vine template (TARGET layervine, L1531)

For every vine type `X` and insertion counts `ks`: every base cut group of the template (`CutG`) and every inserted
rung of a base cut slot (`CutS`) is the level-`1` set of a cut labelling of the expanded template.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LayerCnt
open WaveTurbulence.Vine

/-- Elementary facts about a base template used by the insertion machinery. -/
@[expose] def BaseOK (T : VineTemplate) : Prop :=
  2 ≤ T.n ∧ (∀ e ∈ T.bonds, e.1 < T.n ∧ e.2 < T.n) ∧
    ∀ s ∈ T.slots, (∀ v ∈ slotEnds s, v < T.n) ∧ T.bonds.count s.1 ≤ 1 ∧ T.bonds.count s.2 ≤ 1

instance (T : VineTemplate) : Decidable (BaseOK T) := by unfold BaseOK slotEnds; infer_instance

theorem baseOK (X : VineType) : BaseOK X.template := by
  cases X <;> decide +kernel

theorem expand_certG (X : VineType) (ks : List ℕ) (hk : ks.length = X.template.slots.length)
    (g : List ℕ) (hg : CutG X.template g) :
    ∃ σ, CertAt (X.expand ks) (fun v => v ∈ g) σ ∧ ∀ v ∈ g, σ v = 1 := by
  obtain ⟨hn2, hbdd, hsl⟩ := baseOK X
  obtain ⟨h0, h1, hcut, hside, hgn⟩ := hg
  set σ0 := sigmaOf X.template (fun v => g.contains v) [] with hσ0
  have hmem : ∀ sk ∈ X.template.slots.zip ks, sk.1 ∈ X.template.slots := fun sk hsk =>
    (List.of_mem_zip hsk).1
  obtain ⟨σ', h1', h2', h3', h4'⟩ := fold_ext (X.template.slots.zip ks) X.template.n X.template [] σ0 le_rfl
    hbdd (fun sk hsk => ⟨(hsl _ (hmem sk hsk)).2.1, (hsl _ (hmem sk hsk)).2.2⟩)
    (fun sk hsk => ⟨(hsl _ (hmem sk hsk)).1, hside _ (hmem sk hsk)⟩)
    (fun e he _ => hcut e he) (sigmaOf_le _ _ _)
  refine ⟨σ', ⟨h2', ?_, h4', ?_⟩, ?_⟩
  · rw [h1' 0 (by omega), h1' 1 (by omega)]; exact Or.inl ⟨h0, h1⟩
  · intro v hv hv1
    by_cases hvn : v < X.template.n
    · rw [h1' v hvn] at hv1
      have : (g.contains v) = true := by
        by_contra hc
        simp only [hσ0, sigmaOf, hc] at hv1
        split_ifs at hv1 <;> simp_all
      simpa using this
    · exfalso
      apply h3' v (by omega)
      · unfold VineType.expand at hv
        exact hv
      · exact hv1
  · intro v hv
    rw [h1' v (hgn v hv)]
    simp [hσ0, sigmaOf, hv]

theorem rungσ_le {n k i c₀ c₁ : ℕ} {τ : ℕ → ℕ} (h0 : c₀ ≤ 2) (h1 : c₁ ≤ 2) (hτ : ∀ v, τ v ≤ 2) (v : ℕ) :
    rungσ n k i c₀ c₁ τ v ≤ 2 := by
  unfold rungσ
  by_cases h : v < n ∨ n + 2 * k ≤ v
  · rw [if_pos h]; exact hτ v
  · rw [if_neg h]; dsimp only; split_ifs <;> omega

theorem expand_certS (X : VineType) (ks : List ℕ) (hk : ks.length = X.template.slots.length)
    (c : ℕ) (hc : c < X.template.slots.length) (hS : CutS X.template c (X.template.slots[c]'hc))
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i ≤ ks[c]'(by omega)) :
    ∃ σ, CertAt (X.expand ks)
      (fun v => v = X.template.n + 2 * (ks.take c).sum + (i - 1) ∨
        v = X.template.n + 2 * (ks.take c).sum + ks[c]'(by omega) + (i - 1)) σ ∧
      σ (X.template.n + 2 * (ks.take c).sum + (i - 1)) = 1 ∧
      σ (X.template.n + 2 * (ks.take c).sum + ks[c]'(by omega) + (i - 1)) = 1 := by
  obtain ⟨hn2, hbdd, hsl⟩ := baseOK X
  set T0 := X.template with hT0
  set F : VineTemplate → ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ → VineTemplate := fun U sk => insertRungs U sk.1 sk.2 with hF
  set xs := T0.slots.zip ks with hxs
  have hcl : c < xs.length := by simp [hxs, List.length_zip, hk, hc]
  have hckl : c < ks.length := by omega
  set s := T0.slots[c]'hc with hs
  set kc := ks[c]'hckl with hkc
  have hxc : xs[c]'hcl = (s, kc) := by simp [hxs, hs, hkc, List.getElem_zip]
  have hloc : xs = xs.take c ++ (xs[c]'hcl) :: xs.drop (c + 1) := by
    rw [← List.drop_eq_getElem_cons hcl, List.take_append_drop]
  have hexp : X.expand ks = (xs.drop (c + 1)).foldl F (insertRungs ((xs.take c).foldl F T0) s kc) := by
    unfold VineType.expand
    change xs.foldl F T0 = _
    conv_lhs => rw [hloc]
    rw [List.foldl_append, List.foldl_cons, hxc]
  set P := (xs.take c).foldl F T0 with hP
  have hPn : P.n = T0.n + 2 * (ks.take c).sum := by
    rw [hP, fold_insertRungs_atoms]
    have : (xs.take c).map Prod.snd = ks.take c := by
      rw [List.map_take, hxs, List.map_snd_zip (by omega)]
    rw [this]
  -- the slot labelling
  obtain ⟨hτ0, hτ1, hτne, hτcut, hτx, hτy, hτxy, hτside⟩ := hS
  set τ := sigmaOf T0 (fun _ => false) [s.1, s.2] with hτ
  have hsm : s ∈ T0.slots := List.getElem_mem hc
  obtain ⟨hsend, hsc1, hsc2⟩ := hsl s hsm
  have hx : s.1.1 < T0.n := hsend _ (by simp [slotEnds])
  have hy : s.1.2 < T0.n := hsend _ (by simp [slotEnds])
  have hx' : s.2.1 < T0.n := hsend _ (by simp [slotEnds])
  have hy' : s.2.2 < T0.n := hsend _ (by simp [slotEnds])
  have hτ2 : ∀ v, τ v ≤ 2 := sigmaOf_le _ _ _
  -- other slots
  have hidx : ∀ j (hj : j < xs.length), j ≠ c → Sides2 τ (slotEnds (xs[j]'hj).1) := by
    intro j hj hjc
    have hjs : j < T0.slots.length := by
      have : xs.length ≤ T0.slots.length := by simp [hxs, List.length_zip]
      omega
    have : (xs[j]'hj).1 = T0.slots[j]'hjs := by simp [hxs, List.getElem_zip]
    rw [this]
    exact hτside j hjs hjc _ (List.getElem?_eq_getElem hjs)
  have hpre : ∀ sk ∈ xs.take c, Sides2 τ (slotEnds sk.1) := by
    intro sk hsk
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hsk
    have hj' : j < c := by simp at hj; omega
    have hjx : j < xs.length := by simp at hj; omega
    have : (xs.take c)[j]'hj = xs[j]'hjx := by simp
    rw [this]
    exact hidx j hjx (by omega)
  have hpost : ∀ sk ∈ xs.drop (c + 1), Sides2 τ (slotEnds sk.1) := by
    intro sk hsk
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hsk
    have hjx : c + 1 + j < xs.length := by simp at hj; omega
    have : (xs.drop (c + 1))[j]'hj = xs[c + 1 + j]'hjx := by simp
    rw [this]
    exact hidx _ hjx (by omega)
  have hends_xs : ∀ sk ∈ xs, ∀ v ∈ slotEnds sk.1, v < T0.n := fun sk hsk =>
    (hsl _ (List.of_mem_zip hsk).1).1
  have hcnt_xs : ∀ sk ∈ xs, T0.bonds.count sk.1.1 ≤ 1 ∧ T0.bonds.count sk.1.2 ≤ 1 := fun sk hsk =>
    ⟨(hsl _ (List.of_mem_zip hsk).1).2.1, (hsl _ (List.of_mem_zip hsk).1).2.2⟩
  -- extend through the prefix
  obtain ⟨σp, hp1, hp2, hp3, hp4⟩ := fold_ext (xs.take c) T0.n T0 [s.1, s.2] τ le_rfl hbdd
    (fun sk h => hcnt_xs sk (List.mem_of_mem_take h))
    (fun sk h => ⟨hends_xs sk (List.mem_of_mem_take h), hpre sk h⟩) hτcut hτ2
  have hPb := fold_bdd (xs.take c) T0.n T0 le_rfl hbdd (fun sk h => hends_xs sk (List.mem_of_mem_take h))
  have hPc : ∀ e : ℕ × ℕ, e.1 < T0.n → e.2 < T0.n → P.bonds.count e ≤ T0.bonds.count e := fun e h1 h2 =>
    fold_count (xs.take c) T0.n T0 e h1 h2 le_rfl (fun sk h => hends_xs sk (List.mem_of_mem_take h))
  have hPge : T0.n ≤ P.n := by rw [hPn]; omega
  have hPends : ∀ v ∈ slotEnds s, v < P.n := fun v hv => lt_of_lt_of_le (hsend v hv) hPge
  have hc1 : P.bonds.count s.1 ≤ 1 := (hPc s.1 hx hy).trans hsc1
  have hc2 : P.bonds.count s.2 ≤ 1 := (hPc s.2 hx' hy').trans hsc2
  -- the slot ends
  have hτx1 : τ s.1.1 ≠ 1 := hτne _ hx
  have hτy1 : τ s.1.2 ≠ 1 := hτne _ hy
  have hτx2 := hτ2 s.1.1
  have hτy2 := hτ2 s.1.2
  have hcc : (τ s.1.1 = 0 ∧ τ s.1.2 = 2) ∨ (τ s.1.1 = 2 ∧ τ s.1.2 = 0) := by omega
  have hrung := rung_cert (T := P) (s := s) (k := kc) (i := i) hi1 hi2 hc1 hc2 hPb hPends
    (τ := σp) (c₀ := τ s.1.1) (c₁ := τ s.1.2) hcc
    ⟨by rw [hp1 _ hx], by rw [hp1 _ hx', ← hτx]⟩ ⟨by rw [hp1 _ hy], by rw [hp1 _ hy', ← hτy]⟩ hp4
  set ρ := rungσ P.n kc i (τ s.1.1) (τ s.1.2) σp with hρ
  have hρle : ∀ v, ρ v ≤ 2 := rungσ_le hτx2 hτy2 hp2
  have hρold : ∀ v < T0.n, ρ v = τ v := fun v hv => by
    rw [hρ, rungσ_old (by omega), hp1 v hv]
  have hTmn : (insertRungs P s kc).n = P.n + 2 * kc := insertRungs_atoms _ _ _
  obtain ⟨σf, hf1, hf2, hf3, hf4⟩ := fold_ext (xs.drop (c + 1)) T0.n (insertRungs P s kc) [] ρ
    (by omega) (bdd_insert hPends hPb)
    (fun sk hsk => by
      have hm : sk ∈ xs := List.mem_of_mem_drop hsk
      have hh := hends_xs sk hm
      have hA : sk.1.1.1 < T0.n ∧ sk.1.1.2 < T0.n :=
        ⟨hh _ (by simp [slotEnds]), hh _ (by simp [slotEnds])⟩
      have hB : sk.1.2.1 < T0.n ∧ sk.1.2.2 < T0.n :=
        ⟨hh _ (by simp [slotEnds]), hh _ (by simp [slotEnds])⟩
      exact ⟨(count_insert_le (s := s) (k := kc) ⟨by omega, by omega⟩).trans
          ((hPc _ hA.1 hA.2).trans (hcnt_xs sk hm).1),
        (count_insert_le (s := s) (k := kc) ⟨by omega, by omega⟩).trans
          ((hPc _ hB.1 hB.2).trans (hcnt_xs sk hm).2)⟩)
    (fun sk hsk => by
      have hm : sk ∈ xs := List.mem_of_mem_drop hsk
      refine ⟨hends_xs sk hm, ?_⟩
      have := hpost sk hsk
      intro ⟨⟨v, hv, hv0⟩, ⟨w, hw, hw2⟩⟩
      apply this
      exact ⟨⟨v, hv, by rw [← hρold v (hends_xs sk hm v hv)]; exact hv0⟩,
        ⟨w, hw, by rw [← hρold w (hends_xs sk hm w hw)]; exact hw2⟩⟩)
    hrung hρle
  rw [hexp]
  refine ⟨σf, ⟨hf2, ?_, hf4, ?_⟩, ?_, ?_⟩
  · have h0 : σf 0 = 0 := by rw [hf1 0 (by omega), hρold 0 (by omega)]; exact hτ0
    have h1 : σf 1 = 2 := by rw [hf1 1 (by omega), hρold 1 (by omega)]; exact hτ1
    exact Or.inl ⟨h0, h1⟩
  · intro v hv hv1
    by_cases hvT : v < P.n + 2 * kc
    · rw [hf1 v (by omega)] at hv1
      by_cases hvP : v < P.n
      · exfalso
        rw [hρ, rungσ_old hvP] at hv1
        by_cases hv0 : v < T0.n
        · rw [hp1 v hv0] at hv1; exact hτne v hv0 hv1
        · exact hp3 v (by omega) hvP hv1
      · have hvu : v < P.n + kc ∨ P.n + kc ≤ v := by omega
        rcases hvu with hvu | hvu
        · have : v = P.n + (v - P.n) := by omega
          rw [hρ, this, rungσ_u (by omega)] at hv1
          split_ifs at hv1 <;> omega
        · have : v = P.n + kc + (v - P.n - kc) := by omega
          rw [hρ, this, rungσ_v (by omega)] at hv1
          split_ifs at hv1 <;> try omega
    · exfalso
      refine hf3 v (by omega) (by simpa [hTmn] using hv) hv1
  · rw [hf1 _ (by omega), hρ, show T0.n + 2 * (ks.take c).sum + (i - 1) = P.n + (i - 1) by omega,
      rungσ_u (by omega)]
    simp [Nat.sub_add_cancel hi1]
  · rw [hf1 _ (by omega), hρ,
      show T0.n + 2 * (ks.take c).sum + kc + (i - 1) = P.n + kc + (i - 1) by omega, rungσ_v (by omega)]
    simp [Nat.sub_add_cancel hi1]

end WaveTurbulence.LayerCnt
