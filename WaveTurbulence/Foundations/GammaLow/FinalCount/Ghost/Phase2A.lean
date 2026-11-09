/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.TriSurv
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Step2
public import WaveTurbulence.Foundations.FinalCount.G3Dart
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2
/-! **Ghost assembly, Phase 2 (A): the group-D pair is `PairOK` or an NC edge** (design: `CHAIN-DESIGN.md`).

At a triangle step with two `α`-ghosts `t j₁`, `t j₂` on the class `B`:
* the ghost gaps `gapAt (a j) (b j)` are `±` the record gaps `gvec` (run invariant `HGap.dg`, main `G3Dart`), so
  transversality of the records (`TRon`) is (T-TR) of the ghosts (`TRpair`);
* a lock of the two ghosts forces gap `0` at the third triangle atom, which the node class forbids (SG at `t 0`,
  `t 1`, nonzero at `t 2`) — the run form of M1-R2 Lemma 2.1;
* hence `pairOK_or_edge`: either `PairOK` (ν = 0) or the two ghosts are an edge of the NC graph (ν = 1, paid by the
  bank). Also `UStep2.mono`: the uniform step passes to sub-classes (the split classes). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

section tri
variable {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (T : TriData M)

theorem two_le_deg_t (j : Fin 3) : 2 ≤ M.deg (T.t j) := by
  have hne : T.a j ≠ T.b j := fun e => by have h1 := T.out_a j; rw [e, T.out_b j] at h1; cases h1
  have hsub : ({T.a j, T.b j} : Finset D) ⊆ M.dartsAt (T.t j) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    simp only [Molecule.dartsAt, mem_filter, mem_univ, true_and]
    rcases hx with rfl | rfl
    · exact T.atom_a j
    · exact T.atom_b j
  have := card_le_card hsub
  rw [card_pair hne] at this
  exact this

/-- Two distinct triangle atoms are adjacent (the triangle bond). -/
theorem adj_t {j₁ j₂ : Fin 3} (hne : j₁ ≠ j₂) : M.Adj (T.t j₁) (T.t j₂) := by
  have hc : j₂ = j₁ + 1 ∨ j₂ = j₁ - 1 := by fin_cases j₁ <;> fin_cases j₂ <;> simp_all <;> decide
  rcases hc with rfl | rfl
  · exact ⟨T.b j₁, T.atom_b j₁, by rw [T.mate_b, T.atom_a]⟩
  · refine ⟨T.a j₁, T.atom_a j₁, ?_⟩
    have := T.mate_a (j₁ - 1)
    simp only [sub_add_cancel] at this
    rw [this, T.atom_b]

end tri

/-- **The ghost gap is `±` the record gap** (`HGap.dg`). -/
theorem gap_t_eq_gvec {L : ℝ} {w : Mom d} {k0 : D₀ → (Fin d → ℤ)} {h : HSt V D₀} (hG : HGap L w k0 h)
    (T : TriData h.s.M) (j : Fin 3) (hne : h.s.cls (T.t j) ≠ .eps) :
    Molecule.gapAt L w (k0 ∘ h.s.down) (T.a j) (T.b j) = gvec h L w k0 (T.t j) ∨
      Molecule.gapAt L w (k0 ∘ h.s.down) (T.a j) (T.b j) = -gvec h L w k0 (T.t j) := by
  obtain ⟨p, vis, hp, hg⟩ := hG.dg (T.t j) (T.t_mem j) hne (T.a j) (T.b j) (T.atom_a j) (T.atom_b j) (T.out_a j) (T.out_b j)
  unfold gvec; rw [hp]; exact hg

theorem norm_sq_pm {r g : Mom d} (h : r = g ∨ r = -g) : ‖r‖ ^ 2 = ‖g‖ ^ 2 := by
  rcases h with rfl | rfl
  · rfl
  · rw [norm_neg]

theorem inner_sq_pm {r g r' g' : Mom d} (h : r = g ∨ r = -g) (h' : r' = g' ∨ r' = -g') :
    inner ℝ r r' ^ 2 = inner ℝ g g' ^ 2 := by
  rcases h with rfl | rfl <;> rcases h' with rfl | rfl <;> simp [inner_neg_left, inner_neg_right]

/-- **Transverse records give (T-TR) of the ghosts.** -/
theorem trpair_of_tron {L η : ℝ} {w : Mom d} {h : HSt V D₀} (T : TriData h.s.M) {B : Set (D₀ → (Fin d → ℤ))}
    (hG : ∀ k0 ∈ B, HGap L w k0 h) {j₁ j₂ : Fin 3} (hn₁ : h.s.cls (T.t j₁) ≠ .eps) (hn₂ : h.s.cls (T.t j₂) ≠ .eps)
    (hT : TRon L η w h B (T.t j₁) (T.t j₂)) : TRpair T L η w (AdmS (fun k => k ∈ B) h.s) j₁ j₂ := by
  rintro κ' ⟨k0, hk0, rfl⟩
  have e1 := gap_t_eq_gvec (hG k0 hk0) T j₁ hn₁
  have e2 := gap_t_eq_gvec (hG k0 hk0) T j₂ hn₂
  rw [norm_sq_pm e1, norm_sq_pm e2, inner_sq_pm e1 e2]
  exact hT k0 hk0

/-- **A lock of two triangle atoms forces gap `0` at the third one** (M1-R2 Lemma 2.1, run form). -/
theorem gap_third_zero_of_locked {L : ℝ} {w : Mom d} {h : HSt V D₀} (T : TriData h.s.M)
    {B : Set (D₀ → (Fin d → ℤ))} {j₁ j₂ k : Fin 3} (h1 : k + 1 = j₁) (h2 : k - 1 = j₂)
    (hL : Locked L w h B (T.t j₁) (T.t j₂)) :
    ∀ k0 ∈ B, Molecule.gapAt L w (k0 ∘ h.s.down) (T.a k) (T.b k) = 0 := by
  intro k0 hk0
  have hab : h.s.M.atom (T.b k) = h.s.M.atom (T.a k) := by rw [T.atom_a, T.atom_b]
  have hb : h.s.M.atom (h.s.M.mate (T.b k)) = T.t j₁ := by rw [T.mate_b, T.atom_a, h1]
  have ha : h.s.M.atom (h.s.M.mate (T.a k)) = T.t j₂ := by
    have := T.mate_a (k - 1)
    simp only [sub_add_cancel] at this
    rw [this, T.atom_b, h2]
  have hdir : h.s.M.out (T.b k) ≠ h.s.M.out (T.a k) := by rw [T.out_b, T.out_a]; simp
  have := hL (T.b k) (T.a k) hab hdir hb ha k0 hk0
  unfold Molecule.gapAt at this ⊢
  rw [← neg_sub, this, neg_zero]

/-- The node class forbids a zero gap at a triangle atom. -/
theorem gap_ne_zero_cls2 [Infinite V] {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {n : T2 h}
    (hn : Node2 L γ η h n) {k0 : D₀ → (Fin d → ℤ)} (hk : k0 ∈ cls2 L γ η w h A n) (k : Fin 3) :
    Molecule.gapAt L w (k0 ∘ h.s.down) ((triOf hn).a k) ((triOf hn).b k) ≠ 0 := by
  have hspec := Classical.choose_spec (Classical.choose_spec hn)
  obtain ⟨ht, ha, hb, -⟩ := hspec
  have ea : (triOf hn).a = n.2.1 := ha
  have eb : (triOf hn).b = n.2.2.1 := hb
  rw [ea, eb]
  obtain ⟨-, hsg, -, hnz, -⟩ := hk
  fin_cases k
  · exact gapKind_SG_ne_zero (hsg 0)
  · exact gapKind_SG_ne_zero (hsg 1)
  · exact hnz

/-- The other orientation of `gap_third_zero_of_locked`. -/
theorem gap_third_zero_of_locked' {L : ℝ} {w : Mom d} {h : HSt V D₀} (T : TriData h.s.M)
    {B : Set (D₀ → (Fin d → ℤ))} {j₁ j₂ k : Fin 3} (h1 : k + 1 = j₂) (h2 : k - 1 = j₁)
    (hL : Locked L w h B (T.t j₁) (T.t j₂)) :
    ∀ k0 ∈ B, Molecule.gapAt L w (k0 ∘ h.s.down) (T.a k) (T.b k) = 0 := by
  intro k0 hk0
  have hab : h.s.M.atom (T.a k) = h.s.M.atom (T.b k) := by rw [T.atom_a, T.atom_b]
  have hb : h.s.M.atom (h.s.M.mate (T.b k)) = T.t j₂ := by rw [T.mate_b, T.atom_a, h1]
  have ha : h.s.M.atom (h.s.M.mate (T.a k)) = T.t j₁ := by
    have := T.mate_a (k - 1)
    simp only [sub_add_cancel] at this
    rw [this, T.atom_b, h2]
  have hdir : h.s.M.out (T.a k) ≠ h.s.M.out (T.b k) := by rw [T.out_b, T.out_a]; simp
  exact hL (T.a k) (T.b k) hab hdir ha hb k0 hk0

theorem third_index {j₁ j₂ : Fin 3} (hne : j₁ ≠ j₂) :
    ∃ k : Fin 3, (k + 1 = j₁ ∧ k - 1 = j₂) ∨ (k + 1 = j₂ ∧ k - 1 = j₁) := by
  fin_cases j₁ <;> fin_cases j₂ <;> simp_all <;> decide

/-- **The group-D dichotomy**: two `α`-ghosts of a node are `PairOK` on the node class, or an edge of the NC graph of
the parent class. -/
theorem pairOK_or_edge [Infinite V] {Rn : ℕ} {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))}
    {n : T2 h} (hn : Node2 L γ η h n) (hI : Inv Rn h.s)
    (hG : ∀ k0 ∈ cls2 L γ η w h A n, HGap L w k0 h ∧ HInv L γ η w k0 h)
    (hne : (cls2 L γ η w h A n).Nonempty) {j₁ j₂ : Fin 3} (hj : j₁ ≠ j₂) {R₁ R₂ : ℝ} {k₁ k₂ : ℕ}
    (hc₁ : h.s.cls ((triOf hn).t j₁) = .alpha R₁ k₁) (hc₂ : h.s.cls ((triOf hn).t j₂) = .alpha R₂ k₂) :
    PairOK (triOf hn) L γ η w (AdmS (fun k => k ∈ cls2 L γ η w h A n) h.s) j₁ j₂ R₁ R₂ k₁ k₂ ∨
      NCEdge L γ η w h A ((triOf hn).t j₁) ((triOf hn).t j₂) := by
  set T := triOf hn
  by_cases hok : PairOK T L γ η w (AdmS (fun k => k ∈ cls2 L γ η w h A n) h.s) j₁ j₂ R₁ R₂ k₁ k₂
  · exact Or.inl hok
  right
  obtain ⟨κ, hκ⟩ := hne
  have hsub : cls2 L γ η w h A n ⊆ A := fun k hk => hk.1
  unfold PairOK at hok
  push Not at hok
  obtain ⟨hk₁, hk₂, hmin, hTR⟩ := hok
  have hok₁ := ((hG κ hκ).2.ok _ (T.t_mem j₁)).1 R₁ k₁ hc₁
  have hok₂ := ((hG κ hκ).2.ok _ (T.t_mem j₂)).1 R₂ k₂ hc₂
  have e₁ : k₁ = 0 := by obtain ⟨-, -, -, -, -, h0, -⟩ := hok₁; rcases h0 with h0 | h0; exacts [h0, absurd h0 hk₁]
  have e₂ : k₂ = 0 := by obtain ⟨-, -, -, -, -, h0, -⟩ := hok₂; rcases h0 with h0 | h0; exacts [h0, absurd h0 hk₂]
  have hn₁ : h.s.cls (T.t j₁) ≠ .eps := by rw [hc₁]; exact fun e => by cases e
  have hn₂ : h.s.cls (T.t j₂) ≠ .eps := by rw [hc₂]; exact fun e => by cases e
  have hdeg : ∀ j, h.s.cls (T.t j) ≠ .eps → h.s.M.deg (T.t j) = 2 := fun j hj =>
    le_antisymm (hI.ab _ (T.t_mem j) hj).1 (two_le_deg_t T j)
  have hcr₁ : Crit L γ η R₁ := le_trans (le_min_iff.1 hmin).1 le_rfl
  have hcr₂ : Crit L γ η R₂ := le_trans (le_min_iff.1 hmin).2 le_rfl
  refine ⟨T.t_ne hj, ⟨T.t_mem j₁, hdeg j₁ hn₁, R₁, e₁ ▸ hc₁, hcr₁⟩, ⟨T.t_mem j₂, hdeg j₂ hn₂, R₂, e₂ ▸ hc₂, hcr₂⟩,
    adj_t T hj, fun hT => hTR (trpair_of_tron T (fun k hk => (hG k hk).1) hn₁ hn₂ (hT.mono hsub)), ?_, ?_⟩
  · intro hL
    obtain ⟨k, hk⟩ := third_index hj
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact gap_ne_zero_cls2 hn hκ k (gap_third_zero_of_locked T h1 h2 (hL.mono hsub) κ hκ)
    · exact gap_ne_zero_cls2 hn hκ k (gap_third_zero_of_locked' T h1 h2 (hL.mono hsub) κ hκ)
  · intro hL
    obtain ⟨k, hk⟩ := third_index hj.symm
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact gap_ne_zero_cls2 hn hκ k (gap_third_zero_of_locked T h1 h2 (hL.mono hsub) κ hκ)
    · exact gap_ne_zero_cls2 hn hκ k (gap_third_zero_of_locked' T h1 h2 (hL.mono hsub) κ hκ)

/-- The uniform Step 2 passes to sub-classes. -/
theorem UStep2.mono {L γ η : ℝ} {w : Mom d} {A B : (D₀ → (Fin d → ℤ)) → Prop} (hBA : ∀ k, B k → A k)
    {h h' : HSt V D₀} (hs : UStep2 L γ η w A h h') : UStep2 L γ η w B h h' := by
  have hI : ∀ {p : D₀ × D₀} {R : ℝ}, IotaUnif A L η w h p R → IotaUnif B L η w h p R := by
    rintro p R ⟨q, hq, hcar, sg, hsg, hb⟩
    exact ⟨q, hq, hcar, sg, hsg, fun k hk => hb k (hBA k hk)⟩
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₀' hι₁ hι₁' h3 =>
    refine UStep2.tri h T Q kp hQ hkp (fun k hk => hsg k (hBA k hk)) (fun k hk => hsim k (hBA k hk)) hcl
      (fun k hk => hnz k (hBA k hk)) (fun he h50 => hI (hι₀ he h50)) (fun he h0 k hk => hι₀' he h0 k (hBA k hk))
      (fun he h50 => ?_) (fun he h0 k hk => hι₁' he h0 k (hBA k hk)) h3
    rcases hι₁ he h50 with hu | ⟨he0, sg, hsg', hb⟩
    · exact Or.inl (hI hu)
    · exact Or.inr ⟨he0, sg, hsg', fun k hk => hb k (hBA k hk)⟩

end WaveTurbulence.GammaLow.FinalCount.Ghost
