/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Checker.SoundBasic

/-!
# Soundness of `tvineB`: a block isomorphic to a bond list that passes `tvineB` is a T-vine

* `nbrsU_eq`: L1's `nbrs` of a vertex, read off the neighbour list of its image;
* `closureGraph`: the closure `C` (L1's `IsClosureU`) built from the joints' neighbours;
* `isTVineU_of_tvineB`: `IsBlockU H j₁ j₂` and `tvineB c (f j₁) (f j₂) = true` give `IsTVineU H j₁ j₂`.
-/

@[expose] public section

namespace WaveTurbulence.TVine.Checker

open TVine Core

variable {V : Type*} [DecidableEq V]

/-- L1's neighbour multiset through the isomorphism. -/
theorem nbrsU_eq {H : UMultigraph V} {c : Edges} (φ : Iso H c) {v : V} (hv : v ∈ H.verts) (M : Multiset ℕ)
    (hM : ∀ z, (nbrs c (φ.f v)).count z = M.count z) (hMv : φ.f v ∉ M) (hMe : ∀ z ∈ M, InEnds c z) :
    Core.nbrs H v = M.map φ.g := by
  ext w
  rw [Core.count_nbrs, Multiset.count_map]
  have hfilter : ∀ z ∈ M, (w = φ.g z ↔ φ.f w = z ∧ w ∈ H.verts) := by
    intro z hz
    constructor
    · rintro rfl; exact ⟨φ.fg z (hMe z hz), φ.gv z (hMe z hz)⟩
    · rintro ⟨h1, h2⟩; rw [← h1, φ.gf w h2]
  by_cases hw : w ∈ H.verts
  · have hcount : (M.filter fun z => w = φ.g z).card = M.count (φ.f w) := by
      rw [Multiset.count_eq_card_filter_eq]
      congr 1
      apply Multiset.filter_congr
      intro z hz
      rw [hfilter z hz]; simp [hw, eq_comm]
    rw [hcount, if_pos hw]
    by_cases hvw : v = w
    · subst hvw
      have := hM (φ.f v)
      rw [count_nbrs, Multiset.count_eq_zero.mpr hMv] at this
      rw [if_pos rfl, φ.mult_eq v hv v hv, this, Multiset.count_eq_zero.mpr hMv]
    · rw [if_neg hvw, φ.mult_eq v hv w hw, ← count_nbrs, hM, Nat.add_zero]
  · have hvw : ¬ v = w := fun h => hw (h ▸ hv)
    rw [if_neg hw, if_neg hvw, Nat.add_zero]
    symm
    rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
    intro z hz h
    exact hw ((hfilter z hz).mp h).2

theorem mult_zero_of_loopless {c : Edges} (h : loopless c = true) (x : ℕ) : mult c x x = 0 := by
  unfold mult
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he hp
  have := List.all_eq_true.mp h e he
  rcases (isPair_iff x x e).mp hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all

/-! ## The closure graph -/

/-- The closure of `H` at `j₁, j₂` with the added bonds `added` (as in L1's `IsClosureU`). -/
def closureGraph (H : UMultigraph V) (j₁ j₂ : V) (added : Multiset (Sym2 V))
    (hadd : ∀ e ∈ added, ∀ x ∈ e, x ∈ H.verts ∧ x ≠ j₁ ∧ x ≠ j₂) : UMultigraph V where
  verts := (H.verts.erase j₁).erase j₂
  mult e := (if j₁ ∈ e ∨ j₂ ∈ e then 0 else H.mult e) + added.count e
  supp := by
    intro e he x hx
    simp only [Finset.mem_erase]
    by_cases ha : added.count e = 0
    · rw [ha, Nat.add_zero] at he
      split_ifs at he with hj
      · exact absurd rfl he
      · have hxv := H.supp e he x hx
        refine ⟨fun h => hj (Or.inr (h ▸ hx)), fun h => hj (Or.inl (h ▸ hx)), hxv⟩
    · obtain ⟨h1, h2, h3⟩ := hadd e (Multiset.count_ne_zero.mp ha) x hx
      exact ⟨h3, h2, h1⟩

theorem exists_adj_of_deg {H : UMultigraph V} {v : V} (hv : v ∈ H.verts) (h : Core.deg H v ≠ 0) :
    ∃ w ∈ H.verts, H.mult s(v, w) ≠ 0 := by
  unfold Core.deg at h
  by_cases hl : H.mult s(v, v) = 0
  · rw [hl, Nat.add_zero] at h
    obtain ⟨w, hw, hw'⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨w, hw, hw'⟩
  · exact ⟨v, hv, hl⟩

/-- The isomorphism between the closure graph and the `Bool` closure list `rest ++ addL`. -/
def iso_closureGraph {H : UMultigraph V} {c : Edges} (φ : Iso H c) {j₁ j₂ : V} (hj₁ : j₁ ∈ H.verts)
    (hj₂ : j₂ ∈ H.verts) (hdeg : ∀ v ∈ H.verts, v ≠ j₁ → v ≠ j₂ → Core.deg H v ≠ 0) (addL : Edges)
    (haddL : ∀ e ∈ addL, InEnds c e.1 ∧ InEnds c e.2 ∧ e.1 ≠ φ.f j₁ ∧ e.1 ≠ φ.f j₂ ∧ e.2 ≠ φ.f j₁ ∧
      e.2 ≠ φ.f j₂)
    (hcov : ∀ z, InEnds c z → z ≠ φ.f j₁ → z ≠ φ.f j₂ → (mult c z (φ.f j₁) ≠ 0 ∨ mult c z (φ.f j₂) ≠ 0) →
      InEnds addL z)
    (hadd : ∀ e ∈ (addL.map fun e => s(φ.g e.1, φ.g e.2) : Multiset (Sym2 V)), ∀ x ∈ e,
      x ∈ H.verts ∧ x ≠ j₁ ∧ x ≠ j₂) :
    Iso (closureGraph H j₁ j₂ (addL.map fun e => s(φ.g e.1, φ.g e.2) : Multiset (Sym2 V)) hadd)
      ((c.filter fun e => !touches (φ.f j₁) e && !touches (φ.f j₂) e) ++ addL) := by
  set a := φ.f j₁; set b := φ.f j₂
  have ha := φ.fv j₁ hj₁; have hb := φ.fv j₂ hj₂
  have memC : ∀ v, v ∈ (closureGraph H j₁ j₂ _ hadd).verts ↔ v ∈ H.verts ∧ v ≠ j₁ ∧ v ≠ j₂ := by
    intro v; simp only [closureGraph, Finset.mem_erase]; tauto
  have fne : ∀ v ∈ H.verts, v ≠ j₁ → v ≠ j₂ → φ.f v ≠ a ∧ φ.f v ≠ b := fun v hv h1 h2 =>
    ⟨fun h => h1 (φ.f_injOn hv hj₁ h), fun h => h2 (φ.f_injOn hv hj₂ h)⟩
  have restEnds : ∀ z, InEnds (c.filter fun e => !touches a e && !touches b e) z → InEnds c z ∧ z ≠ a ∧ z ≠ b := by
    rintro z ⟨e, he, hz⟩
    rw [List.mem_filter] at he
    simp only [touches, nat_beq_eq_decide, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at he
    refine ⟨⟨e, he.1, hz⟩, ?_, ?_⟩ <;> rcases hz with rfl | rfl <;> tauto
  have endsCl : ∀ z, InEnds ((c.filter fun e => !touches a e && !touches b e) ++ addL) z →
      InEnds c z ∧ z ≠ a ∧ z ≠ b := by
    intro z hz
    rcases inEnds_append.mp hz with hz | ⟨e, he, hz⟩
    · exact restEnds z hz
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := haddL e he
      rcases hz with rfl | rfl
      · exact ⟨h1, h3, h4⟩
      · exact ⟨h2, h5, h6⟩
  refine ⟨φ.f, φ.g, fun v hv => φ.gf v ((memC v).mp hv).1, fun z hz => φ.fg z (endsCl z hz).1, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨hvH, hv1, hv2⟩ := (memC v).mp hv
    obtain ⟨fa, fb⟩ := fne v hvH hv1 hv2
    obtain ⟨w, hw, hvw⟩ := exists_adj_of_deg hvH (hdeg v hvH hv1 hv2)
    rw [φ.mult_eq v hvH w hw] at hvw
    by_cases hw1 : w = j₁
    · subst hw1
      exact inEnds_append.mpr (Or.inr (hcov _ (φ.fv v hvH) fa fb (Or.inl hvw)))
    by_cases hw2 : w = j₂
    · subst hw2
      exact inEnds_append.mpr (Or.inr (hcov _ (φ.fv v hvH) fa fb (Or.inr hvw)))
    obtain ⟨wa, wb⟩ := fne w hw hw1 hw2
    refine inEnds_append.mpr (Or.inl (inEnds_iff.mpr ⟨φ.f w, ?_⟩))
    rw [mult_filter_ab c a b _ _ fa fb wa wb]; exact hvw
  · intro z hz
    obtain ⟨hz, za, zb⟩ := endsCl z hz
    refine (memC _).mpr ⟨φ.gv z hz, fun h => za ?_, fun h => zb ?_⟩
    · rw [← φ.fg z hz, h]
    · rw [← φ.fg z hz, h]
  · intro u hu v hv
    obtain ⟨huH, hu1, hu2⟩ := (memC u).mp hu
    obtain ⟨hvH, hv1, hv2⟩ := (memC v).mp hv
    obtain ⟨ua, ub⟩ := fne u huH hu1 hu2
    obtain ⟨va, vb⟩ := fne v hvH hv1 hv2
    have hnj : ¬ (j₁ ∈ s(u, v) ∨ j₂ ∈ s(u, v)) := by
      simp only [Sym2.mem_iff, not_or]
      exact ⟨⟨Ne.symm hu1, Ne.symm hv1⟩, Ne.symm hu2, Ne.symm hv2⟩
    show (if j₁ ∈ s(u, v) ∨ j₂ ∈ s(u, v) then 0 else H.mult s(u, v)) +
      (addL.map fun e => s(φ.g e.1, φ.g e.2) : Multiset (Sym2 V)).count s(u, v) = _
    rw [if_neg hnj, φ.mult_eq u huH v hvH, mult_append, mult_filter_ab c a b _ _ ua ub va vb]
    congr 1
    rw [Multiset.coe_count, List.count, List.countP_map, mult]
    -- the added bonds correspond
    have key : ∀ e ∈ addL, (s(u, v) = s(φ.g e.1, φ.g e.2) ↔ isPair (φ.f u) (φ.f v) e = true) := by
      intro e he
      obtain ⟨h1, h2, -⟩ := haddL e he
      rw [isPair_iff_sym2]
      constructor
      · intro h
        have := congrArg (Sym2.map φ.f) h
        simp only [Sym2.map_mk, φ.fg _ h1, φ.fg _ h2] at this
        exact this.symm
      · intro h
        have := congrArg (Sym2.map φ.g) h
        simp only [Sym2.map_mk, φ.gf u huH, φ.gf v hvH] at this
        exact this.symm
    rw [List.countP_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro e he
    by_cases h : isPair (φ.f u) (φ.f v) e = true
    · rw [h]; simp only [Function.comp, beq_iff_eq]; exact ((key e he).mpr h).symm
    · have : ¬ s(u, v) = s(φ.g e.1, φ.g e.2) := fun hh => h ((key e he).mp hh)
      rw [Bool.not_eq_true] at h
      rw [h]; simp only [Function.comp, beq_eq_false_iff_ne, ne_eq]; exact fun hh => this hh.symm

/-! ## `tvineB` is sound -/

theorem count_nbrs_ne_zero {c : Edges} {a z : ℕ} (h : mult c z a ≠ 0) : z ∈ nbrs c a := by
  rw [mult_comm, ← count_nbrs] at h
  exact List.count_pos_iff.mp (Nat.pos_of_ne_zero h)

theorem inEnds_of_mem_nbrs {c : Edges} {a z : ℕ} (h : z ∈ nbrs c a) : InEnds c z := by
  have := List.count_pos_iff.mpr h
  rw [count_nbrs] at this
  exact (inEnds_of_mult_ne_zero (by omega : mult c a z ≠ 0)).2

/-- **Soundness of `tvineB`.** -/
theorem isTVineU_of_tvineB {H : UMultigraph V} {c : Edges} (φ : Iso H c) {j₁ j₂ : V} (hB : IsBlockU H j₁ j₂)
    (hb : tvineB c (φ.f j₁) (φ.f j₂) = true) : IsTVineU H j₁ j₂ := by
  have hB' := hB
  obtain ⟨hj₁, hj₂, hj, -, -, hd, -⟩ := hB'
  have hdeg : ∀ v ∈ H.verts, v ≠ j₁ → v ≠ j₂ → Core.deg H v ≠ 0 := fun v hv h1 h2 => by
    rw [hd v hv h1 h2]; omega
  have ha := φ.fv j₁ hj₁; have hb' := φ.fv j₂ hj₂
  have hab : φ.f j₁ ≠ φ.f j₂ := fun h => hj (φ.f_injOn hj₁ hj₂ h)
  unfold tvineB at hb
  rw [Bool.and_eq_true] at hb
  obtain ⟨hm2, hb⟩ := hb
  refine ⟨hB, fun u hu v hv _ => ?_, ?_⟩
  · rw [φ.mult_eq u hu v hv]
    by_cases h0 : mult c (φ.f u) (φ.f v) = 0
    · omega
    · exact multLe2_le hm2 h0
  split at hb
  · exact absurd hb (by simp)
  rename_i cl hcl
  rw [Bool.and_eq_true] at hb
  obtain ⟨hloop, hdt⟩ := hb
  set a := φ.f j₁ with ha_def
  set b := φ.f j₂ with hb_def
  -- the reduction of the closure, once its isomorphism is known
  have finish : ∀ (added : Multiset (Sym2 V)) (hadd : ∀ e ∈ added, ∀ x ∈ e, x ∈ H.verts ∧ x ≠ j₁ ∧ x ≠ j₂),
      Iso (closureGraph H j₁ j₂ added hadd) cl → (closureGraph H j₁ j₂ added hadd).Loopless ∧
        ReducesToT (closureGraph H j₁ j₂ added hadd) := by
    intro added hadd ψ
    refine ⟨fun v => ?_, ?_⟩
    · by_cases hv : v ∈ (closureGraph H j₁ j₂ added hadd).verts
      · rw [ψ.mult_eq v hv v hv]; exact mult_zero_of_loopless hloop _
      · exact ψ.mult_eq_zero_of_not_mem hv
    · obtain ⟨C', hC', ⟨ψ'⟩⟩ := y2Greedy_sound 16 ψ
      exact ⟨C', hC', isDoubledTriangle_sound ψ' hdt⟩
  unfold closure at hcl
  simp only at hcl
  split at hcl
  · -- σ = 0
    rename_i x₁ y₁ x₂ y₂ hσ hn₁ hn₂
    split_ifs at hcl with hbad
    simp only [Option.some.injEq] at hcl
    subst hcl
    have hx₁a : x₁ ≠ a := by intro h; apply hbad; simp [h]
    have hx₁b : x₁ ≠ b := by intro h; apply hbad; simp [h]
    have hy₁a : y₁ ≠ a := by intro h; apply hbad; simp [h]
    have hy₁b : y₁ ≠ b := by intro h; apply hbad; simp [h]
    have hx₂a : x₂ ≠ a := by intro h; apply hbad; simp [h]
    have hx₂b : x₂ ≠ b := by intro h; apply hbad; simp [h]
    have hy₂a : y₂ ≠ a := by intro h; apply hbad; simp [h]
    have hy₂b : y₂ ≠ b := by intro h; apply hbad; simp [h]
    have m₁ : ∀ z, z ∈ [x₁, y₁] → InEnds c z := fun z hz => inEnds_of_mem_nbrs (hn₁ ▸ hz)
    have m₂ : ∀ z, z ∈ [x₂, y₂] → InEnds c z := fun z hz => inEnds_of_mem_nbrs (hn₂ ▸ hz)
    have e₁ := m₁ x₁ (by simp); have e₁' := m₁ y₁ (by simp)
    have e₂ := m₂ x₂ (by simp); have e₂' := m₂ y₂ (by simp)
    have gne : ∀ z, InEnds c z → z ≠ a → z ≠ b → φ.g z ∈ H.verts ∧ φ.g z ≠ j₁ ∧ φ.g z ≠ j₂ :=
      fun z hz h1 h2 => ⟨φ.gv z hz, fun h => h1 (by rw [← φ.fg z hz, h]), fun h => h2 (by rw [← φ.fg z hz, h])⟩
    have hadd : ∀ e ∈ ([(x₁, y₁), (x₂, y₂)].map fun e => s(φ.g e.1, φ.g e.2) : Multiset (Sym2 V)), ∀ x ∈ e,
        x ∈ H.verts ∧ x ≠ j₁ ∧ x ≠ j₂ := by
      intro e he x hx
      simp only [Multiset.mem_coe, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with he | he <;> rw [he] at hx <;> rcases Sym2.mem_iff.mp hx with h | h <;> rw [h]
      · exact gne _ e₁ hx₁a hx₁b
      · exact gne _ e₁' hy₁a hy₁b
      · exact gne _ e₂ hx₂a hx₂b
      · exact gne _ e₂' hy₂a hy₂b
    have ψ := iso_closureGraph φ hj₁ hj₂ hdeg [(x₁, y₁), (x₂, y₂)] (by
        intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact ⟨e₁, e₁', hx₁a, hx₁b, hy₁a, hy₁b⟩
        · exact ⟨e₂, e₂', hx₂a, hx₂b, hy₂a, hy₂b⟩)
      (by
        intro z _ _ _ hz
        rcases hz with hz | hz
        · have := count_nbrs_ne_zero hz
          rw [hn₁] at this
          simp only [List.mem_cons, List.not_mem_nil, or_false] at this
          rcases this with h | h
          · exact ⟨(x₁, y₁), by simp, Or.inl h.symm⟩
          · exact ⟨(x₁, y₁), by simp, Or.inr h.symm⟩
        · have := count_nbrs_ne_zero hz
          rw [hn₂] at this
          simp only [List.mem_cons, List.not_mem_nil, or_false] at this
          rcases this with h | h
          · exact ⟨(x₂, y₂), by simp, Or.inl h.symm⟩
          · exact ⟨(x₂, y₂), by simp, Or.inr h.symm⟩) hadd
    obtain ⟨hL, hR⟩ := finish _ hadd ψ
    refine ⟨closureGraph H j₁ j₂ _ hadd, ⟨by rw [φ.mult_eq j₁ hj₁ j₂ hj₂, hσ]; omega, rfl, hL,
      _, Or.inl ⟨by rw [φ.mult_eq j₁ hj₁ j₂ hj₂, hσ], φ.g x₁, φ.g y₁, φ.g x₂, φ.g y₂, ?_, ?_, ?_⟩,
      fun e => rfl⟩, hR⟩
    · rw [nbrsU_eq φ hj₁ ({x₁, y₁} : Multiset ℕ) (fun z => by rw [hn₁, ← Multiset.coe_count]; rfl) (by rw [← ha_def]; simp [Ne.symm hx₁a, Ne.symm hy₁a])
        (fun z hz => m₁ z (by simpa using hz))]
      simp
    · rw [nbrsU_eq φ hj₂ ({x₂, y₂} : Multiset ℕ) (fun z => by rw [hn₂, ← Multiset.coe_count]; rfl) (by rw [← hb_def]; simp [Ne.symm hx₂b, Ne.symm hy₂b])
        (fun z hz => m₂ z (by simpa using hz))]
      simp
    · rfl
  · -- σ = 1
    rename_i n₁ n₂ hσ
    split at hcl
    · rename_i x y hx hy
      split_ifs at hcl with hbad
      simp only [Option.some.injEq] at hcl
      subst hcl
      have hxa : x ≠ a := by intro h; apply hbad; simp [h]
      have hxb : x ≠ b := by intro h; apply hbad; simp [h]
      have hya : y ≠ a := by intro h; apply hbad; simp [h]
      have hyb : y ≠ b := by intro h; apply hbad; simp [h]
      have hA : ∀ z, z ≠ b → mult c a z = if z = x then 1 else 0 := fun z hz => mult_of_nbrs_filter hx hz
      have hBm : ∀ z, z ≠ a → mult c b z = if z = y then 1 else 0 := fun z hz => mult_of_nbrs_filter hy hz
      have ex : InEnds c x := (inEnds_of_mult_ne_zero (show mult c a x ≠ 0 by rw [hA x hxb]; simp)).2
      have ey : InEnds c y := (inEnds_of_mult_ne_zero (show mult c b y ≠ 0 by rw [hBm y hya]; simp)).2
      have gne : ∀ z, InEnds c z → z ≠ a → z ≠ b → φ.g z ∈ H.verts ∧ φ.g z ≠ j₁ ∧ φ.g z ≠ j₂ :=
        fun z hz h1 h2 => ⟨φ.gv z hz, fun h => h1 (by rw [← φ.fg z hz, h]), fun h => h2 (by rw [← φ.fg z hz, h])⟩
      have hadd : ∀ e ∈ ([(x, y)].map fun e => s(φ.g e.1, φ.g e.2) : Multiset (Sym2 V)), ∀ z ∈ e,
          z ∈ H.verts ∧ z ≠ j₁ ∧ z ≠ j₂ := by
        intro e he z hz
        simp only [Multiset.mem_coe, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
          or_false] at he
        subst he
        rcases Sym2.mem_iff.mp hz with rfl | rfl
        · exact gne _ ex hxa hxb
        · exact gne _ ey hya hyb
      have ψ := iso_closureGraph φ hj₁ hj₂ hdeg [(x, y)] (by
          intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          subst he; exact ⟨ex, ey, hxa, hxb, hya, hyb⟩)
        (by
          intro z _ hza hzb hz
          rcases hz with hz | hz
          · rw [mult_comm, hA z hzb] at hz
            have : z = x := by by_contra hh; rw [if_neg hh] at hz; exact hz rfl
            exact ⟨(x, y), by simp, Or.inl this.symm⟩
          · rw [mult_comm, hBm z hza] at hz
            have : z = y := by by_contra hh; rw [if_neg hh] at hz; exact hz rfl
            exact ⟨(x, y), by simp, Or.inr this.symm⟩) hadd
      obtain ⟨hL, hR⟩ := finish _ hadd ψ
      have hσ' : H.mult s(j₁, j₂) = 1 := by rw [φ.mult_eq j₁ hj₁ j₂ hj₂]; exact hσ
      have hgb : φ.g b = j₂ := φ.gf j₂ hj₂
      have hga : φ.g a = j₁ := φ.gf j₁ hj₁
      refine ⟨closureGraph H j₁ j₂ _ hadd, ⟨by omega, rfl, hL,
        _, Or.inr ⟨hσ', φ.g x, φ.g y, ?_, ?_, ?_⟩, fun e => rfl⟩, hR⟩
      · rw [nbrsU_eq φ hj₁ ({b, x} : Multiset ℕ) (fun z => ?_) (by rw [← ha_def]; simp [hab, Ne.symm hab, Ne.symm hxa])
          (fun z hz => by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
                          rcases hz with rfl | rfl
                          · exact hb'
                          · exact ex)]
        · simp [hgb]
        · rw [count_nbrs, count_pair]
          by_cases hz : z = b
          · subst hz; rw [hσ]; simp [Ne.symm hxb]
          · rw [hA z hz]; simp [hz]
      · rw [nbrsU_eq φ hj₂ ({a, y} : Multiset ℕ) (fun z => ?_) (by rw [← hb_def]; simp [hab, Ne.symm hab, Ne.symm hyb])
          (fun z hz => by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
                          rcases hz with rfl | rfl
                          · exact ha
                          · exact ey)]
        · simp [hga]
        · rw [count_nbrs, count_pair]
          by_cases hz : z = a
          · subst hz; rw [mult_comm, hσ]; simp [Ne.symm hya]
          · rw [hBm z hz]; simp [hz]
      · rfl
    · exact absurd hcl (by simp)
  · exact absurd hcl (by simp)

end WaveTurbulence.TVine.Checker
