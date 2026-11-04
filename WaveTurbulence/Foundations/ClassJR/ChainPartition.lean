/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.ClassJR.Chain2
public import WaveTurbulence.Foundations.ClassJR.LegalPartitions

/-!
# Catalan codes are the legal partitions

DH21 Def 4.4 (L739–L740) defines legal partitions as non-crossing pairings; REG-STRUCT's
`PairPartition` / `PairPartition.Legal` (copied in `LegalPartitions.lean`) formalizes them. This file
bridges them to the Catalan codes `LegalCode` used in Lemmas 5.9–5.10 (`Chain.lean`, `Chain2.lean`):
* `LegalCode.partner c o` is the partner involution of the code placed at the positions
  `o, …, o + 2m - 1`, and `LegalCode.toPartition c : PairPartition (2 * c.size)` is legal
  (`toPartition_legal`);
* every legal pair partition of `{0, …, n-1}` is `toPartition c` for exactly one code
  (`exists_code_of_legal`, `partner_inj`); this is DH21 Prop 4.5(2) (L741–L749);
* the pairs of a code, listed in preorder (pair `q + k` is the `k`-th), have the left endpoints
  `pairLeft`, which increase strictly (`pairLeft_strictMono`): the preorder is DH21's increasing
  order of the smaller elements (§5.2);
* every pair is listed (`exists_pairLeft`), and `adjSet` is exactly the set of adjacent pairs
  `{a, a+1}` (`mem_adjSet_iff`).
-/

public section

namespace WaveTurbulence.ClassJR

namespace LegalCode

/-- The partner of the position `x` when the code `c` occupies the positions `o, …, o+2m-1`
(identity outside). -/
@[expose] def partner : LegalCode → ℕ → ℕ → ℕ
  | nil, _, x => x
  | node i r, o, x =>
    if x = o then o + 2 * i.size + 1
    else if x = o + 2 * i.size + 1 then o
    else if x < o + 2 * i.size + 1 then i.partner (o + 1) x
    else r.partner (o + 2 * i.size + 2) x

theorem partner_out : ∀ (c : LegalCode) (o x : ℕ), (x < o ∨ o + 2 * c.size ≤ x) →
    c.partner o x = x
  | nil, o, x, _ => rfl
  | node i r, o, x, h => by
    have hs : (node i r).size = i.size + r.size + 1 := rfl
    rw [hs] at h
    simp only [partner]
    split_ifs with h1 h2 h3
    · omega
    · omega
    · exact partner_out i (o + 1) x (by omega)
    · exact partner_out r _ x (by omega)

theorem partner_node_o (i r : LegalCode) (o : ℕ) :
    (node i r).partner o o = o + 2 * i.size + 1 := by
  simp [partner]

theorem partner_node_m (i r : LegalCode) (o : ℕ) :
    (node i r).partner o (o + 2 * i.size + 1) = o := by
  simp only [partner]; split_ifs <;> first | rfl | omega

theorem partner_node_inner {i r : LegalCode} {o x : ℕ} (h1 : o < x) (h2 : x < o + 2 * i.size + 1) :
    (node i r).partner o x = i.partner (o + 1) x := by
  simp only [partner]; split_ifs <;> first | rfl | omega

theorem partner_node_rest {i r : LegalCode} {o x : ℕ} (h : o + 2 * i.size + 1 < x) :
    (node i r).partner o x = r.partner (o + 2 * i.size + 2) x := by
  simp only [partner]; split_ifs <;> first | rfl | omega

/-- The partner map is a fixed-point-free involution of the positions. -/
theorem partner_spec : ∀ (c : LegalCode) (o x : ℕ), o ≤ x → x < o + 2 * c.size →
    o ≤ c.partner o x ∧ c.partner o x < o + 2 * c.size ∧ c.partner o x ≠ x ∧
      c.partner o (c.partner o x) = x
  | nil, o, x, h1, h2 => by simp [size] at h2; omega
  | node i r, o, x, h1, h2 => by
    have hs : (node i r).size = i.size + r.size + 1 := rfl
    rw [hs] at h2 ⊢
    by_cases hx : x = o
    · subst hx
      rw [partner_node_o, partner_node_m]
      exact ⟨by omega, by omega, by omega, rfl⟩
    by_cases hm : x = o + 2 * i.size + 1
    · subst hm
      rw [partner_node_m, partner_node_o]
      exact ⟨le_rfl, by omega, by omega, rfl⟩
    by_cases hlt : x < o + 2 * i.size + 1
    · obtain ⟨a1, a2, a3, a4⟩ := partner_spec i (o + 1) x (by omega) (by omega)
      rw [partner_node_inner (by omega) hlt, partner_node_inner (by omega) (by omega), a4]
      exact ⟨by omega, by omega, a3, rfl⟩
    · obtain ⟨a1, a2, a3, a4⟩ := partner_spec r (o + 2 * i.size + 2) x (by omega) (by omega)
      rw [partner_node_rest (by omega), partner_node_rest (by omega), a4]
      exact ⟨by omega, by omega, a3, rfl⟩

/-- **The pairs of a code do not cross** (DH21 Def 4.4). -/
theorem partner_noncrossing : ∀ (c : LegalCode) (o a b x d : ℕ), o ≤ a → a < b → b < x → x < d →
    d < o + 2 * c.size → c.partner o a = x → c.partner o b = d → False
  | nil, o, a, b, x, d, h0, _, _, _, hd, _, _ => by simp [size] at hd; omega
  | node i r, o, a, b, x, d, h0, hab, hbx, hxd, hd, ha, hb => by
    have hs : (node i r).size = i.size + r.size + 1 := rfl
    rw [hs] at hd
    by_cases ha0 : a = o
    · subst ha0
      rw [partner_node_o] at ha
      subst ha
      rw [partner_node_inner (by omega) (by omega)] at hb
      have := partner_spec i (a + 1) b (by omega) (by omega)
      omega
    by_cases ham : a = o + 2 * i.size + 1
    · subst ham
      rw [partner_node_m] at ha
      omega
    by_cases hai : a < o + 2 * i.size + 1
    · rw [partner_node_inner (by omega) hai] at ha
      have hx := partner_spec i (o + 1) a (by omega) (by omega)
      rw [ha] at hx
      rw [partner_node_inner (by omega) (by omega)] at hb
      have hd' := partner_spec i (o + 1) b (by omega) (by omega)
      rw [hb] at hd'
      exact partner_noncrossing i (o + 1) a b x d (by omega) hab hbx hxd (by omega) ha hb
    · rw [partner_node_rest (by omega)] at ha hb
      exact partner_noncrossing r _ a b x d (by omega) hab hbx hxd (by omega) ha hb

/-- **The legal partition of a code.** -/
@[expose] def toPartition (c : LegalCode) : PairPartition (2 * c.size) where
  pair x := ⟨c.partner 0 x, by
    have := (partner_spec c 0 x.val (Nat.zero_le _) (by simp)).2.1; simpa using this⟩
  involutive x := Fin.ext (partner_spec c 0 x.val (Nat.zero_le _) (by simp)).2.2.2
  no_fixed x h := (partner_spec c 0 x.val (Nat.zero_le _) (by simp)).2.2.1
    (congrArg Fin.val h)

theorem toPartition_pair (c : LegalCode) (x : Fin (2 * c.size)) :
    (c.toPartition.pair x).val = c.partner 0 x.val := rfl

/-- **The partition of a code is legal** (DH21 Def 4.4). -/
theorem toPartition_legal (c : LegalCode) : c.toPartition.Legal := by
  intro a b x d hab hbx hxd ha hb
  exact partner_noncrossing c 0 a b x d (Nat.zero_le _) hab hbx hxd (by simp)
    (congrArg Fin.val ha) (congrArg Fin.val hb)

/-- **Uniqueness of the code** of a partner map. -/
theorem partner_inj : ∀ (c c' : LegalCode) (o : ℕ), c.size = c'.size →
    (∀ x, o ≤ x → x < o + 2 * c.size → c.partner o x = c'.partner o x) → c = c'
  | nil, nil, _, _, _ => rfl
  | nil, node _ _, _, h, _ => by simp [size] at h
  | node _ _, nil, _, h, _ => by simp [size] at h
  | node i r, node i' r', o, h, he => by
    have hs : (node i r).size = i.size + r.size + 1 := rfl
    have hs' : (node i' r').size = i'.size + r'.size + 1 := rfl
    rw [hs, hs'] at h
    have h0 := he o le_rfl (by rw [hs]; omega)
    rw [partner_node_o, partner_node_o] at h0
    have hi : i.size = i'.size := by omega
    have hr : r.size = r'.size := by omega
    have e1 : i = i' := partner_inj i i' (o + 1) hi fun x hx1 hx2 => by
      have := he x (by omega) (by rw [hs]; omega)
      rwa [partner_node_inner (by omega) (by omega),
        partner_node_inner (by omega) (by omega)] at this
    have e2 : r = r' := partner_inj r r' (o + 2 * i.size + 2) hr fun x hx1 hx2 => by
      have := he x (by omega) (by rw [hs]; omega)
      rw [partner_node_rest (by omega), partner_node_rest (by omega), ← hi] at this
      exact this
    rw [e1, e2]

/-- **Every non-crossing perfect matching of `o, …, o+n-1` is the partner map of a code**
(DH21 Prop 4.5(2)). -/
theorem exists_code_of_matching : ∀ (n o : ℕ) (f : ℕ → ℕ),
    (∀ x, o ≤ x → x < o + n → o ≤ f x ∧ f x < o + n ∧ f x ≠ x ∧ f (f x) = x) →
    (∀ a b x d, o ≤ a → a < b → b < x → x < d → d < o + n → f a = x → f b = d → False) →
    ∃ c : LegalCode, 2 * c.size = n ∧ ∀ x, o ≤ x → x < o + n → c.partner o x = f x := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro o f hf hnc
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨nil, rfl, fun x h1 h2 => by omega⟩
    set b := f o with hb
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hf o le_rfl (by omega)
    have hob : o < b := by omega
    -- the inner block `(o, b)` is closed under `f`
    have hin : ∀ y, o < y → y < b → o < f y ∧ f y < b := by
      intro y h1 h2
      obtain ⟨y1, y2, y3, y4⟩ := hf y (by omega) (by omega)
      have hne0 : f y ≠ o := fun h => by rw [← h, y4] at hb; omega
      have hneb : f y ≠ b := fun h => by
        have := congrArg f h; rw [y4, hb, hb4] at this; omega
      refine ⟨by omega, ?_⟩
      by_contra hc
      exact hnc o y b (f y) le_rfl h1 h2 (by omega) y2 hb.symm rfl
    -- the rest block `(b, o+n)` is closed under `f`
    have hre : ∀ y, b < y → y < o + n → b < f y := by
      intro y h1 h2
      obtain ⟨y1, y2, y3, y4⟩ := hf y (by omega) (by omega)
      have hne0 : f y ≠ o := fun h => by rw [← h, y4] at hb; omega
      have hneb : f y ≠ b := fun h => by
        have := congrArg f h; rw [y4, hb, hb4] at this; omega
      by_contra hc
      have := hin (f y) (by omega) (by omega)
      rw [y4] at this; omega
    obtain ⟨ci, hci, hci'⟩ := ih (b - o - 1) (by omega) (o + 1) f
      (fun x h1 h2 => by
        obtain ⟨_, _, x3, x4⟩ := hf x (by omega) (by omega)
        have := hin x (by omega) (by omega)
        exact ⟨by omega, by omega, x3, x4⟩)
      (fun a b' x d h1 h2 h3 h4 h5 h6 h7 => hnc a b' x d (by omega) h2 h3 h4 (by omega) h6 h7)
    obtain ⟨cr, hcr, hcr'⟩ := ih (o + n - b - 1) (by omega) (b + 1) f
      (fun x h1 h2 => by
        obtain ⟨_, x2, x3, x4⟩ := hf x (by omega) (by omega)
        have := hre x (by omega) (by omega)
        exact ⟨by omega, by omega, x3, x4⟩)
      (fun a b' x d h1 h2 h3 h4 h5 h6 h7 => hnc a b' x d (by omega) h2 h3 h4 (by omega) h6 h7)
    have hsz : o + 2 * ci.size + 1 = b := by omega
    refine ⟨node ci cr, by simp only [size]; omega, fun x h1 h2 => ?_⟩
    by_cases hx : x = o
    · subst hx; rw [partner_node_o, hsz]
    by_cases hxb : x = b
    · subst hxb; rw [← hsz, partner_node_m, hsz]; exact hb4.symm
    by_cases hlt : x < b
    · rw [partner_node_inner (by omega) (by omega)]
      exact hci' x (by omega) (by omega)
    · rw [partner_node_rest (by omega)]
      have e : o + 2 * ci.size + 2 = b + 1 := by omega
      rw [e]
      exact hcr' x (by omega) (by omega)

/-- **Every legal partition is the partition of a unique code** (DH21 Prop 4.5(2)). -/
theorem exists_code_of_legal {n : ℕ} (P : PairPartition n) (hP : P.Legal) :
    ∃ c : LegalCode, 2 * c.size = n ∧ ∀ x : Fin n, (P.pair x).val = c.partner 0 x.val := by
  let f : ℕ → ℕ := fun x => if h : x < n then (P.pair ⟨x, h⟩).val else x
  have hf : ∀ x (h : x < n), f x = (P.pair ⟨x, h⟩).val := fun x h => by simp [f, h]
  obtain ⟨c, hc, hc'⟩ := exists_code_of_matching n 0 f
    (fun x _ h2 => by
      rw [hf x (by omega)]
      refine ⟨Nat.zero_le _, by simp, fun h => ?_, ?_⟩
      · exact P.no_fixed ⟨x, by omega⟩ (Fin.ext h)
      · rw [hf _ (P.pair ⟨x, by omega⟩).isLt]
        simp only [Fin.eta]
        rw [P.involutive])
    (fun a b x d _ hab hbx hxd hd ha hb => by
      rw [hf a (by omega)] at ha
      rw [hf b (by omega)] at hb
      exact hP ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨x, by omega⟩ ⟨d, by omega⟩ hab hbx hxd
        (Fin.ext ha) (Fin.ext hb))
  exact ⟨c, hc, fun x => by rw [hc' x.val (Nat.zero_le _) (by simp), hf x.val x.isLt]⟩

/-! ### The pairs in preorder -/

/-- The left endpoint of the pair `j` (pairs `q, q+1, …` in preorder) of the code at offset `o`. -/
@[expose] def pairLeft : LegalCode → ℕ → ℕ → ℕ → ℕ
  | nil, o, _, _ => o
  | node i r, o, q, j =>
    if j = q then o
    else if j < q + 1 + i.size then i.pairLeft (o + 1) (q + 1) j
    else r.pairLeft (o + 2 * i.size + 2) (q + i.size + 1) j

theorem pairLeft_node_q (i r : LegalCode) (o q : ℕ) : (node i r).pairLeft o q q = o := by
  simp [pairLeft]

theorem pairLeft_node_inner {i r : LegalCode} {o q j : ℕ} (h1 : q < j) (h2 : j < q + 1 + i.size) :
    (node i r).pairLeft o q j = i.pairLeft (o + 1) (q + 1) j := by
  simp only [pairLeft]; split_ifs <;> first | rfl | omega

theorem pairLeft_node_rest {i r : LegalCode} {o q j : ℕ} (h : q + 1 + i.size ≤ j) :
    (node i r).pairLeft o q j = r.pairLeft (o + 2 * i.size + 2) (q + i.size + 1) j := by
  simp only [pairLeft]; split_ifs <;> first | rfl | omega

theorem pairLeft_spec : ∀ (c : LegalCode) (o q j : ℕ), q ≤ j → j < q + c.size →
    o ≤ c.pairLeft o q j ∧ c.pairLeft o q j < c.partner o (c.pairLeft o q j)
  | nil, _, q, j, h1, h2 => by simp [size] at h2; omega
  | node i r, o, q, j, h1, h2 => by
    have hs : (node i r).size = i.size + r.size + 1 := rfl
    rw [hs] at h2
    by_cases hj : j = q
    · subst hj; rw [pairLeft_node_q, partner_node_o]; omega
    by_cases hji : j < q + 1 + i.size
    · rw [pairLeft_node_inner (by omega) hji]
      obtain ⟨a1, a2⟩ := pairLeft_spec i (o + 1) (q + 1) j (by omega) (by omega)
      have hlt : i.pairLeft (o + 1) (q + 1) j < o + 1 + 2 * i.size := by
        by_contra hc
        rw [partner_out i (o + 1) _ (Or.inr (by omega))] at a2; omega
      rw [partner_node_inner (by omega) (by omega)]
      exact ⟨by omega, a2⟩
    · rw [pairLeft_node_rest (by omega)]
      obtain ⟨a1, a2⟩ := pairLeft_spec r (o + 2 * i.size + 2) (q + i.size + 1) j (by omega) (by omega)
      rw [partner_node_rest (by omega)]
      exact ⟨by omega, a2⟩

theorem pairLeft_lt (c : LegalCode) (o q j : ℕ) (h1 : q ≤ j) (h2 : j < q + c.size) :
    c.pairLeft o q j < o + 2 * c.size := by
  obtain ⟨a1, a2⟩ := pairLeft_spec c o q j h1 h2
  by_contra hc
  rw [partner_out c o _ (Or.inr (by omega))] at a2; omega

/-- **The preorder of the pairs is the increasing order of their smaller elements** (DH21 §5.2). -/
theorem pairLeft_strictMono : ∀ (c : LegalCode) (o q j j' : ℕ), q ≤ j → j < j' → j' < q + c.size →
    c.pairLeft o q j < c.pairLeft o q j'
  | nil, _, q, j, j', h1, h2, h3 => by simp [size] at h3; omega
  | node i r, o, q, j, j', h1, h2, h3 => by
    have hs : (node i r).size = i.size + r.size + 1 := rfl
    rw [hs] at h3
    by_cases hj : j = q
    · subst hj
      rw [pairLeft_node_q]
      by_cases h : j' < j + 1 + i.size
      · rw [pairLeft_node_inner (by omega) h]
        have := (pairLeft_spec i (o + 1) (j + 1) j' (by omega) (by omega)).1; omega
      · rw [pairLeft_node_rest (by omega)]
        have := (pairLeft_spec r (o + 2 * i.size + 2) (j + i.size + 1) j' (by omega) (by omega)).1
        omega
    by_cases ha : j < q + 1 + i.size
    · rw [pairLeft_node_inner (by omega) ha]
      by_cases hb : j' < q + 1 + i.size
      · rw [pairLeft_node_inner (by omega) hb]
        exact pairLeft_strictMono i (o + 1) (q + 1) j j' (by omega) h2 (by omega)
      · rw [pairLeft_node_rest (by omega)]
        have := pairLeft_lt i (o + 1) (q + 1) j (by omega) (by omega)
        have := (pairLeft_spec r (o + 2 * i.size + 2) (q + i.size + 1) j' (by omega)
          (by omega)).1
        omega
    · rw [pairLeft_node_rest (by omega), pairLeft_node_rest (by omega)]
      exact pairLeft_strictMono r _ _ j j' (by omega) h2 (by omega)

/-- **Every pair is listed**: each smaller element of a pair is the left endpoint of some pair. -/
theorem exists_pairLeft : ∀ (c : LegalCode) (o q x : ℕ), o ≤ x → x < c.partner o x →
    ∃ j, q ≤ j ∧ j < q + c.size ∧ c.pairLeft o q j = x
  | nil, o, q, x, _, h => by simp [partner] at h
  | node i r, o, q, x, h1, h2 => by
    have hs : (node i r).size = i.size + r.size + 1 := rfl
    by_cases hx : x = o
    · subst hx; exact ⟨q, le_rfl, by rw [hs]; omega, pairLeft_node_q i r x q⟩
    have hxe : x < o + 2 * (node i r).size := by
      by_contra hc; rw [partner_out _ o x (Or.inr (by omega))] at h2; omega
    rw [hs] at hxe
    by_cases hm : x = o + 2 * i.size + 1
    · subst hm; rw [partner_node_m] at h2; omega
    by_cases hlt : x < o + 2 * i.size + 1
    · rw [partner_node_inner (by omega) hlt] at h2
      obtain ⟨j, j1, j2, j3⟩ := exists_pairLeft i (o + 1) (q + 1) x (by omega) h2
      exact ⟨j, by omega, by rw [hs]; omega, by rw [pairLeft_node_inner (by omega) (by omega), j3]⟩
    · rw [partner_node_rest (by omega)] at h2
      obtain ⟨j, j1, j2, j3⟩ := exists_pairLeft r _ (q + i.size + 1) x (by omega) h2
      exact ⟨j, by omega, by rw [hs]; omega, by rw [pairLeft_node_rest (by omega), j3]⟩

end LegalCode

open LegalCode in
/-- **`adjSet` is the set of adjacent pairs** `{a, a+1}` (DH21 Lemma 5.10). -/
theorem mem_adjSet_iff : ∀ (c : LegalCode) (o q j : ℕ), q ≤ j → j < q + c.size →
    (j ∈ adjSet c q ↔ c.partner o (c.pairLeft o q j) = c.pairLeft o q j + 1)
  | .nil, _, q, j, _, h2 => by simp [size] at h2; omega
  | .node i r, o, q, j, h1, h2 => by
    have hs : (node i r).size = i.size + r.size + 1 := rfl
    rw [hs] at h2
    by_cases hj : j = q
    · subst hj
      rw [pairLeft_node_q, partner_node_o]
      cases i with
      | nil => simp [adjSet, size]
      | node a b =>
        have : j ∉ adjSet (.node (.node a b) r) j := by
          simp only [adjSet, Finset.mem_union, not_or]
          exact ⟨fun h => by have := mem_adjSet _ _ _ h; omega,
            fun h => by have := mem_adjSet _ _ _ h; omega⟩
        simp only [this, false_iff, size]; omega
    by_cases hji : j < q + 1 + i.size
    · rw [pairLeft_node_inner (by omega) hji]
      have hl1 := (pairLeft_spec i (o + 1) (q + 1) j (by omega) (by omega)).1
      have hl2 := pairLeft_lt i (o + 1) (q + 1) j (by omega) (by omega)
      rw [partner_node_inner (by omega) (by omega), ← mem_adjSet_iff i (o + 1) (q + 1) j (by omega)
        (by omega)]
      cases i with
      | nil => simp [size] at hji; omega
      | node a b =>
        simp only [adjSet, Finset.mem_union]
        constructor
        · rintro (h | h)
          · exact h
          · have := mem_adjSet _ _ _ h; simp only [size] at this hji ⊢; omega
        · exact Or.inl
    · rw [pairLeft_node_rest (by omega)]
      have hl1 := (pairLeft_spec r (o + 2 * i.size + 2) (q + i.size + 1) j (by omega) (by omega)).1
      rw [partner_node_rest (by omega), ← mem_adjSet_iff r _ (q + i.size + 1) j (by omega)
        (by omega)]
      cases i with
      | nil => simp [adjSet, size, hj]
      | node a b =>
        simp only [adjSet, Finset.mem_union]
        constructor
        · rintro (h | h)
          · have := mem_adjSet _ _ _ h; simp only [size] at this hji ⊢; omega
          · exact h
        · exact Or.inr

end WaveTurbulence.ClassJR
