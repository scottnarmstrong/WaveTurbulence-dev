/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Defs
public import WaveTurbulence.Foundations.GammaLow.Famc.Spine.Pieces
public import WaveTurbulence.Foundations.GammaLow.Fama.Splice.Data
public import WaveTurbulence.Foundations.Stage1.ClassCount.VineData
public import WaveTurbulence.Foundations.Molecule.VineBlockJoints
/-! # T-vine bookkeeping for the class count (packet L5c, item I)

Facts about T-vines (D11 `Molecule.IsTVine`) used by the `𝒱_γ` transfer-matrix links of the class count:
* `tvine_card_odd`: a T-vine has `2m + 5` atoms (its closure has `|S| − 2` atoms, each (Y2) move removes two, and the
  doubled triangle has three);
* `pieces_swap`, `pieces_eq_or_disjoint`: the pieces are symmetric in the joints and pairwise disjoint;
* `tvineIncoherency_le`: the incoherency index of a T-vine with `2m + 5` atoms is at most `m + 1` (an incoherent piece
  has two atoms);
* `vineIncoh_tvine`: L5a's `Fama.vineIncoh` of a T-vine is `tvineIncoherency` (a T-vine is not (I)/(II): parity). -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc.ClassCount
open Finset WaveTurbulence WaveTurbulence.TVine

section parity
variable {V : Type*} [DecidableEq V]

theorem y2Step_card {G G' : UMultigraph V} (h : Y2Step G G') : G'.verts.card + 2 = G.verts.card := by
  obtain ⟨a, b, c, d, hab, -, -, -, -, -, h3, -, -, -, -, hv, -⟩ := h
  have hne : G.mult s(a, b) ≠ 0 := by rw [h3]; norm_num
  have ha : a ∈ G.verts := G.supp _ hne a (Sym2.mem_mk_left a b)
  have hb : b ∈ G.verts := G.supp _ hne b (Sym2.mem_mk_right a b)
  have hb' : b ∈ G.verts.erase a := Finset.mem_erase.mpr ⟨fun h => hab h.symm, hb⟩
  rw [hv, Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]
  have : 2 ≤ G.verts.card := by
    have : ({a, b} : Finset V) ⊆ G.verts := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton.mp hx]; exact hb
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hab] at h2; exact h2
  omega

theorem rtg_card {G G' : UMultigraph V} (h : Relation.ReflTransGen Y2Step G G') :
    ∃ k : ℕ, G.verts.card = G'.verts.card + 2 * k := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hs ih =>
    obtain ⟨k, hk⟩ := ih
    have := y2Step_card hs
    exact ⟨k + 1, by omega⟩

theorem doubledTriangle_card {G : UMultigraph V} (h : IsDoubledTriangle G) : G.verts.card = 3 := by
  obtain ⟨a, b, c, hab, hac, hbc, hv, -⟩ := h
  rw [hv, Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]

end parity

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D}

/-- **A T-vine has `2m + 5` atoms.** -/
theorem tvine_card_odd {S : Finset V} {a b : V} (h : M.IsTVine S a b) : ∃ m : ℕ, S.card = 2 * m + 5 := by
  obtain ⟨hB, -, G, G', hcl, hrtg, htri⟩ := h
  obtain ⟨-, hv, -⟩ := hcl
  obtain ⟨k, hk⟩ := rtg_card hrtg
  have h3 := doubledTriangle_card htri
  have ha : a ∈ S := hB.2.1
  have hb : b ∈ S.erase a := Finset.mem_erase.mpr ⟨fun h => hB.2.2.2.1 h.symm, hB.2.2.1⟩
  rw [hv, Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha] at hk
  have : 2 ≤ S.card := by
    have h2 : ({a, b} : Finset V) ⊆ S := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · rw [Finset.mem_singleton.mp hx]; exact hB.2.2.1
    have := Finset.card_le_card h2
    rw [Finset.card_pair hB.2.2.2.1] at this; exact this
  exact ⟨k, by omega⟩

/-- The pieces do not depend on the order of the joints. -/
theorem pieces_swap (S : Finset V) (a b : V) : M.pieces S a b = M.pieces S b a := by
  unfold Molecule.pieces
  rw [Finset.erase_right_comm]

theorem tvineGroups_swap (S : Finset V) (a b : V) : M.tvineGroups S a b = M.tvineGroups S b a :=
  pieces_swap S a b

/-- Every piece is the class of one of its atoms, inside `S ∖ {a, b}`. -/
theorem mem_pieces {S : Finset V} {a b : V} {P : Finset V} (hP : P ∈ M.pieces S a b) :
    ∃ u ∈ (S.erase a).erase b, ∀ w, w ∈ P ↔ w ∈ (S.erase a).erase b ∧ M.SamePiece S u w := by
  classical
  unfold Molecule.pieces at hP
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hP
  exact ⟨u, hu, fun w => by rw [Finset.mem_filter]⟩

theorem pieces_sub {S : Finset V} {a b : V} {P : Finset V} (hP : P ∈ M.pieces S a b) :
    P ⊆ (S.erase a).erase b := by
  obtain ⟨u, -, hu⟩ := mem_pieces hP
  exact fun w hw => ((hu w).mp hw).1

/-- **Distinct pieces are disjoint.** -/
theorem pieces_eq_or_disjoint {S : Finset V} {a b : V} {P Q : Finset V} (hP : P ∈ M.pieces S a b)
    (hQ : Q ∈ M.pieces S a b) : P = Q ∨ Disjoint P Q := by
  by_cases h : Disjoint P Q
  · exact Or.inr h
  · left
    obtain ⟨x, hxP, hxQ⟩ := Finset.not_disjoint_iff.mp h
    obtain ⟨u, -, hu⟩ := mem_pieces hP
    obtain ⟨v, -, hv⟩ := mem_pieces hQ
    have hux := ((hu x).mp hxP).2
    have hvx := ((hv x).mp hxQ).2
    ext w
    rw [hu w, hv w]
    constructor
    · rintro ⟨hw, huw⟩; exact ⟨hw, samePiece_trans M hvx (samePiece_trans M (samePiece_symm M hux) huw)⟩
    · rintro ⟨hw, hvw⟩; exact ⟨hw, samePiece_trans M hux (samePiece_trans M (samePiece_symm M hvx) hvw)⟩

/-- Groups among the pieces satisfying a predicate that forces two atoms number at most half the interior. -/
theorem two_mul_card_filter_pieces_le (S : Finset V) (a b : V) (q : Finset V → Prop) {_ : DecidablePred q}
    (hq : ∀ g, q g → ∃ x ∈ g, ∃ y ∈ g, x ≠ y) :
    2 * ((M.pieces S a b).filter q).card ≤ ((S.erase a).erase b).card := by
  classical
  set Inc := (M.pieces S a b).filter q with hInc
  have hsub : ∀ P ∈ Inc, P ∈ M.pieces S a b := fun P hP => (Finset.mem_filter.mp hP).1
  have htwo : ∀ P ∈ Inc, 2 ≤ P.card := by
    intro P hP
    obtain ⟨x, hx, y, hy, hne⟩ := hq P (Finset.mem_filter.mp hP).2
    have : ({x, y} : Finset V) ⊆ P := by
      intro z hz; rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · rw [Finset.mem_singleton.mp hz]; exact hy
    have h2 := Finset.card_le_card this
    rw [Finset.card_pair hne] at h2; exact h2
  have hdisj : (Inc : Set (Finset V)).PairwiseDisjoint id := by
    intro P hP Q hQ hPQ
    rcases pieces_eq_or_disjoint (hsub P hP) (hsub Q hQ) with h | h
    · exact absurd h hPQ
    · exact h
  have hU : Inc.biUnion id ⊆ (S.erase a).erase b := by
    intro x hx
    obtain ⟨P, hP, hxP⟩ := Finset.mem_biUnion.mp hx
    exact pieces_sub (hsub P hP) hxP
  have hcard := Finset.card_biUnion hdisj
  have hle := Finset.card_le_card hU
  have hsum : 2 * Inc.card ≤ ∑ P ∈ Inc, P.card := by
    rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum htwo
  simp only [id] at hcard
  omega

/-- **The incoherency index of a T-vine is at most half its interior.** -/
theorem tvineIncoherency_two_mul_le (S : Finset V) (a b : V) (layer : V → ℕ) :
    2 * tvineIncoherency M S a b layer ≤ ((S.erase a).erase b).card := by
  unfold tvineIncoherency Molecule.tvineGroups
  refine two_mul_card_filter_pieces_le S a b _ ?_
  intro g hg
  by_contra hc
  push Not at hc
  exact hg fun x hx y hy => by
    by_cases hxy : x = y
    · rw [hxy]
    · exact absurd (hc x hx y hy) (by simpa using hxy)

/-- **For a T-vine with `2m + 5` atoms the incoherency index is at most `m + 1`.** -/
theorem tvineIncoherency_le {S : Finset V} {a b : V} (hT : M.IsTVine S a b) {m : ℕ} (hm : S.card = 2 * m + 5)
    (layer : V → ℕ) : tvineIncoherency M S a b layer ≤ m + 1 := by
  have h := tvineIncoherency_two_mul_le (M := M) S a b layer
  have ha : a ∈ S := hT.1.2.1
  have hb : b ∈ S.erase a := Finset.mem_erase.mpr ⟨fun h => hT.1.2.2.2.1 h.symm, hT.1.2.2.1⟩
  rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha] at h
  omega

/-- The list form of the incoherency index (main `Vine.incoherencyIndex`) of a finset of groups. -/
theorem incoherencyIndex_toList {A : Type*} [DecidableEq A] (layer : A → ℕ) (groups : Finset (Finset A))
    {_ : DecidablePred fun g : Finset A => ¬ ∀ x ∈ g, ∀ y ∈ g, layer x = layer y} :
    Vine.incoherencyIndex layer (groups.toList.map Finset.toList) =
      (groups.filter fun g => ¬ ∀ x ∈ g, ∀ y ∈ g, layer x = layer y).card := by
  unfold Vine.incoherencyIndex
  rw [List.filter_map, List.length_map, Finset.card_def, Finset.filter_val, ← Finset.coe_toList groups,
    Multiset.filter_coe, Multiset.coe_card]
  congr 1
  apply List.filter_congr
  intro g _
  simp [Vine.GroupCoherent]

/-- The joints of a block are determined up to order. -/
theorem joints_cases {p q x y : V} (hpq : p ≠ q) (h : ({p, q} : Finset V) = {x, y}) :
    (p = x ∧ q = y) ∨ (p = y ∧ q = x) := by
  have hp : p ∈ ({x, y} : Finset V) := h ▸ Finset.mem_insert_self p {q}
  have hq : q ∈ ({x, y} : Finset V) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hpq
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hpq

/-- **L5a's `vineIncoh` of a T-vine is its incoherency over its pieces** (`tvineIncoherency`, at either order of
the joints; a T-vine is not (I)/(II) since its cardinality is odd). -/
theorem vineIncoh_tvine (γ : ℝ) [Fact (γ ≤ 1 / 2)] {w : ℕ} (G : Garden w) (layer0 : GBranch G.tree → ℕ)
    {T : Finset (GBranch G.tree)} {x y : GBranch G.tree} (hT : G.molecule.IsTVine T x y) :
    Fama.vineIncoh γ G layer0 T = tvineIncoherency G.molecule T x y layer0 := by
  obtain ⟨m, hm⟩ := tvine_card_odd hT
  have hnb : ¬ ∃ X p q, X.IsBad = true ∧ G.molecule.IsVine X T p q := by
    rintro ⟨X, p, q, hX, hv⟩
    obtain ⟨m', h1, -⟩ := ClassCount.vine_card_m hv
    have := h1 hX; omega
  have hex : ∃ p q, G.molecule.IsTVine T p q := ⟨x, y, hT⟩
  have hgen : ∀ p q, G.molecule.IsTVine T p q → G.molecule.tvineGroups T p q = G.molecule.tvineGroups T x y := by
    intro p q hpq
    rcases joints_cases hpq.1.2.2.2.1 (Vine.block_joints_unique G.molecule hpq.1 hT.1) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2]; exact tvineGroups_swap T y x
  have hgr := hgen _ _ hex.choose_spec.choose_spec
  unfold Fama.vineIncoh
  rw [dif_neg hnb, dif_pos hex, hgr]
  unfold tvineIncoherency
  exact incoherencyIndex_toList layer0 _

end WaveTurbulence.GammaLow.Famc.ClassCount
