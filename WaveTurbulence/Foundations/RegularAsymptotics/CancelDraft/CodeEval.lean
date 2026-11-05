/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.CodeMain

/-!
# Evaluation of the limits (DH21 Props 7.4, 7.5)

* `cplJ_eq_zero`: **non-dominant codes have limit `0`** (DH21 Prop 7.4). Either a non-dominant
  subcouple has limit `0`, or a chain has a non-adjacent pair, which gives `0` (DH21 Lemma 7.1).
* `cplJ_eq_JB`: **a dominant code with a special `Z` has limit `(-1)^{|Z|} 𝒥ℬ_Q`** (DH21 Prop 7.5,
  corrected by F61). Here `𝒥ℬ_Q` is B2's `RegCpl.JB 0`, the recursion (recurtype1)/(recurtype2). A
  special `Z` contains no type 1 root (C5's `cplSpecial`). Each chain pair in `Z` contributes `-1`.
-/

@[expose] public section

namespace WaveTurbulence.Cancel

open TTree WaveTurbulence.Reg WaveTurbulence.ClassJR WaveTurbulence.Links Set

/-! ### Non-dominant codes -/

theorem chainJ_zero_cont (Z : Finset Addr) : ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr),
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ g : ℝ → ℂ, (∀ x ∈ Icc (0 : ℝ) 1, g x = 0) → chainJ Z X ζ a t g = 0
  | .nil, _, _, t, ht, g, hg => hg t ht
  | .pair m Qr Qg .nil r, ζ, a, t, ht, g, hg => by
    simp only [chainJ]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun τ hτ => ?_]
    · simp
    · rw [uIcc_of_le ht.1] at hτ
      simp only
      rw [chainJ_zero_cont Z r _ _ τ ⟨hτ.1, hτ.2.trans ht.2⟩ g hg, mul_zero]
  | .pair _ _ _ (.pair _ _ _ _ _) _, _, _, _, _, _, _ => rfl

mutual
/-- **DH21 Prop 7.4 (limit form)**: the limit of a non-dominant code vanishes on the square. -/
theorem cplJ_eq_zero (Z : Finset Addr) : ∀ (Q : RegCpl) (a b : Addr), Q.dominant = false →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, cplJ Z Q a b t s = 0
  | .triv, _, _, h, _, _, _, _ => by simp [RegCpl.dominant] at h
  | .type1 c Q₁ Q₂ Q₃, a, b, h, t, ht, s, hs => by
    simp only [RegCpl.dominant, Bool.and_eq_false_iff] at h
    simp only [cplJ]
    split_ifs
    · rfl
    · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun τ hτ => ?_]
      · simp
      · rw [uIcc_of_le (le_min ht.1 hs.1)] at hτ
        have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ((min_le_left _ _).trans ht.2)⟩
        simp only
        rcases h with (h | h) | h
        · rw [cplJ_eq_zero Z Q₁ _ _ h τ hτ' τ hτ']; ring
        · rw [cplJ_eq_zero Z Q₂ _ _ h τ hτ' τ hτ']; ring
        · rw [cplJ_eq_zero Z Q₃ _ _ h τ hτ' τ hτ']; ring
  | .type2 Xp Xm Qlp, a, b, h, t, ht, s, hs => by
    simp only [RegCpl.dominant, Bool.and_eq_false_iff] at h
    simp only [cplJ]
    rcases h with (h | h) | h
    · exact chainJ_eq_zero Z Xp 1 a h t ht _
    · exact chainJ_zero_cont Z Xp 1 a t ht _ fun t' _ => chainJ_eq_zero Z Xm (-1) b h s hs _
    · exact chainJ_zero_cont Z Xp 1 a t ht _ fun t' ht' => chainJ_zero_cont Z Xm (-1) b s hs _
        fun s' hs' => cplJ_eq_zero Z Qlp _ _ h t' ht' s' hs'

/-- A non-dominant chain has limit `0`. -/
theorem chainJ_eq_zero (Z : Finset Addr) : ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr), X.dominant = false →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ g : ℝ → ℂ, chainJ Z X ζ a t g = 0
  | .nil, _, _, h, _, _, _ => by simp [RegChain.dominant] at h
  | .pair m Qr Qg .nil r, ζ, a, h, t, ht, g => by
    simp only [RegChain.dominant, RegChain.isNil, Bool.true_and, Bool.and_eq_false_iff] at h
    simp only [chainJ]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) fun τ hτ => ?_]
    · simp
    · rw [uIcc_of_le ht.1] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ht.2⟩
      simp only
      rcases h with (h | h) | h
      · rw [cplJ_eq_zero Z Qr _ _ h τ hτ' τ hτ']; ring
      · rw [cplJ_eq_zero Z Qg _ _ h τ hτ' τ hτ']; ring
      · rw [chainJ_eq_zero Z r _ _ h τ hτ' g]; ring
  | .pair _ _ _ (.pair _ _ _ _ _) _, _, _, _, _, _, _ => rfl
end

end WaveTurbulence.Cancel

/-! ### Dominant codes -/

namespace WaveTurbulence.Cancel

open TTree WaveTurbulence.Reg WaveTurbulence.ClassJR WaveTurbulence.Links Set

theorem chainSpecial_pair (m : MiniTreeCode) (Qr Qg : RegCpl) (i r : RegChain) (ζ : ℤˣ) (a : Addr) :
    chainSpecial (.pair m Qr Qg i r) ζ a = (if i.isNil then [a] else []) ++
      (cplSpecial Qr (redRoots m ζ a i).1 (redRoots m ζ a i).2 ++
        cplSpecial Qg (greenRoots m ζ a i).1 (greenRoots m ζ a i).2 ++
        chainSpecial i (slotSign ζ m.c) (addrExt a [m.c]) ++
        chainSpecial r (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))) := by
  simp only [chainSpecial, redRoots, greenRoots]
  split_ifs <;> rfl

theorem mem_chosenSet_of_cplSpecial {Q : RegCpl} {a b : Addr} {z : Addr} (h : z ∈ cplSpecial Q a b) :
    z ∈ chosenSet (Q.linksAt a b) :=
  List.mem_toFinset.2 ((cplSpecial_sublist Q a b).subset h)

theorem mem_chosenSet_of_chainSpecial {X : RegChain} {ζ : ℤˣ} {a : Addr} {z : Addr}
    (h : z ∈ chainSpecial X ζ a) : z ∈ chosenSet (X.linksAt ζ a) :=
  List.mem_toFinset.2 ((chainSpecial_sublist X ζ a).subset h)

theorem card_inter_union {Z A B : Finset Addr} (h : Disjoint A B) :
    (Z ∩ (A ∪ B)).card = (Z ∩ A).card + (Z ∩ B).card := by
  rw [Finset.inter_union_distrib_left, Finset.card_union_of_disjoint]
  exact Finset.disjoint_of_subset_left Finset.inter_subset_right
    (Finset.disjoint_of_subset_right Finset.inter_subset_right h)

theorem card_inter_insert {Z X : Finset Addr} {a : Addr} (ha : a ∉ X) :
    (Z ∩ insert a X).card = (if a ∈ Z then 1 else 0) + (Z ∩ X).card := by
  by_cases haZ : a ∈ Z
  · rw [Finset.inter_insert_of_mem haZ, Finset.card_insert_of_notMem (fun h => ha (Finset.mem_inter.1 h).2)]
    simp [haZ]; ring
  · rw [Finset.inter_insert_of_notMem haZ]; simp [haZ]

theorem disjoint_chosen_cons {l : Addr × Addr} {L : List (Addr × Addr)}
    (h : ((l :: L).map Prod.fst).Nodup) : l.1 ∉ chosenSet L := by
  simp only [List.map_cons, List.nodup_cons] at h
  simpa [chosenSet] using h.1

mutual
/-- **DH21 Prop 7.5 (limit form), corrected (F61)**: a dominant code with a special `Z` has limit
`(-1)^{|Z|} 𝒥ℬ_Q` on the square. -/
theorem cplJ_eq_JB (Z : Finset Addr) : ∀ (Q : RegCpl) (a b : Addr), Q.dominant = true →
    ((Q.linksAt a b).map Prod.fst).Nodup →
    (∀ z ∈ Z, z ∈ chosenSet (Q.linksAt a b) → z ∈ cplSpecial Q a b) →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      cplJ Z Q a b t s = (-1) ^ (Z ∩ chosenSet (Q.linksAt a b)).card * (Q.JB 0 t s : ℂ)
  | .triv, _, _, _, _, _, _, _, _, _ => by simp [cplJ, RegCpl.JB, RegCpl.linksAt, chosenSet]
  | .type1 c Q₁ Q₂ Q₃, a, b, hd, hnd, hsp, t, ht, s, hs => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at hd
    obtain ⟨⟨hd1, hd2⟩, hd3⟩ := hd
    set L₁ := Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])
    set L₂ := Q₂.linksAt (addrExt b [1]) (addrExt a [1])
    set L₃ := Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])
    have hL : (RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b = (a, b) :: (L₁ ++ L₂ ++ L₃) := rfl
    have hSp : cplSpecial (RegCpl.type1 c Q₁ Q₂ Q₃) a b =
        cplSpecial Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) ++
          cplSpecial Q₂ (addrExt b [1]) (addrExt a [1]) ++
          cplSpecial Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) := rfl
    rw [hL] at hnd hsp ⊢
    rw [hSp] at hsp
    have ha := disjoint_chosen_cons hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨-, hnd⟩ := hnd
    have h12 := nodup_of_append_left hnd
    have hd12 : Disjoint (chosenSet L₁) (chosenSet L₂) := disjoint_chosenSet_of_nodup h12
    have hd123 : Disjoint (chosenSet L₁ ∪ chosenSet L₂) (chosenSet L₃) := by
      rw [← chosenSet_append]; exact disjoint_chosenSet_of_nodup hnd
    rw [chosenSet_append, chosenSet_append] at ha
    -- the root is not in `Z`
    have haZ : a ∉ Z := by
      intro haZ
      have := hsp a haZ (by simp [chosenSet])
      simp only [List.mem_append] at this
      rcases this with (h | h) | h
      · exact ha (Finset.mem_union_left _ (Finset.mem_union_left _ (mem_chosenSet_of_cplSpecial h)))
      · exact ha (Finset.mem_union_left _ (Finset.mem_union_right _ (mem_chosenSet_of_cplSpecial h)))
      · exact ha (Finset.mem_union_right _ (mem_chosenSet_of_cplSpecial h))
    have hmem : ∀ z ∈ Z, ∀ (x : Finset Addr), x ⊆ chosenSet L₁ ∪ chosenSet L₂ ∪ chosenSet L₃ →
        z ∈ x → z ∈ chosenSet ((a, b) :: (L₁ ++ L₂ ++ L₃)) := by
      intro z _ x hx hz
      rw [chosenSet_cons, chosenSet_append, chosenSet_append]
      exact Finset.mem_insert_of_mem (hx hz)
    have hs1 : ∀ z ∈ Z, z ∈ chosenSet L₁ → z ∈ cplSpecial Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) := by
      intro z hz h1
      have := hsp z hz (hmem z hz _ (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h)) h1)
      simp only [List.mem_append] at this
      rcases this with (h | h) | h
      · exact h
      · exact absurd (mem_chosenSet_of_cplSpecial h) (Finset.disjoint_left.1 hd12 h1)
      · exact absurd (mem_chosenSet_of_cplSpecial h)
          (Finset.disjoint_left.1 hd123 (Finset.mem_union_left _ h1))
    have hs2 : ∀ z ∈ Z, z ∈ chosenSet L₂ → z ∈ cplSpecial Q₂ (addrExt b [1]) (addrExt a [1]) := by
      intro z hz h2
      have := hsp z hz (hmem z hz _ (fun _ h => Finset.mem_union_left _ (Finset.mem_union_right _ h)) h2)
      simp only [List.mem_append] at this
      rcases this with (h | h) | h
      · exact absurd h2 (Finset.disjoint_left.1 hd12 (mem_chosenSet_of_cplSpecial h))
      · exact h
      · exact absurd (mem_chosenSet_of_cplSpecial h)
          (Finset.disjoint_left.1 hd123 (Finset.mem_union_right _ h2))
    have hs3 : ∀ z ∈ Z, z ∈ chosenSet L₃ → z ∈ cplSpecial Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) := by
      intro z hz h3
      have := hsp z hz (hmem z hz _ (fun _ h => Finset.mem_union_right _ h) h3)
      simp only [List.mem_append] at this
      rcases this with (h | h) | h
      · exact absurd h3 (Finset.disjoint_left.1 hd123
          (Finset.mem_union_left _ (mem_chosenSet_of_cplSpecial h)))
      · exact absurd h3 (Finset.disjoint_left.1 hd123
          (Finset.mem_union_right _ (mem_chosenSet_of_cplSpecial h)))
      · exact h
    have hcard : (Z ∩ chosenSet ((a, b) :: (L₁ ++ L₂ ++ L₃))).card =
        (Z ∩ chosenSet L₁).card + (Z ∩ chosenSet L₂).card + (Z ∩ chosenSet L₃).card := by
      rw [chosenSet_cons, chosenSet_append, chosenSet_append, card_inter_insert ha,
        card_inter_union hd123, card_inter_union hd12]
      simp [haZ]
    simp only [cplJ, haZ, ite_false, RegCpl.JB]
    rw [hcard]
    have hint : ∫ τ in (0 : ℝ)..min t s, cplJ Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) τ τ *
        cplJ Z Q₂ (addrExt b [1]) (addrExt a [1]) τ τ * cplJ Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) τ τ =
        ∫ τ in (0 : ℝ)..min t s, (-1 : ℂ) ^ ((Z ∩ chosenSet L₁).card + (Z ∩ chosenSet L₂).card +
          (Z ∩ chosenSet L₃).card) * ((Q₁.JB 0 τ τ * Q₂.JB 0 τ τ * Q₃.JB 0 τ τ : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le (le_min ht.1 hs.1)] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ((min_le_left _ _).trans ht.2)⟩
      rw [cplJ_eq_JB Z Q₁ _ _ hd1 (nodup_of_append_left h12) hs1 τ hτ' τ hτ',
        cplJ_eq_JB Z Q₂ _ _ hd2 (nodup_of_append_right h12) hs2 τ hτ' τ hτ',
        cplJ_eq_JB Z Q₃ _ _ hd3 (nodup_of_append_right hnd) hs3 τ hτ' τ hτ', pow_add, pow_add]
      push_cast; ring
    rw [hint, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    push_cast; ring
  | .type2 Xp Xm Qlp, a, b, hd, hnd, hsp, t, ht, s, hs => by
    simp only [RegCpl.dominant, Bool.and_eq_true] at hd
    obtain ⟨⟨hdp, hdm⟩, hdl⟩ := hd
    set Lp := Xp.linksAt 1 a
    set Lm := Xm.linksAt (-1) b
    set Ll := Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)
    have hL : (RegCpl.type2 Xp Xm Qlp).linksAt a b = Lp ++ Lm ++ Ll := rfl
    have hSp : cplSpecial (RegCpl.type2 Xp Xm Qlp) a b = chainSpecial Xp 1 a ++ chainSpecial Xm (-1) b ++
        cplSpecial Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) := rfl
    rw [hL] at hnd hsp ⊢
    rw [hSp] at hsp
    have hpm := nodup_of_append_left hnd
    have hndp := nodup_of_append_left hpm
    have hndm := nodup_of_append_right hpm
    have hndl := nodup_of_append_right hnd
    have hd12 : Disjoint (chosenSet Lp) (chosenSet Lm) := disjoint_chosenSet_of_nodup hpm
    have hd123 : Disjoint (chosenSet Lp ∪ chosenSet Lm) (chosenSet Ll) := by
      rw [← chosenSet_append]; exact disjoint_chosenSet_of_nodup hnd
    have hcs : chosenSet (Lp ++ Lm ++ Ll) = chosenSet Lp ∪ chosenSet Lm ∪ chosenSet Ll := by
      rw [chosenSet_append, chosenSet_append]
    have hsp1 : ∀ z ∈ Z, z ∈ chosenSet Lp → z ∈ chainSpecial Xp 1 a := by
      intro z hz h1
      have := hsp z hz (by rw [hcs]; exact Finset.mem_union_left _ (Finset.mem_union_left _ h1))
      simp only [List.mem_append] at this
      rcases this with (h | h) | h
      · exact h
      · exact absurd (mem_chosenSet_of_chainSpecial h) (Finset.disjoint_left.1 hd12 h1)
      · exact absurd (mem_chosenSet_of_cplSpecial h)
          (Finset.disjoint_left.1 hd123 (Finset.mem_union_left _ h1))
    have hsp2 : ∀ z ∈ Z, z ∈ chosenSet Lm → z ∈ chainSpecial Xm (-1) b := by
      intro z hz h2
      have := hsp z hz (by rw [hcs]; exact Finset.mem_union_left _ (Finset.mem_union_right _ h2))
      simp only [List.mem_append] at this
      rcases this with (h | h) | h
      · exact absurd h2 (Finset.disjoint_left.1 hd12 (mem_chosenSet_of_chainSpecial h))
      · exact h
      · exact absurd (mem_chosenSet_of_cplSpecial h)
          (Finset.disjoint_left.1 hd123 (Finset.mem_union_right _ h2))
    have hsp3 : ∀ z ∈ Z, z ∈ chosenSet Ll → z ∈ cplSpecial Qlp (addrExt a Xp.lonePath)
        (addrExt b Xm.lonePath) := by
      intro z hz h3
      have := hsp z hz (by rw [hcs]; exact Finset.mem_union_right _ h3)
      simp only [List.mem_append] at this
      rcases this with (h | h) | h
      · exact absurd h3 (Finset.disjoint_left.1 hd123
          (Finset.mem_union_left _ (mem_chosenSet_of_chainSpecial h)))
      · exact absurd h3 (Finset.disjoint_left.1 hd123
          (Finset.mem_union_right _ (mem_chosenSet_of_chainSpecial h)))
      · exact h
    have hcard : (Z ∩ chosenSet (Lp ++ Lm ++ Ll)).card =
        (Z ∩ chosenSet Lp).card + (Z ∩ chosenSet Lm).card + (Z ∩ chosenSet Ll).card := by
      rw [hcs, card_inter_union hd123, card_inter_union hd12]
    have hin : ∀ t' ∈ Icc (0 : ℝ) 1, chainJ Z Xm (-1) b s
        (fun s' => cplJ Z Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) t' s') =
        ((-1 : ℂ) ^ (Z ∩ chosenSet Ll).card * (-1) ^ (Z ∩ chosenSet Lm).card) *
          (Xm.JBchain 0 0 s (fun sm => Qlp.JB 0 t' sm) : ℂ) := by
      intro t' ht'
      rw [chainJ_eq_JBchain Z Xm (-1) b hdm hndm hsp2 s hs ((-1) ^ (Z ∩ chosenSet Ll).card)
        (fun s' => Qlp.JB 0 t' s') _ fun x hx => cplJ_eq_JB Z Qlp _ _ hdl hndl hsp3 t' ht' x hx]
    simp only [cplJ, RegCpl.JB]
    rw [chainJ_eq_JBchain Z Xp 1 a hdp hndp hsp1 t ht _ (fun t' => Xm.JBchain 0 0 s fun sm => Qlp.JB 0 t' sm)
      _ hin, hcard, pow_add, pow_add]
    ring

/-- The chain version: `chainJ = c (-1)^{|Z|} 𝒥ℬchain` for a continuation `g = c G`. -/
theorem chainJ_eq_JBchain (Z : Finset Addr) : ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr),
    X.dominant = true → ((X.linksAt ζ a).map Prod.fst).Nodup →
    (∀ z ∈ Z, z ∈ chosenSet (X.linksAt ζ a) → z ∈ chainSpecial X ζ a) →
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ (c : ℂ) (G : ℝ → ℝ) (g : ℝ → ℂ), (∀ x ∈ Icc (0 : ℝ) 1, g x = c * G x) →
      chainJ Z X ζ a t g = c * (-1) ^ (Z ∩ chosenSet (X.linksAt ζ a)).card * (X.JBchain 0 0 t G : ℂ)
  | .nil, _, _, _, _, _, t, ht, c, G, g, hg => by
    simp [chainJ, RegChain.JBchain, RegChain.linksAt, chosenSet, hg t ht]
  | .pair m Qr Qg .nil r, ζ, a, hd, hnd, hsp, t, ht, c, G, g, hg => by
    simp only [RegChain.dominant, RegChain.isNil, Bool.true_and, Bool.and_eq_true] at hd
    obtain ⟨⟨hdr, hdg⟩, hdrest⟩ := hd
    set Lr := Qr.linksAt (redRoots m ζ a .nil).1 (redRoots m ζ a .nil).2
    set Lg := Qg.linksAt (greenRoots m ζ a .nil).1 (greenRoots m ζ a .nil).2
    set Lrest := r.linksAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone]))
    have hLi : RegChain.nil.linksAt (slotSign ζ m.c) (addrExt a [m.c]) = [] := rfl
    have hSi : chainSpecial RegChain.nil (slotSign ζ m.c) (addrExt a [m.c]) = [] := rfl
    rw [linksAt_pair, hLi, List.append_nil] at hnd hsp ⊢
    rw [chainSpecial_pair, hSi, List.append_nil] at hsp
    simp only [RegChain.isNil, ite_true] at hsp
    have ha := disjoint_chosen_cons hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨-, hnd⟩ := hnd
    have h12 := nodup_of_append_left hnd
    have hd12 : Disjoint (chosenSet Lr) (chosenSet Lg) := disjoint_chosenSet_of_nodup h12
    have hd123 : Disjoint (chosenSet Lr ∪ chosenSet Lg) (chosenSet Lrest) := by
      rw [← chosenSet_append]; exact disjoint_chosenSet_of_nodup hnd
    rw [chosenSet_append, chosenSet_append] at ha
    have hcs : chosenSet ((a, addrExt a ([m.c] ++ RegChain.nil.lonePath)) :: (Lr ++ Lg ++ Lrest)) =
        insert a (chosenSet Lr ∪ chosenSet Lg ∪ chosenSet Lrest) := by
      rw [chosenSet_cons, chosenSet_append, chosenSet_append]
    have hmem : ∀ z, z ∈ chosenSet Lr ∪ chosenSet Lg ∪ chosenSet Lrest →
        z ∈ chosenSet ((a, addrExt a ([m.c] ++ RegChain.nil.lonePath)) :: (Lr ++ Lg ++ Lrest)) := by
      intro z hz; rw [hcs]; exact Finset.mem_insert_of_mem hz
    have ha' : a ∉ chosenSet Lr ∪ chosenSet Lg ∪ chosenSet Lrest := ha
    have hne : ∀ z, z ∈ chosenSet Lr ∪ chosenSet Lg ∪ chosenSet Lrest → z ≠ a := by
      intro z hz h; apply ha'; rw [← h]; exact hz
    have hsp1 : ∀ z ∈ Z, z ∈ chosenSet Lr → z ∈ cplSpecial Qr (redRoots m ζ a .nil).1 (redRoots m ζ a .nil).2 := by
      intro z hz h1
      have h1' : z ∈ chosenSet Lr ∪ chosenSet Lg ∪ chosenSet Lrest :=
        Finset.mem_union_left _ (Finset.mem_union_left _ h1)
      have := hsp z hz (hmem z h1')
      simp only [List.mem_append, List.mem_singleton] at this
      rcases this with h | (h | h) | h
      · exact absurd h (hne z h1')
      · exact h
      · exact absurd (mem_chosenSet_of_cplSpecial h) (Finset.disjoint_left.1 hd12 h1)
      · exact absurd (mem_chosenSet_of_chainSpecial h)
          (Finset.disjoint_left.1 hd123 (Finset.mem_union_left _ h1))
    have hsp2 : ∀ z ∈ Z, z ∈ chosenSet Lg → z ∈ cplSpecial Qg (greenRoots m ζ a .nil).1 (greenRoots m ζ a .nil).2 := by
      intro z hz h2
      have h2' : z ∈ chosenSet Lr ∪ chosenSet Lg ∪ chosenSet Lrest :=
        Finset.mem_union_left _ (Finset.mem_union_right _ h2)
      have := hsp z hz (hmem z h2')
      simp only [List.mem_append, List.mem_singleton] at this
      rcases this with h | (h | h) | h
      · exact absurd h (hne z h2')
      · exact absurd h2 (Finset.disjoint_left.1 hd12 (mem_chosenSet_of_cplSpecial h))
      · exact h
      · exact absurd (mem_chosenSet_of_chainSpecial h)
          (Finset.disjoint_left.1 hd123 (Finset.mem_union_right _ h2))
    have hsp3 : ∀ z ∈ Z, z ∈ chosenSet Lrest → z ∈ chainSpecial r (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone])) := by
      intro z hz h3
      have h3' : z ∈ chosenSet Lr ∪ chosenSet Lg ∪ chosenSet Lrest := Finset.mem_union_right _ h3
      have := hsp z hz (hmem z h3')
      simp only [List.mem_append, List.mem_singleton] at this
      rcases this with h | (h | h) | h
      · exact absurd h (hne z h3')
      · exact absurd h3 (Finset.disjoint_left.1 hd123
          (Finset.mem_union_left _ (mem_chosenSet_of_cplSpecial h)))
      · exact absurd h3 (Finset.disjoint_left.1 hd123
          (Finset.mem_union_right _ (mem_chosenSet_of_cplSpecial h)))
      · exact h
    have hcard : (Z ∩ chosenSet ((a, addrExt a ([m.c] ++ RegChain.nil.lonePath)) :: (Lr ++ Lg ++ Lrest))).card =
        (if a ∈ Z then 1 else 0) + ((Z ∩ chosenSet Lr).card + (Z ∩ chosenSet Lg).card +
          (Z ∩ chosenSet Lrest).card) := by
      rw [hcs, card_inter_insert ha', card_inter_union hd123, card_inter_union hd12]
    have hsgn : (if a ∈ Z then (-1 : ℂ) else 1) = (-1) ^ (if a ∈ Z then 1 else 0) := by
      split_ifs <;> simp
    simp only [chainJ, RegChain.JBchain]
    rw [hcard]
    have hint : ∫ τ in (0 : ℝ)..t, (if a ∈ Z then (-1 : ℂ) else 1) *
        (cplJ Z Qr (redRoots m ζ a .nil).1 (redRoots m ζ a .nil).2 τ τ *
          cplJ Z Qg (greenRoots m ζ a .nil).1 (greenRoots m ζ a .nil).2 τ τ) *
        chainJ Z r (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone])) τ g =
        ∫ τ in (0 : ℝ)..t, (c * (-1) ^ ((if a ∈ Z then 1 else 0) + ((Z ∩ chosenSet Lr).card +
          (Z ∩ chosenSet Lg).card + (Z ∩ chosenSet Lrest).card))) *
          ((Qr.JB 0 τ τ * Qg.JB 0 τ τ * r.JBchain 0 0 τ G : ℝ) : ℂ) := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le ht.1] at hτ
      have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ht.2⟩
      rw [cplJ_eq_JB Z Qr _ _ hdr (nodup_of_append_left h12) hsp1 τ hτ' τ hτ',
        cplJ_eq_JB Z Qg _ _ hdg (nodup_of_append_right h12) hsp2 τ hτ' τ hτ',
        chainJ_eq_JBchain Z r _ _ hdrest (nodup_of_append_right hnd) hsp3 τ hτ' c G g hg, hsgn,
        pow_add, pow_add, pow_add]
      push_cast; ring
    rw [hint, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
  | .pair _ _ _ (.pair _ _ _ _ _) _, _, _, hd, _, _, _, _, _, _, _, _ => by
    simp [RegChain.dominant, RegChain.isNil] at hd
end

end WaveTurbulence.Cancel
