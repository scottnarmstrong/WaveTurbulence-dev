/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.CodeDefs

/-!
# Variables of chains of regular couple codes

For a chain `X` (sign `ζ`, root `a`) whose pairs sit at the positions `q, q+1, …` of a list `L` of pair
data (`ChainAgr`), the variables of `ClassJR.chainT` are the chosen nodes of the chain links
(`chainVarsF_eq`). They are distinct when the chosen nodes are (`chainDisjF_of_nodup`). The chain limit
`chainL` is `chainJ` (`chainL_eq_chainJ`).
-/

@[expose] public section

namespace WaveTurbulence.Cancel

open TTree WaveTurbulence.Reg WaveTurbulence.ClassJR WaveTurbulence.Links

theorem chosenSet_nil : chosenSet ([] : List (Addr × Addr)) = ∅ := rfl

theorem chosenSet_cons (l : Addr × Addr) (L : List (Addr × Addr)) :
    chosenSet (l :: L) = insert l.1 (chosenSet L) := by
  simp [chosenSet]

theorem chosenSet_append (L₁ L₂ : List (Addr × Addr)) :
    chosenSet (L₁ ++ L₂) = chosenSet L₁ ∪ chosenSet L₂ := by
  simp [chosenSet, List.toFinset_append]

theorem disjoint_chosenSet_of_nodup {L₁ L₂ : List (Addr × Addr)}
    (h : ((L₁ ++ L₂).map Prod.fst).Nodup) : Disjoint (chosenSet L₁) (chosenSet L₂) := by
  rw [List.map_append, List.nodup_append] at h
  rw [Finset.disjoint_left]
  intro x h₁ h₂
  simp only [chosenSet, List.mem_toFinset] at h₁ h₂
  exact h.2.2 x h₁ x h₂ rfl

/-- The variables of a pair: the chosen nodes of its red and green couples. -/
def pairVars (d : PairDatum) : Finset Addr :=
  chosenSet (d.2.1.1.linksAt d.2.1.2.1 d.2.1.2.2) ∪ chosenSet (d.2.2.1.linksAt d.2.2.2.1 d.2.2.2.2)

/-- The chain `X` sits at the positions `q, q+1, …` of `L`. -/
def ChainAgr (L : List PairDatum) (X : RegChain) (ζ : ℤˣ) (a : Addr) (q : ℕ) : Prop :=
  ∀ k < (chainCode X).size, L.getD (q + k) dfltP = (chainData X ζ a).getD k dfltP

theorem ChainAgr.head {L : List PairDatum} {m : MiniTreeCode} {Qr Qg : RegCpl} {i r : RegChain}
    {ζ : ℤˣ} {a : Addr} {q : ℕ} (h : ChainAgr L (.pair m Qr Qg i r) ζ a q) :
    L.getD q dfltP = (a, (Qr, redRoots m ζ a i), (Qg, greenRoots m ζ a i)) := by
  have := h 0 (by simp [chainCode, LegalCode.size])
  simpa [chainData] using this

theorem ChainAgr.inner {L : List PairDatum} {m : MiniTreeCode} {Qr Qg : RegCpl} {i r : RegChain}
    {ζ : ℤˣ} {a : Addr} {q : ℕ} (h : ChainAgr L (.pair m Qr Qg i r) ζ a q) :
    ChainAgr L i (slotSign ζ m.c) (addrExt a [m.c]) (q + 1) := by
  intro k hk
  have := h (k + 1) (by simp only [chainCode, LegalCode.size]; omega)
  rw [show q + 1 + k = q + (k + 1) by omega, this]
  simp only [chainData, List.getD_cons_succ]
  rw [List.getD_append _ _ _ _ (by rw [length_chainData]; exact hk)]

theorem ChainAgr.rest {L : List PairDatum} {m : MiniTreeCode} {Qr Qg : RegCpl} {i r : RegChain}
    {ζ : ℤˣ} {a : Addr} {q : ℕ} (h : ChainAgr L (.pair m Qr Qg i r) ζ a q) :
    ChainAgr L r (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))
      (q + (chainCode i).size + 1) := by
  intro k hk
  have := h ((chainCode i).size + k + 1) (by simp only [chainCode, LegalCode.size]; omega)
  rw [show q + (chainCode i).size + 1 + k = q + ((chainCode i).size + k + 1) by omega, this]
  simp only [chainData, List.getD_cons_succ]
  rw [List.getD_append_right _ _ _ _ (by rw [length_chainData]; omega), length_chainData,
    Nat.add_sub_cancel_left]

/-- **The variables of a chain are the chosen nodes of its links.** -/
theorem chainVarsF_eq (L : List PairDatum) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr) (q : ℕ), ChainAgr L X ζ a q →
      chainVarsF (chainSig L) (fun j => pairVars (L.getD j dfltP)) (chainCode X) q =
        chosenSet (X.linksAt ζ a)
  | .nil, _, _, _, _ => rfl
  | .pair m Qr Qg i r, ζ, a, q, h => by
    have hi := chainVarsF_eq L i _ _ _ h.inner
    have hr := chainVarsF_eq L r _ _ _ h.rest
    simp only [chainCode, chainVarsF]
    rw [hi, hr, linksAt_pair, chosenSet_cons, chosenSet_append, chosenSet_append, chosenSet_append]
    simp only [chainSig, h.head, pairVars]

/-- **The variables of the factors of a chain are distinct.** -/
theorem chainDisjF_of_nodup (L : List PairDatum) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr) (q : ℕ), ChainAgr L X ζ a q →
      ((X.linksAt ζ a).map Prod.fst).Nodup →
      ChainDisjF (chainSig L) (fun j => pairVars (L.getD j dfltP)) (chainCode X) q
  | .nil, _, _, _, _, _ => trivial
  | .pair m Qr Qg i r, ζ, a, q, h, hnd => by
    rw [linksAt_pair] at hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    have h1 := hnd
    rw [List.map_append, List.map_append, List.map_append] at h1
    have h1a := (List.nodup_append.1 h1).1
    have h1b := (List.nodup_append.1 h1a).1
    have hrg : Disjoint (chosenSet (Qr.linksAt (redRoots m ζ a i).1 (redRoots m ζ a i).2))
        (chosenSet (Qg.linksAt (greenRoots m ζ a i).1 (greenRoots m ζ a i).2)) := by
      refine disjoint_chosenSet_of_nodup ?_
      rw [List.map_append]; exact h1b
    have hgi := disjoint_chosenSet_of_nodup (L₁ := Qr.linksAt (redRoots m ζ a i).1 (redRoots m ζ a i).2 ++
      Qg.linksAt (greenRoots m ζ a i).1 (greenRoots m ζ a i).2)
      (L₂ := i.linksAt (slotSign ζ m.c) (addrExt a [m.c]))
      (by rw [List.map_append, List.map_append]; exact h1a)
    have hri := disjoint_chosenSet_of_nodup (L₁ := Qr.linksAt (redRoots m ζ a i).1 (redRoots m ζ a i).2 ++
      Qg.linksAt (greenRoots m ζ a i).1 (greenRoots m ζ a i).2 ++ i.linksAt (slotSign ζ m.c) (addrExt a [m.c]))
      (L₂ := r.linksAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ i.lonePath ++ [m.lone])))
      (by rw [List.map_append, List.map_append, List.map_append]; exact h1)
    have hndi : ((i.linksAt (slotSign ζ m.c) (addrExt a [m.c])).map Prod.fst).Nodup :=
      (List.nodup_append.1 h1a).2.1
    have hndr : ((r.linksAt (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ i.lonePath ++ [m.lone]))).map Prod.fst).Nodup := (List.nodup_append.1 h1).2.1
    simp only [chainCode, ChainDisjF]
    rw [chainVarsF_eq L i _ _ _ h.inner, chainVarsF_eq L r _ _ _ h.rest]
    simp only [chainSig, h.head, pairVars]
    rw [chosenSet_append, chosenSet_append] at hri
    rw [chosenSet_append] at hgi
    refine ⟨?_, ?_, ?_, chainDisjF_of_nodup L i _ _ _ h.inner hndi,
      chainDisjF_of_nodup L r _ _ _ h.rest hndr⟩
    · intro hmem
      apply ha
      simp only [Finset.mem_union, chosenSet, List.mem_toFinset] at hmem
      simp only [List.map_append, List.mem_append]
      tauto
    · exact hgi
    · exact hri

/-- The limit of a pair: the product of the limits of its red and green couples on the diagonal. -/
noncomputable def pairJ (Z : Finset Addr) (d : PairDatum) (τ : ℝ) : ℂ :=
  cplJ Z d.2.1.1 d.2.1.2.1 d.2.1.2.2 τ τ * cplJ Z d.2.2.1 d.2.2.2.1 d.2.2.2.2 τ τ

/-- **The chain limit `chainL` of the regularized chain is `chainJ`.** -/
theorem chainL_eq_chainJ (Z : Finset Addr) (L : List PairDatum) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr) (q : ℕ), ChainAgr L X ζ a q → ∀ (t : ℝ) (g : ℝ → ℂ),
      chainL (kD (fun j => decide (chainSig L j ∈ Z)) (fun j τ _ => pairJ Z (L.getD j dfltP) τ))
        (chainCode X) q t g = chainJ Z X ζ a t g
  | .nil, _, _, _, _, _, _ => rfl
  | .pair m Qr Qg .nil r, ζ, a, q, h, t, g => by
    have hr := chainL_eq_chainJ Z L r _ _ _ h.rest
    simp only [chainCode, LegalCode.size, add_zero] at hr
    show (∫ τ in (0 : ℝ)..t, kD (fun j => decide (chainSig L j ∈ Z))
        (fun j τ _ => pairJ Z (L.getD j dfltP) τ) q τ *
        chainL (kD (fun j => decide (chainSig L j ∈ Z)) (fun j τ _ => pairJ Z (L.getD j dfltP) τ))
          (chainCode r) (q + 1) τ g) = ∫ τ in (0 : ℝ)..t, (if a ∈ Z then (-1 : ℂ) else 1) *
        (cplJ Z Qr (redRoots m ζ a .nil).1 (redRoots m ζ a .nil).2 τ τ *
          cplJ Z Qg (greenRoots m ζ a .nil).1 (greenRoots m ζ a .nil).2 τ τ) *
        chainJ Z r (slotSign (slotSign ζ m.c) m.lone)
          (addrExt a ([m.c] ++ RegChain.nil.lonePath ++ [m.lone])) τ g
    refine intervalIntegral.integral_congr fun τ _ => ?_
    rw [hr τ g]
    simp only [kD, chainSig, h.head, pairJ, sg]
    by_cases ha : a ∈ Z <;> simp [ha]
  | .pair _ _ _ (.pair _ _ _ _ _) _, _, _, _, _, _, _ => rfl

end WaveTurbulence.Cancel
