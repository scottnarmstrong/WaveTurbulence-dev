/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.CodeTrees
public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.CodeDefs

/-!
# The code-defined `B̃` satisfies wt-torus's recursion hypothesis `BtRec`

wt-torus's DH21 Props 7.4/7.5 (`/home/scott/wt-scratch/cancel`, `CancelDraft.CodeDefs`, sha256
`9081e873…`) consume `B̃_Q` through the named obligation `Cancel.BtRec Bt`: the recursions (newexp1),
(newexp2) on a family `Bt Q a b` over the B2 codes. Here `BtJR Q a b = (toJR Q).Bt a b` is the
code-defined `B̃` of DH21 Prop 5.1 (`ClassJR.RegCpl.maincoef`), and `btRec_BtJR : Cancel.BtRec BtJR`.
The time swaps are `![false, true, false]` (type 1), `swAt` (the pair couples whose `+` root hangs from
`𝔫_b`) and none for the lone pair.
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree

/-- **The code-defined `B̃_Q`** on the B2 codes, with roots `(a, b)`. -/
noncomputable def BtJR (Q : RegCpl) (a b : Cancel.Addr) : Cancel.TCoef := (toJR Q).Bt a b

theorem addrExt_B2 {w : ℕ} (a : Fin w × TTree.Path) (p : TTree.Path) :
    addrExt a p = ClassJR.addrExt a p := rfl

theorem chainCode_eq : ∀ X : RegChain, Cancel.chainCode X = (toJRc X).code
  | .nil => rfl
  | .pair _ _ _ i r => by
    rw [Cancel.chainCode, chainCode_eq i, chainCode_eq r]
    rfl

/-- wt-torus's node sign is ClassJR's. -/
theorem zetaA_eq (v : ClassJR.Addr) : Cancel.zetaA v = ClassJR.nodeSgn v := by
  rcases v with ⟨j, p⟩
  simp only [Cancel.zetaA, nodeSign, TTree.pathSign, ClassJR.nodeSgn, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  fin_cases j <;> simp

/-- `chainT` only depends on the pair variables, signs and coefficients of its own pairs. -/
theorem chainT_congr_Ico {V : Type} : ∀ (c : ClassJR.LegalCode) (q : ℕ) {σ σ' : ℕ → V}
    {ε ε' : ℕ → ℤ} {F F' : ℕ → (V → ℝ) → ℝ → ℝ → ℂ}
    (_ : ∀ j ∈ Set.Ico q (q + c.size), σ j = σ' j) (_ : ∀ j ∈ Set.Ico q (q + c.size), ε j = ε' j)
    (_ : ∀ j ∈ Set.Ico q (q + c.size), F j = F' j) (β : V → ℝ) (t : ℝ) (g : ℝ → ℂ),
    ClassJR.chainT σ ε c q F β t g = ClassJR.chainT σ' ε' c q F' β t g
  | .nil, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | .node i r, q, σ, σ', ε, ε', F, F', hσ, hε, hF, β, t, g => by
    have hsz : (ClassJR.LegalCode.node i r).size = i.size + r.size + 1 := rfl
    rw [hsz] at hσ hε hF
    have hi : ∀ t' g', ClassJR.chainT σ ε i (q + 1) F β t' g' = ClassJR.chainT σ' ε' i (q + 1) F' β t' g' :=
      chainT_congr_Ico i (q + 1) (fun j hj => hσ j (by simp only [Set.mem_Ico] at hj ⊢; omega))
        (fun j hj => hε j (by simp only [Set.mem_Ico] at hj ⊢; omega))
        (fun j hj => hF j (by simp only [Set.mem_Ico] at hj ⊢; omega)) β
    have hr : ∀ t', ClassJR.chainT σ ε r (q + i.size + 1) F β t' g =
        ClassJR.chainT σ' ε' r (q + i.size + 1) F' β t' g := fun t' =>
      chainT_congr_Ico r (q + i.size + 1) (fun j hj => hσ j (by simp only [Set.mem_Ico] at hj ⊢; omega))
        (fun j hj => hε j (by simp only [Set.mem_Ico] at hj ⊢; omega))
        (fun j hj => hF j (by simp only [Set.mem_Ico] at hj ⊢; omega)) β t' g
    have hq : q ∈ Set.Ico q (q + (i.size + r.size + 1)) := by simp only [Set.mem_Ico]; omega
    rw [ClassJR.chainT_node, ClassJR.chainT_node]
    simp only [hi, hr, hσ q hq, hε q hq, hF q hq]

/-- The time swaps of the pair couples of a chain: the couple's times are swapped when its `+` root
hangs from `𝔫_b` (`ClassJR.RegChain.coefAt`). -/
def swAt : RegChain → ℤˣ → ℕ → ℕ → Bool × Bool
  | .nil, _, _ => fun _ => (false, false)
  | .pair m _ _ inner rest, ζ, q => fun j =>
    if j = q then (decide (slotSign ζ m.red.1 ≠ 1), decide (slotSign ζ m.green.1 ≠ 1))
    else if j < q + 1 + (toJRc inner).code.size then swAt inner (slotSign ζ m.c) (q + 1) j
    else swAt rest (slotSign (slotSign ζ m.c) m.lone) (q + (toJRc inner).code.size + 1) j

theorem length_chainData (X : RegChain) (ζ : ℤˣ) (a : Cancel.Addr) :
    (Cancel.chainData X ζ a).length = (toJRc X).code.size := by
  rw [Cancel.length_chainData, chainCode_eq]

/-- The three index ranges of a pair node. -/
theorem pair_cases {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain} {q j : ℕ}
    (hj : j ∈ Set.Ico q (q + (toJRc (.pair m Qr Qg inner rest)).code.size)) :
    j = q ∨ (j ∈ Set.Ico (q + 1) (q + 1 + (toJRc inner).code.size)) ∨
      j ∈ Set.Ico (q + (toJRc inner).code.size + 1)
        (q + (toJRc inner).code.size + 1 + (toJRc rest).code.size) := by
  rw [size_toJRc_pair] at hj
  simp only [Set.mem_Ico] at hj ⊢
  omega

/-- wt-torus's pair variables are the chosen nodes `σ`. -/
theorem chainSig_eq : ∀ (X : RegChain) (ζ : ℤˣ) (a : Cancel.Addr) (q j : ℕ),
    j ∈ Set.Ico q (q + (toJRc X).code.size) →
      Cancel.chainSig (Cancel.chainData X ζ a) (j - q) = (toJRc X).sigmaAt a q j
  | .nil, _, _, q, j, hj => by
    simp only [toJRc, ClassJR.RegChain.code, ClassJR.LegalCode.size, add_zero, Set.mem_Ico] at hj
    omega
  | .pair m Qr Qg inner rest, ζ, a, q, j, hj => by
    rcases pair_cases hj with rfl | hj' | hj'
    · rw [sigmaAt_toJRc_self]
      simp [Cancel.chainSig, Cancel.chainData]
    · have h1 : j - q = (j - (q + 1)) + 1 := by simp only [Set.mem_Ico] at hj'; omega
      have hlt : j - (q + 1) < (Cancel.chainData inner (slotSign ζ m.c) (addrExt a [m.c])).length := by
        rw [length_chainData]; simp only [Set.mem_Ico] at hj'; omega
      rw [sigmaAt_toJRc_inner m Qr Qg inner rest a q hj',
        ← chainSig_eq inner (slotSign ζ m.c) (ClassJR.addrExt a [m.c]) (q + 1) j hj', h1]
      simp only [Cancel.chainSig, Cancel.chainData, List.getD_cons_succ]
      rw [List.getD_append _ _ _ _ hlt]
      rfl
    · have h1 : j - q = (j - (q + 1)) + 1 := by simp only [Set.mem_Ico] at hj'; omega
      have hle : (Cancel.chainData inner (slotSign ζ m.c) (addrExt a [m.c])).length ≤ j - (q + 1) := by
        rw [length_chainData]; simp only [Set.mem_Ico] at hj'; omega
      have h2 : j - (q + 1) - (Cancel.chainData inner (slotSign ζ m.c) (addrExt a [m.c])).length =
          j - (q + (toJRc inner).code.size + 1) := by
        rw [length_chainData]; omega
      rw [sigmaAt_toJRc_rest m Qr Qg inner rest a q hj',
        ← chainSig_eq rest (slotSign (slotSign ζ m.c) m.lone)
          (ClassJR.addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) _ j hj', h1]
      simp only [Cancel.chainSig, Cancel.chainData, List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ hle, h2]
      rfl

/-- wt-torus's pair coefficients `pairF` are ClassJR's `coefAt`, with the time swaps `swAt`. -/
theorem pairF_eq : ∀ (X : RegChain) (ζ : ℤˣ) (a : Cancel.Addr) (q j : ℕ),
    j ∈ Set.Ico q (q + (toJRc X).code.size) →
      Cancel.pairF BtJR ((Cancel.chainData X ζ a).getD (j - q) Cancel.dfltP) (swAt X ζ q j) =
        (toJRc X).coefAt ζ a q j
  | .nil, _, _, q, j, hj => by
    simp only [toJRc, ClassJR.RegChain.code, ClassJR.LegalCode.size, add_zero, Set.mem_Ico] at hj
    omega
  | .pair m Qr Qg inner rest, ζ, a, q, j, hj => by
    rcases pair_cases hj with rfl | hj' | hj'
    · rw [coefAt_toJRc_self]
      simp only [swAt, ↓reduceIte, Nat.sub_self, Cancel.chainData, List.getD_cons_zero]
      funext α ta tb
      by_cases hr : slotSign ζ m.red.1 = 1 <;> by_cases hg : slotSign ζ m.green.1 = 1 <;>
        simp [hr, hg, Cancel.pairF, Cancel.redRoots, Cancel.greenRoots, ClassJR.swapT, BtJR,
          addrExt_B2]
    · have hjq : j ≠ q := by simp only [Set.mem_Ico] at hj'; omega
      have hjlt : j < q + 1 + (toJRc inner).code.size := by simp only [Set.mem_Ico] at hj'; omega
      have h1 : j - q = (j - (q + 1)) + 1 := by simp only [Set.mem_Ico] at hj'; omega
      have hlt : j - (q + 1) < (Cancel.chainData inner (slotSign ζ m.c) (addrExt a [m.c])).length := by
        rw [length_chainData]; simp only [Set.mem_Ico] at hj'; omega
      rw [coefAt_toJRc_inner m Qr Qg inner rest ζ a q hj',
        ← pairF_eq inner (slotSign ζ m.c) (ClassJR.addrExt a [m.c]) (q + 1) j hj', h1]
      simp only [swAt, hjq, hjlt, ↓reduceIte, Cancel.chainData, List.getD_cons_succ]
      rw [List.getD_append _ _ _ _ hlt]
      rfl
    · have hjq : j ≠ q := by simp only [Set.mem_Ico] at hj'; omega
      have hjlt : ¬ j < q + 1 + (toJRc inner).code.size := by simp only [Set.mem_Ico] at hj'; omega
      have h1 : j - q = (j - (q + 1)) + 1 := by simp only [Set.mem_Ico] at hj'; omega
      have hle : (Cancel.chainData inner (slotSign ζ m.c) (addrExt a [m.c])).length ≤ j - (q + 1) := by
        rw [length_chainData]; simp only [Set.mem_Ico] at hj'; omega
      have h2 : j - (q + 1) - (Cancel.chainData inner (slotSign ζ m.c) (addrExt a [m.c])).length =
          j - (q + (toJRc inner).code.size + 1) := by
        rw [length_chainData]; omega
      rw [coefAt_toJRc_rest m Qr Qg inner rest ζ a q hj',
        ← pairF_eq rest (slotSign (slotSign ζ m.c) m.lone)
          (ClassJR.addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) _ j hj', h1]
      simp only [swAt, hjq, hjlt, ↓reduceIte, Cancel.chainData, List.getD_cons_succ]
      rw [List.getD_append_right _ _ _ _ hle, h2]
      rfl

/-- One chain of the type 2 recursion, in wt-torus's form. -/
theorem chainT_toCancel (X : RegChain) (ζ : ℤˣ) (a : Cancel.Addr) (β : Cancel.Addr → ℝ) (t : ℝ)
    (g : ℝ → ℂ) :
    ClassJR.chainT ((toJRc X).sigmaAt a 0) (fun j => ClassJR.nodeSgn ((toJRc X).sigmaAt a 0 j))
        (toJRc X).code 0 ((toJRc X).coefAt ζ a 0) β t g =
      ClassJR.chainT (Cancel.chainSig (Cancel.chainData X ζ a))
        (fun j => Cancel.zetaA (Cancel.chainSig (Cancel.chainData X ζ a) j)) (Cancel.chainCode X) 0
        (fun j => Cancel.pairF BtJR ((Cancel.chainData X ζ a).getD j Cancel.dfltP) (swAt X ζ 0 j)) β t
        g := by
  rw [chainCode_eq]
  refine chainT_congr_Ico _ _ (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) β t g
  · rw [← chainSig_eq X ζ a 0 j hj, Nat.sub_zero]
  · rw [zetaA_eq, ← chainSig_eq X ζ a 0 j hj, Nat.sub_zero]
  · rw [← pairF_eq X ζ a 0 j hj, Nat.sub_zero]

/-- **`B̃` satisfies wt-torus's recursion hypothesis** (DH21 (newexp1), (newexp2)). -/
theorem btRec_BtJR : Cancel.BtRec BtJR where
  triv _ _ := rfl
  type1 _ _ _ _ _ _ := ⟨![false, true, false], rfl⟩
  type2 Xp Xm Qlp a b := by
    refine ⟨swAt Xp 1 0, swAt Xm (-1) 0, false, ?_⟩
    funext β t s
    simp only [BtJR, toJR, ClassJR.RegCpl.Bt, ClassJR.type2F]
    rw [chainT_toCancel]
    congr 1
    funext t'
    rw [chainT_toCancel]
    congr 1
    funext s'
    simp only [ClassJR.swapT, Bool.false_eq_true, ↓reduceIte, lonePath_toJRc, addrExt_B2]

end WaveTurbulence.MainCoef
