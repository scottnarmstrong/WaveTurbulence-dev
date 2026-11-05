/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.CancelDraft.CodeVars

/-!
# The regularized limits of the time coefficients of regular couple codes

If a family `Bt Q a b` satisfies the recursion (newexp1)/(newexp2) (`BtRec`), then the
`Z`-regularized integrals of `B̃_Q = Bt Q a b` over its variables `𝒩^ch` converge to `cplJ Z Q a b`
(`regCoef_cpl`). The induction runs over the codes with the closure lemmas `regCoef_type1` and
`regCoef_type2` of `Foundations/Cancel`. The variables of the components are distinct because the
chosen nodes of the links are (`chosen_nodup`).
-/

@[expose] public section

namespace WaveTurbulence.Cancel

open TTree WaveTurbulence.Reg WaveTurbulence.ClassJR WaveTurbulence.Links

/-- The limit of a pair coefficient with its time swaps. -/
noncomputable def pairJsw (Z : Finset Addr) (d : PairDatum) (sw : Bool × Bool) : ℝ → ℝ → ℂ :=
  fun t s => (if sw.1 then cplJ Z d.2.1.1 d.2.1.2.1 d.2.1.2.2 s t else cplJ Z d.2.1.1 d.2.1.2.1 d.2.1.2.2 t s) *
    (if sw.2 then cplJ Z d.2.2.1 d.2.2.2.1 d.2.2.2.2 s t else cplJ Z d.2.2.1 d.2.2.2.1 d.2.2.2.2 t s)

theorem pairJsw_diag (Z : Finset Addr) (d : PairDatum) (sw : Bool × Bool) (τ : ℝ) :
    pairJsw Z d sw τ τ = pairJ Z d τ := by
  unfold pairJsw pairJ; split_ifs <;> rfl

theorem cplJ_symm (Z : Finset Addr) {Q : RegCpl} (h : Q.isType2 = false) (a b : Addr) (t s : ℝ) :
    cplJ Z Q a b t s = cplJ Z Q a b s t := by
  cases Q with
  | triv => rfl
  | type1 c Q₁ Q₂ Q₃ => simp only [cplJ, min_comm]
  | type2 => simp [RegCpl.isType2] at h

theorem RegCoef.of_eq {ζ : Addr → ℤ} {Z S S' : Finset Addr} {F F' : TCoef} {J J' : ℝ → ℝ → ℂ}
    (h : RegCoef ζ Z S F J) (hS : S = S') (hF : F = F') (hJ : J = J') : RegCoef ζ Z S' F' J' := by
  subst hS hF hJ; exact h

theorem nodup_of_append_left {L₁ L₂ : List (Addr × Addr)} (h : ((L₁ ++ L₂).map Prod.fst).Nodup) :
    (L₁.map Prod.fst).Nodup := by rw [List.map_append] at h; exact (List.nodup_append.1 h).1

theorem nodup_of_append_right {L₁ L₂ : List (Addr × Addr)} (h : ((L₁ ++ L₂).map Prod.fst).Nodup) :
    (L₂.map Prod.fst).Nodup := by rw [List.map_append] at h; exact (List.nodup_append.1 h).2.1

variable {Bt : RegCpl → Addr → Addr → TCoef}

theorem pairF_dflt (hBt : BtRec Bt) (sw : Bool × Bool) : pairF Bt dfltP sw = fun _ _ _ => 1 := by
  funext α t s
  simp only [pairF, dfltP, hBt.triv, swapT]
  split_ifs <;> simp

theorem regCoef_dflt (hBt : BtRec Bt) (Z : Finset Addr) (sw : Bool × Bool) :
    RegCoef zetaA Z (pairVars dfltP) (pairF Bt dfltP sw) (pairJsw Z dfltP sw) := by
  refine (regCoef_one zetaA Z).of_eq ?_ (pairF_dflt hBt sw).symm ?_
  · simp [pairVars, dfltP, RegCpl.linksAt, chosenSet]
  · funext t s; simp only [pairJsw, dfltP, cplJ]; split_ifs <;> simp

mutual
/-- **The regularized limit of `B̃_Q`** (DH21 Props 7.4, 7.5 before evaluation). -/
theorem regCoef_cpl (hBt : BtRec Bt) (Z : Finset Addr) :
    ∀ (Q : RegCpl) (a b : Addr), Q.wf = true → ((Q.linksAt a b).map Prod.fst).Nodup →
      RegCoef zetaA Z (chosenSet (Q.linksAt a b)) (Bt Q a b) (cplJ Z Q a b)
  | .triv, a, b, _, _ => by
    refine (regCoef_one zetaA Z).of_eq (by simp [RegCpl.linksAt, chosenSet]) (hBt.triv a b).symm ?_
    funext t s; rfl
  | .type1 c Q₁ Q₂ Q₃, a, b, hwf, hnd => by
    obtain ⟨sw, hsw⟩ := hBt.type1 c Q₁ Q₂ Q₃ a b
    simp only [RegCpl.wf, Bool.and_eq_true] at hwf
    obtain ⟨⟨hw1, hw2⟩, hw3⟩ := hwf
    set L₁ := Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])
    set L₂ := Q₂.linksAt (addrExt b [1]) (addrExt a [1])
    set L₃ := Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])
    have hL : (RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b = (a, b) :: (L₁ ++ L₂ ++ L₃) := rfl
    rw [hL] at hnd ⊢
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨ha, hnd⟩ := hnd
    have h12 := nodup_of_append_left hnd
    have h1 := regCoef_cpl hBt Z Q₁ _ _ hw1 (nodup_of_append_left h12)
    have h2 := regCoef_cpl hBt Z Q₂ _ _ hw2 (nodup_of_append_right h12)
    have h3 := regCoef_cpl hBt Z Q₃ _ _ hw3 (nodup_of_append_right hnd)
    have h01 : Disjoint (chosenSet L₁) (chosenSet L₂) := disjoint_chosenSet_of_nodup h12
    have h012 : Disjoint (chosenSet L₁ ∪ chosenSet L₂) (chosenSet L₃) := by
      rw [← chosenSet_append]; exact disjoint_chosenSet_of_nodup hnd
    have hv : a ∉ chosenSet L₁ ∪ chosenSet L₂ ∪ chosenSet L₃ := by
      rw [← chosenSet_append, ← chosenSet_append]
      simpa [chosenSet] using ha
    have h := regCoef_type1 (ζ := zetaA) (Z := Z) (v := a) sw (S := ![chosenSet L₁, chosenSet L₂, chosenSet L₃])
      (F := ![Bt Q₁ (addrExt a [0]) (addrExt b [c.partner 0]), Bt Q₂ (addrExt b [1]) (addrExt a [1]),
        Bt Q₃ (addrExt a [2]) (addrExt b [c.partner 2])])
      (J := ![cplJ Z Q₁ (addrExt a [0]) (addrExt b [c.partner 0]), cplJ Z Q₂ (addrExt b [1]) (addrExt a [1]),
        cplJ Z Q₃ (addrExt a [2]) (addrExt b [c.partner 2])])
      (fun j => by fin_cases j <;> simpa using ‹_›) h01 h012 hv
    refine h.of_eq ?_ hsw.symm ?_
    · simp [chosenSet_cons, chosenSet_append]
    · funext t s
      simp only [cplJ, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  | .type2 Xp Xm Qlp, a, b, hwf, hnd => by
    obtain ⟨swp, swm, swl, hsw⟩ := hBt.type2 Xp Xm Qlp a b
    simp only [RegCpl.wf, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hwf
    obtain ⟨⟨⟨⟨hwp, hwm⟩, hwl⟩, hl2⟩, -⟩ := hwf
    have hL : (RegCpl.type2 Xp Xm Qlp).linksAt a b = Xp.linksAt 1 a ++ Xm.linksAt (-1) b ++
        Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) := rfl
    rw [hL] at hnd ⊢
    have hndpm := nodup_of_append_left hnd
    have hndp := nodup_of_append_left hndpm
    have hndm := nodup_of_append_right hndpm
    have hndl := nodup_of_append_right hnd
    have hagp : ChainAgr (chainData Xp 1 a) Xp 1 a 0 := fun k _ => by rw [zero_add]
    have hagm : ChainAgr (chainData Xm (-1) b) Xm (-1) b 0 := fun k _ => by rw [zero_add]
    -- the pair coefficients
    have hRp : ∀ j, RegCoef zetaA Z (pairVars ((chainData Xp 1 a).getD j dfltP))
        (pairF Bt ((chainData Xp 1 a).getD j dfltP) (swp j))
        (pairJsw Z ((chainData Xp 1 a).getD j dfltP) (swp j)) := by
      intro j
      by_cases hj : j < (chainData Xp 1 a).length
      · rw [List.getD_eq_getElem _ _ hj]
        exact regCoef_chain hBt Z Xp 1 a hwp hndp _ (List.getElem_mem hj) (swp j)
      · rw [List.getD_eq_default _ _ (not_lt.1 hj)]; exact regCoef_dflt hBt Z (swp j)
    have hRm : ∀ j, RegCoef zetaA Z (pairVars ((chainData Xm (-1) b).getD j dfltP))
        (pairF Bt ((chainData Xm (-1) b).getD j dfltP) (swm j))
        (pairJsw Z ((chainData Xm (-1) b).getD j dfltP) (swm j)) := by
      intro j
      by_cases hj : j < (chainData Xm (-1) b).length
      · rw [List.getD_eq_getElem _ _ hj]
        exact regCoef_chain hBt Z Xm (-1) b hwm hndm _ (List.getElem_mem hj) (swm j)
      · rw [List.getD_eq_default _ _ (not_lt.1 hj)]; exact regCoef_dflt hBt Z (swm j)
    -- a uniform bound
    choose Bp hBp using fun j => (hRp j).nice.bdd
    choose Bm hBm using fun j => (hRm j).nice.bdd
    set BF := ∑ j ∈ Finset.range (chainData Xp 1 a).length, max (Bp j) 0 +
      ∑ j ∈ Finset.range (chainData Xm (-1) b).length, max (Bm j) 0 + 1 with hBFdef
    have hsp : 0 ≤ ∑ j ∈ Finset.range (chainData Xp 1 a).length, max (Bp j) 0 :=
      Finset.sum_nonneg fun _ _ => le_max_right _ _
    have hsm : 0 ≤ ∑ j ∈ Finset.range (chainData Xm (-1) b).length, max (Bm j) 0 :=
      Finset.sum_nonneg fun _ _ => le_max_right _ _
    have hBF0 : 0 ≤ BF := by positivity
    have hBFp : ∀ j α, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖pairF Bt ((chainData Xp 1 a).getD j dfltP) (swp j) α t s‖ ≤ BF := by
      intro j α t ht s hs
      by_cases hj : j < (chainData Xp 1 a).length
      · refine (hBp j α t ht s hs).trans ((le_max_left (Bp j) 0).trans ?_)
        have := Finset.single_le_sum (f := fun j => max (Bp j) 0) (fun _ _ => le_max_right _ _)
          (Finset.mem_range.2 hj)
        linarith
      · rw [List.getD_eq_default _ _ (not_lt.1 hj), pairF_dflt hBt]
        simp only [norm_one]; linarith
    have hBFm : ∀ j α, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ Set.Icc (0 : ℝ) 1,
        ‖pairF Bt ((chainData Xm (-1) b).getD j dfltP) (swm j) α t s‖ ≤ BF := by
      intro j α t ht s hs
      by_cases hj : j < (chainData Xm (-1) b).length
      · refine (hBm j α t ht s hs).trans ((le_max_left (Bm j) 0).trans ?_)
        have := Finset.single_le_sum (f := fun j => max (Bm j) 0) (fun _ _ => le_max_right _ _)
          (Finset.mem_range.2 hj)
        linarith
      · rw [List.getD_eq_default _ _ (not_lt.1 hj), pairF_dflt hBt]
        simp only [norm_one]; linarith
    -- disjointness
    have hvp := chainVarsF_eq (chainData Xp 1 a) Xp 1 a 0 hagp
    have hvm := chainVarsF_eq (chainData Xm (-1) b) Xm (-1) b 0 hagm
    have hpm : Disjoint (chainVarsF (chainSig (chainData Xp 1 a))
        (fun j => pairVars ((chainData Xp 1 a).getD j dfltP)) (chainCode Xp) 0)
        (chainVarsF (chainSig (chainData Xm (-1) b)) (fun j => pairVars ((chainData Xm (-1) b).getD j dfltP))
          (chainCode Xm) 0 ∪ chosenSet (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))) := by
      rw [hvp, hvm, ← chosenSet_append]
      exact disjoint_chosenSet_of_nodup (by rw [← List.append_assoc]; exact hnd)
    have hml : Disjoint (chainVarsF (chainSig (chainData Xm (-1) b))
        (fun j => pairVars ((chainData Xm (-1) b).getD j dfltP)) (chainCode Xm) 0)
        (chosenSet (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))) := by
      rw [hvm]
      exact disjoint_chosenSet_of_nodup (nodup_of_append_right (L₁ := Xp.linksAt 1 a)
        (by rw [← List.append_assoc]; exact hnd))
    have h := regCoef_type2 zetaA_pm (Z := Z) (σp := chainSig (chainData Xp 1 a))
      (σm := chainSig (chainData Xm (-1) b)) (εp := fun j => zetaA (chainSig (chainData Xp 1 a) j))
      (εm := fun j => zetaA (chainSig (chainData Xm (-1) b) j)) (fun _ => rfl) (fun _ => rfl)
      (fun j => (hRp j).nice) (fun j => (hRm j).nice) hBF0 hBFp hBFm (chainCode Xp) (chainCode Xm)
      (fun j _ => (hRp j).lim) (fun j _ => (hRm j).lim)
      (regCoef_swap (regCoef_cpl hBt Z Qlp _ _ hwl hndl) swl)
      (chainDisjF_of_nodup _ Xp 1 a 0 hagp hndp) (chainDisjF_of_nodup _ Xm (-1) b 0 hagm hndm) hpm hml
    refine h.of_eq ?_ (hsw.symm) ?_
    · rw [hvp, hvm, chosenSet_append, chosenSet_append, Finset.union_assoc]
    · funext t s
      simp only [pairJsw_diag]
      rw [chainL_eq_chainJ Z _ Xp 1 a 0 hagp]
      simp only [cplJ]
      congr 1
      funext t'
      rw [chainL_eq_chainJ Z _ Xm (-1) b 0 hagm]
      congr 1
      funext s'
      split_ifs
      · exact cplJ_symm Z hl2 _ _ _ _
      · rfl
/-- The pair coefficients of a chain have regularized limits. -/
theorem regCoef_chain (hBt : BtRec Bt) (Z : Finset Addr) :
    ∀ (X : RegChain) (ζ : ℤˣ) (a : Addr), X.wf = true → ((X.linksAt ζ a).map Prod.fst).Nodup →
      ∀ d ∈ chainData X ζ a, ∀ sw : Bool × Bool,
        RegCoef zetaA Z (pairVars d) (pairF Bt d sw) (pairJsw Z d sw)
  | .nil, _, _, _, _, d, hd, _ => by simp [chainData] at hd
  | .pair m Qr Qg i r, ζ, a, hwf, hnd, d, hd, sw => by
    simp only [RegChain.wf, Bool.and_eq_true] at hwf
    obtain ⟨⟨⟨hwr, hwg⟩, hwi⟩, hwrest⟩ := hwf
    rw [linksAt_pair] at hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨-, hnd⟩ := hnd
    have h1a := nodup_of_append_left hnd
    have h1b := nodup_of_append_left h1a
    rcases List.mem_cons.1 hd with rfl | hd
    · exact regCoef_mul (disjoint_chosenSet_of_nodup h1b)
        (regCoef_swap (regCoef_cpl hBt Z Qr _ _ hwr (nodup_of_append_left h1b)) sw.1)
        (regCoef_swap (regCoef_cpl hBt Z Qg _ _ hwg (nodup_of_append_right h1b)) sw.2)
    · rcases List.mem_append.1 hd with hd | hd
      · exact regCoef_chain hBt Z i _ _ hwi (nodup_of_append_right h1a) d hd sw
      · exact regCoef_chain hBt Z r _ _ hwrest (nodup_of_append_right hnd) d hd sw
end

end WaveTurbulence.Cancel
