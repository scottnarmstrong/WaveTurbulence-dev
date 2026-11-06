/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.WaveB.Molecules
public import WaveTurbulence.Foundations.Molecule.MoleculeDegreeCompat
import Mathlib.Tactic

/-! # Unordered bond multisets of one ladder insertion

Pure natural-number combinatorics. For a slot with rails `x ⋯ y`, `x' ⋯ y'` in a
template with `N` atoms, `insSym N x y x' y' k R` is the unordered bond multiset
of `k` inserted rungs (`R` the untouched bonds).
-/

public section
namespace WaveTurbulence.Vine.Param

/-- Unordered bond multiset of a list of ordered bonds. -/
@[expose] def bondSym (l : List (ℕ×ℕ)) : Multiset (Sym2 ℕ) :=
  ((l.map fun p => s(p.1,p.2) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ))

/-- The `j`-th node of a rail with `k` interior nodes `base, base+1, ...`. -/
@[expose] def ladderNode (z z' base k j : ℕ) : ℕ :=
  if j = 0 then z else if j ≤ k then base + j - 1 else z'

/-- Unordered rail bonds, as a list. -/
@[expose] def railList (z z' base k : ℕ) : List (Sym2 ℕ) :=
  (List.range (k+1)).map fun j => s(ladderNode z z' base k j,ladderNode z z' base k (j+1))

/-- Unordered rung pairs (each occurs twice in the template). -/
@[expose] def rungList (base k : ℕ) : List (Sym2 ℕ) :=
  (List.range k).map fun j => s(base+j,base+k+j)

/-- Bond multiset of `k` inserted rungs next to the untouched bonds `R`. -/
@[expose] def insSym (N x y x' y' k : ℕ) (R : Multiset (Sym2 ℕ)) : Multiset (Sym2 ℕ) :=
  R + (railList x y N k : Multiset (Sym2 ℕ)) + (railList x' y' (N+k) k : Multiset (Sym2 ℕ)) +
    2 • (rungList N k : Multiset (Sym2 ℕ))

/-- The order preserving relabeling that skips two removed atoms. -/
@[expose] def skip2 (f0 f1 t : ℕ) : ℕ := t - (if f0 < t then 1 else 0) - (if f1 < t then 1 else 0)

theorem railBonds_list (z z' base k : ℕ) :
    (railBonds z ((List.range k).map (base + ·)) z').map (fun p => s(p.1,p.2)) =
      railList z z' base k := by
  induction k generalizing z base with
  | zero => simp [railBonds,railList,ladderNode]
  | succ k ih =>
    have h1 : railBonds z ((List.range (k+1)).map (base + ·)) z' =
        (z,base) :: railBonds base ((List.range k).map (base+1 + ·)) z' := by
      rw [List.range_succ_eq_map]
      simp only [railBonds,List.map_cons,List.map_map,List.cons_append,List.zip_cons_cons]
      simp [Function.comp_def,add_assoc,add_comm 1]
    rw [h1,List.map_cons,ih]
    unfold railList
    rw [List.range_succ_eq_map (n := k+1),List.map_cons,List.map_map]
    refine congrArg₂ List.cons ?_ (List.map_congr_left ?_)
    · simp [ladderNode]
    · intro j _
      have e0 : ladderNode base z' (base+1) k j = ladderNode z z' base (k+1) (j+1) := by
        simp only [ladderNode,Nat.add_one_ne_zero,if_false]; split_ifs <;> omega
      have e1 : ladderNode base z' (base+1) k (j+1) = ladderNode z z' base (k+1) (j+1+1) := by
        simp only [ladderNode,Nat.add_one_ne_zero,if_false]; split_ifs <;> omega
      simp only [Function.comp_apply,Nat.succ_eq_add_one]
      rw [e0,e1]

theorem coe_flatMap_double {α β : Type} (f : α → β) (l : List α) :
    (((l.flatMap fun a => [a,a]).map f : List β) : Multiset β) = 2 • ((l.map f : List β) : Multiset β) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.flatMap_cons]
    simp only [List.cons_append,List.nil_append,List.map_cons]
    rw [← Multiset.cons_coe,← Multiset.cons_coe,ih]
    simp only [two_nsmul,← Multiset.cons_coe,Multiset.cons_add,Multiset.add_cons]

theorem bondSym_split (U : VineTemplate) (x y x' y' : ℕ)
    (h1 : (x,y) ∈ U.bonds) (h2 : (x',y') ∈ U.bonds.erase (x,y)) :
    bondSym U.bonds = s(x,y) ::ₘ s(x',y') ::ₘ
      bondSym ((U.bonds.erase (x,y)).erase (x',y')) := by
  have p1 := List.perm_cons_erase h1
  have p2 := List.perm_cons_erase h2
  have p3 := (p1.trans (List.Perm.cons _ p2))
  unfold bondSym
  rw [Multiset.cons_coe,Multiset.cons_coe,Multiset.coe_eq_coe]
  simpa using (p3.map fun p : ℕ×ℕ => s(p.1,p.2))

theorem bondSym_insertRungs (U : VineTemplate) (x y x' y' k : ℕ)
    (h1 : (x,y) ∈ U.bonds) (h2 : (x',y') ∈ U.bonds.erase (x,y)) :
    bondSym (insertRungs U ((x,y),(x',y')) k).bonds =
      insSym U.n x y x' y' k (bondSym ((U.bonds.erase (x,y)).erase (x',y'))) := by
  by_cases hk : k = 0
  · subst hk
    simp only [insertRungs,ite_true,insSym,railList,rungList,List.range_zero,List.map_nil,
      Multiset.coe_nil,smul_zero,add_zero]
    rw [bondSym_split U x y x' y' h1 h2]
    simp [ladderNode,add_comm]
  · simp only [insertRungs,hk,ite_false]
    have hB : ∀ z z' b : ℕ,
        bondSym (railBonds z ((List.range k).map (b + ·)) z') = (railList z z' b k : Multiset (Sym2 ℕ)) := by
      intro z z' b
      unfold bondSym
      rw [railBonds_list]
    have hD : bondSym (((List.range k).map (U.n + ·)).zip ((List.range k).map (U.n+k+ ·))
        |>.flatMap fun p => [p,p]) = 2 • (rungList U.n k : Multiset (Sym2 ℕ)) := by
      unfold bondSym
      rw [coe_flatMap_double (fun p : ℕ×ℕ => s(p.1,p.2)),List.zip_map',List.map_map]
      rfl
    have hA : ∀ l1 l2 : List (ℕ×ℕ), bondSym (l1 ++ l2) = bondSym l1 + bondSym l2 := by
      intro l1 l2
      unfold bondSym
      rw [List.map_append,Multiset.coe_add]
    rw [hA,hA,hA,hB,hB,hD]
    rfl

theorem railList_succ_last (z z' base k : ℕ) :
    railList z z' base (k+1) =
      (List.range k).map (fun j => s(ladderNode z z' base (k+1) j,ladderNode z z' base (k+1) (j+1))) ++
        [s(ladderNode z z' base (k+1) k,ladderNode z z' base (k+1) (k+1)),
         s(ladderNode z z' base (k+1) (k+1),ladderNode z z' base (k+1) (k+2))] := by
  unfold railList
  rw [List.range_succ,List.range_succ,List.map_append,List.map_append]
  simp

theorem rungList_succ_last (base k : ℕ) :
    rungList base (k+1) = (List.range k).map (fun j => s(base+j,base+(k+1)+j)) ++
      [s(base+k,base+(k+1)+k)] := by
  unfold rungList
  rw [List.range_succ,List.map_append]
  simp

/-- The six bonds of the contracted cell next to the `y`-end. -/
@[expose] def cellY (N k x y x' y' : ℕ) : Multiset (Sym2 ℕ) :=
  {s(ladderNode x y N (k+1) k,N+k)} + {s(ladderNode x' y' (N+(k+1)) (k+1) k,N+(2*k+1))} +
    2 • {s(N+k,N+(2*k+1))} + {s(N+k,y)} + {s(N+(2*k+1),y')}

/-- The remaining bonds (no contact with the two removed atoms). -/
@[expose] def restY (N k x y x' y' : ℕ) (R : Multiset (Sym2 ℕ)) : Multiset (Sym2 ℕ) :=
  R + (((List.range k).map (fun j => s(ladderNode x y N (k+1) j,ladderNode x y N (k+1) (j+1))) :
        List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) +
    (((List.range k).map (fun j => s(ladderNode x' y' (N+(k+1)) (k+1) j,
        ladderNode x' y' (N+(k+1)) (k+1) (j+1))) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) +
    2 • (((List.range k).map (fun j => s(N+j,N+(k+1)+j)) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ))

theorem contractY_split (N k x y x' y' : ℕ) (R : Multiset (Sym2 ℕ)) :
    insSym N x y x' y' (k+1) R = cellY N k x y x' y' + restY N k x y x' y' R := by
  unfold insSym cellY restY
  rw [railList_succ_last,railList_succ_last,rungList_succ_last]
  have n1 : ladderNode x y N (k+1) (k+1) = N+k := by simp [ladderNode]
  have n2 : ladderNode x y N (k+1) (k+1+1) = y := by simp [ladderNode]
  have n3 : ladderNode x' y' (N+(k+1)) (k+1) (k+1) = N+(2*k+1) := by
    simp only [ladderNode,Nat.add_one_ne_zero,ite_false,le_refl,ite_true]; omega
  have n4 : ladderNode x' y' (N+(k+1)) (k+1) (k+1+1) = y' := by simp [ladderNode]
  have e1 : N+(k+1)+k = N+(2*k+1) := by omega
  simp only [n1,n2,n3,n4,e1,List.cons_append,List.nil_append,← Multiset.coe_add,← Multiset.cons_coe,
    Multiset.coe_nil,← Multiset.singleton_add,Multiset.add_zero,Multiset.zero_add,two_nsmul]
  abel

theorem skip2_lt (f0 f1 t : ℕ) (h : t < f0) (h1 : f0 ≤ f1) : skip2 f0 f1 t = t := by
  simp only [skip2]; split_ifs <;> omega

theorem contractY_nu (N k x y j : ℕ) (hx : x < N) (hy : y < N) (hj : j ≤ k) :
    skip2 (N+k) (N+(2*k+1)) (ladderNode x y N (k+1) j) = ladderNode x y N k j := by
  simp only [ladderNode,skip2]
  split_ifs <;> omega

theorem contractY_nv (N k x' y' j : ℕ) (hx : x' < N) (hy : y' < N) (hj : j ≤ k) :
    skip2 (N+k) (N+(2*k+1)) (ladderNode x' y' (N+(k+1)) (k+1) j) =
      ladderNode x' y' (N+k) k j := by
  simp only [ladderNode,skip2]
  split_ifs <;> omega

theorem contractY_back (N k x y x' y' : ℕ) (hx : x < N) (hy : y < N) (hx' : x' < N)
    (hy' : y' < N) (R : Multiset (Sym2 ℕ)) (hR : ∀ e ∈ R, ∀ z ∈ e, z < N) :
    insSym N x y x' y' k R =
      (restY N k x y x' y' R).map (Sym2.map (skip2 (N+k) (N+(2*k+1)))) +
        {s(skip2 (N+k) (N+(2*k+1)) (ladderNode x y N (k+1) k),
            skip2 (N+k) (N+(2*k+1)) y)} +
        {s(skip2 (N+k) (N+(2*k+1)) (ladderNode x' y' (N+(k+1)) (k+1) k),
            skip2 (N+k) (N+(2*k+1)) y')} := by
  have hRm : R.map (Sym2.map (skip2 (N+k) (N+(2*k+1)))) = R := by
    conv_rhs => rw [← Multiset.map_id R]
    apply Multiset.map_congr rfl
    intro e he
    revert he
    induction e using Sym2.ind with
    | h a b =>
      intro he
      have ha := hR _ he a (Sym2.mem_mk_left _ _)
      have hb := hR _ he b (Sym2.mem_mk_right _ _)
      simp only [Sym2.map_mk,id,skip2_lt (N+k) (N+(2*k+1)) a (by omega) (by omega),
        skip2_lt (N+k) (N+(2*k+1)) b (by omega) (by omega)]
  have hy1 : skip2 (N+k) (N+(2*k+1)) y = y := skip2_lt (N+k) (N+(2*k+1)) y (by omega) (by omega)
  have hy2 : skip2 (N+k) (N+(2*k+1)) y' = y' := skip2_lt (N+k) (N+(2*k+1)) y' (by omega) (by omega)
  unfold insSym restY
  simp only [Multiset.map_add,Multiset.map_coe,Multiset.map_nsmul,hRm,List.map_map]
  have L1 : List.map (Sym2.map (skip2 (N+k) (N+(2*k+1))) ∘ fun j =>
      s(ladderNode x y N (k+1) j,ladderNode x y N (k+1) (j+1))) (List.range k) =
      (List.range k).map (fun j => s(ladderNode x y N k j,ladderNode x y N k (j+1))) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk]
    rw [contractY_nu N k x y j hx hy (by omega),contractY_nu N k x y (j+1) hx hy (by omega)]
  have L2 : List.map (Sym2.map (skip2 (N+k) (N+(2*k+1))) ∘ fun j =>
      s(ladderNode x' y' (N+(k+1)) (k+1) j,ladderNode x' y' (N+(k+1)) (k+1) (j+1))) (List.range k) =
      (List.range k).map (fun j => s(ladderNode x' y' (N+k) k j,ladderNode x' y' (N+k) k (j+1))) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk]
    rw [contractY_nv N k x' y' j hx' hy' (by omega),contractY_nv N k x' y' (j+1) hx' hy' (by omega)]
  have L3 : List.map (Sym2.map (skip2 (N+k) (N+(2*k+1))) ∘ fun j => s(N+j,N+(k+1)+j))
      (List.range k) = (List.range k).map (fun j => s(N+j,N+k+j)) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk,skip2]
    congr 2 <;> split_ifs <;> omega
  rw [L1,L2,L3,hy1,hy2,contractY_nu N k x y k hx hy le_rfl,
    contractY_nv N k x' y' k hx' hy' le_rfl]
  unfold rungList railList
  rw [List.range_succ,List.map_append,List.map_append]
  have f1 : ladderNode x y N k (k+1) = y := by simp [ladderNode]
  have f2 : ladderNode x' y' (N+k) k (k+1) = y' := by simp [ladderNode]
  simp only [f1,f2,List.map_cons,List.map_nil,← Multiset.coe_add,List.cons_append,List.nil_append,
    ← Multiset.cons_coe,Multiset.coe_nil,← Multiset.singleton_add,Multiset.add_zero,Multiset.zero_add]
  abel

theorem restY_avoid (N k x y x' y' : ℕ) (hx : x < N) (hx' : x' < N)
    (R : Multiset (Sym2 ℕ)) (hR : ∀ e ∈ R, ∀ z ∈ e, z < N) :
    ∀ e ∈ restY N k x y x' y' R, ∀ z ∈ e, z ≠ N+k ∧ z ≠ N+(2*k+1) := by
  intro e he z hz
  have hu : ∀ j ≤ k, ladderNode x y N (k+1) j ≠ N+k ∧ ladderNode x y N (k+1) j ≠ N+(2*k+1) := by
    intro j hj
    simp only [ladderNode]
    split_ifs <;> omega
  have hv : ∀ j ≤ k, ladderNode x' y' (N+(k+1)) (k+1) j ≠ N+k ∧
      ladderNode x' y' (N+(k+1)) (k+1) j ≠ N+(2*k+1) := by
    intro j hj
    simp only [ladderNode]
    split_ifs <;> omega
  unfold restY at he
  simp only [Multiset.mem_add,Multiset.mem_nsmul,Multiset.mem_coe,List.mem_map,List.mem_range] at he
  rcases he with ((he | ⟨j,hj,rfl⟩) | ⟨j,hj,rfl⟩) | ⟨_,⟨j,hj,rfl⟩⟩
  · have := hR e he z hz; omega
  · rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hu j (by omega)
    · exact hu (j+1) (by omega)
  · rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hv j (by omega)
    · exact hv (j+1) (by omega)
  · rcases Sym2.mem_iff.mp hz with rfl | rfl <;> omega

/-- The six bonds of the contracted cell next to the `x`-end (first rung). -/
@[expose] def cellX (N k x y x' y' : ℕ) : Multiset (Sym2 ℕ) :=
  {s(x,N)} + {s(x',N+(k+1))} + 2 • {s(N,N+(k+1))} +
    {s(N,ladderNode x y N (k+1) 2)} + {s(N+(k+1),ladderNode x' y' (N+(k+1)) (k+1) 2)}

/-- The remaining bonds when the first rung is removed. -/
@[expose] def restX (N k x y x' y' : ℕ) (R : Multiset (Sym2 ℕ)) : Multiset (Sym2 ℕ) :=
  R + (((List.range k).map (fun j => s(ladderNode x y N (k+1) (j+2),ladderNode x y N (k+1) (j+3))) :
        List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) +
    (((List.range k).map (fun j => s(ladderNode x' y' (N+(k+1)) (k+1) (j+2),
        ladderNode x' y' (N+(k+1)) (k+1) (j+3))) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ)) +
    2 • (((List.range k).map (fun j => s(N+(j+1),N+(k+1)+(j+1))) : List (Sym2 ℕ)) : Multiset (Sym2 ℕ))

theorem contractX_split (N k x y x' y' : ℕ) (R : Multiset (Sym2 ℕ)) :
    insSym N x y x' y' (k+1) R = cellX N k x y x' y' + restX N k x y x' y' R := by
  unfold insSym cellX restX railList rungList
  have n1 : ladderNode x y N (k+1) 1 = N := by simp [ladderNode]
  have n2 : ladderNode x' y' (N+(k+1)) (k+1) 1 = N+(k+1) := by simp [ladderNode]
  have n0 : ladderNode x y N (k+1) 0 = x := by simp [ladderNode]
  have n3 : ladderNode x' y' (N+(k+1)) (k+1) 0 = x' := by simp [ladderNode]
  simp only [List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def,Nat.succ_eq_add_one,n0,n1,n2,n3,
    zero_add,add_zero,← Multiset.coe_add,List.cons_append,List.nil_append,
    ← Multiset.cons_coe,Multiset.coe_nil,← Multiset.singleton_add,Multiset.add_zero,
    Multiset.zero_add,two_nsmul,Nat.add_assoc,Nat.reduceAdd]
  abel

theorem contractX_nu (N k x y j : ℕ) (hx : x < N) (hy : y < N) (hj : 1 ≤ j) (hj' : j ≤ k+1) :
    skip2 N (N+(k+1)) (ladderNode x y N (k+1) (j+1)) = ladderNode x y N k j := by
  simp only [ladderNode,skip2,Nat.add_one_ne_zero,ite_false]
  split_ifs <;> omega

theorem contractX_nv (N k x' y' j : ℕ) (hx : x' < N) (hy : y' < N) (hj : 1 ≤ j) (hj' : j ≤ k+1) :
    skip2 N (N+(k+1)) (ladderNode x' y' (N+(k+1)) (k+1) (j+1)) =
      ladderNode x' y' (N+k) k j := by
  simp only [ladderNode,skip2,Nat.add_one_ne_zero,ite_false]
  split_ifs <;> omega

theorem contractX_back (N k x y x' y' : ℕ) (hx : x < N) (hy : y < N) (hx' : x' < N)
    (hy' : y' < N) (R : Multiset (Sym2 ℕ)) (hR : ∀ e ∈ R, ∀ z ∈ e, z < N) :
    insSym N x y x' y' k R =
      (restX N k x y x' y' R).map (Sym2.map (skip2 N (N+(k+1)))) +
        {s(skip2 N (N+(k+1)) x,skip2 N (N+(k+1)) (ladderNode x y N (k+1) 2))} +
        {s(skip2 N (N+(k+1)) x',skip2 N (N+(k+1)) (ladderNode x' y' (N+(k+1)) (k+1) 2))} := by
  have hRm : R.map (Sym2.map (skip2 N (N+(k+1)))) = R := by
    conv_rhs => rw [← Multiset.map_id R]
    apply Multiset.map_congr rfl
    intro e he
    revert he
    induction e using Sym2.ind with
    | h a b =>
      intro he
      have ha := hR _ he a (Sym2.mem_mk_left _ _)
      have hb := hR _ he b (Sym2.mem_mk_right _ _)
      simp only [Sym2.map_mk,id,skip2_lt N (N+(k+1)) a (by omega) (by omega),
        skip2_lt N (N+(k+1)) b (by omega) (by omega)]
  have hx1 : skip2 N (N+(k+1)) x = x := skip2_lt N (N+(k+1)) x (by omega) (by omega)
  have hx2 : skip2 N (N+(k+1)) x' = x' := skip2_lt N (N+(k+1)) x' (by omega) (by omega)
  unfold insSym restX
  simp only [Multiset.map_add,Multiset.map_coe,Multiset.map_nsmul,hRm,List.map_map]
  have L1 : List.map (Sym2.map (skip2 N (N+(k+1))) ∘ fun j =>
      s(ladderNode x y N (k+1) (j+2),ladderNode x y N (k+1) (j+3))) (List.range k) =
      (List.range k).map (fun j => s(ladderNode x y N k (j+1),ladderNode x y N k (j+2))) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk]
    rw [contractX_nu N k x y (j+1) hx hy (by omega) (by omega),
      contractX_nu N k x y (j+2) hx hy (by omega) (by omega)]
  have L2 : List.map (Sym2.map (skip2 N (N+(k+1))) ∘ fun j =>
      s(ladderNode x' y' (N+(k+1)) (k+1) (j+2),ladderNode x' y' (N+(k+1)) (k+1) (j+3)))
      (List.range k) =
      (List.range k).map (fun j => s(ladderNode x' y' (N+k) k (j+1),ladderNode x' y' (N+k) k (j+2))) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk]
    rw [contractX_nv N k x' y' (j+1) hx' hy' (by omega) (by omega),
      contractX_nv N k x' y' (j+2) hx' hy' (by omega) (by omega)]
  have L3 : List.map (Sym2.map (skip2 N (N+(k+1))) ∘ fun j => s(N+(j+1),N+(k+1)+(j+1)))
      (List.range k) = (List.range k).map (fun j => s(N+j,N+k+j)) := by
    apply List.map_congr_left
    intro j hj
    have hj := List.mem_range.mp hj
    simp only [Function.comp_apply,Sym2.map_mk,skip2]
    congr 2 <;> split_ifs <;> omega
  have m1 : skip2 N (N+(k+1)) (ladderNode x y N (k+1) 2) = ladderNode x y N k 1 := by
    have := contractX_nu N k x y 1 hx hy le_rfl (by omega)
    simpa using this
  have m2 : skip2 N (N+(k+1)) (ladderNode x' y' (N+(k+1)) (k+1) 2) = ladderNode x' y' (N+k) k 1 := by
    have := contractX_nv N k x' y' 1 hx' hy' le_rfl (by omega)
    simpa using this
  rw [L1,L2,L3,hx1,hx2,m1,m2]
  unfold rungList railList
  have g1 : ladderNode x y N k 0 = x := by simp [ladderNode]
  have g2 : ladderNode x' y' (N+k) k 0 = x' := by simp [ladderNode]
  simp only [List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def,
    Nat.succ_eq_add_one,g1,g2,zero_add,← Multiset.coe_add,List.cons_append,List.nil_append,
    ← Multiset.cons_coe,Multiset.coe_nil,← Multiset.singleton_add,Multiset.add_zero,
    Multiset.zero_add,two_nsmul,Nat.add_assoc,Nat.reduceAdd]
  abel

theorem restX_avoid (N k x y x' y' : ℕ) (hx : x < N) (hy : y < N) (hx' : x' < N) (hy' : y' < N)
    (R : Multiset (Sym2 ℕ)) (hR : ∀ e ∈ R, ∀ z ∈ e, z < N) :
    ∀ e ∈ restX N k x y x' y' R, ∀ z ∈ e, z ≠ N ∧ z ≠ N+(k+1) := by
  intro e he z hz
  have hu : ∀ j, 2 ≤ j → j ≤ k+2 → ladderNode x y N (k+1) j ≠ N ∧
      ladderNode x y N (k+1) j ≠ N+(k+1) := by
    intro j hj hj'
    simp only [ladderNode]
    split_ifs <;> omega
  have hv : ∀ j, 2 ≤ j → j ≤ k+2 → ladderNode x' y' (N+(k+1)) (k+1) j ≠ N ∧
      ladderNode x' y' (N+(k+1)) (k+1) j ≠ N+(k+1) := by
    intro j hj hj'
    simp only [ladderNode]
    split_ifs <;> omega
  unfold restX at he
  simp only [Multiset.mem_add,Multiset.mem_nsmul,Multiset.mem_coe,List.mem_map,List.mem_range] at he
  rcases he with ((he | ⟨j,hj,rfl⟩) | ⟨j,hj,rfl⟩) | ⟨_,⟨j,hj,rfl⟩⟩
  · have := hR e he z hz; omega
  · rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hu (j+2) (by omega) (by omega)
    · exact hu (j+3) (by omega) (by omega)
  · rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact hv (j+2) (by omega) (by omega)
    · exact hv (j+3) (by omega) (by omega)
  · rcases Sym2.mem_iff.mp hz with rfl | rfl <;> omega

end WaveTurbulence.Vine.Param
