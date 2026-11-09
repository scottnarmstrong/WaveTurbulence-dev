/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.TVine.Chart.DeriveNodeSpine
public import WaveTurbulence.Foundations.TVine.Chart.DeriveCopy

/-!
# Derivation of the cell decomposition, XVIII: the pendant cells and the copy cell

* the pendant rung `Y k` (`k + 1 < s`), input region `S ∖ H k`, exit region `S ∖ H (k+1)` (`pc_pendRung`);
* the (D) core `Y (s-1)`, input region `S ∖ H (s-1)` (`pc_pendCore`); its input atoms are its two ends, by the budget
  at the middle atom;
* the copy cell of a (P-b) attachment at `j`: input region `reg j false`, exit region `reg j true`, pendant region
  `S ∖ H 0` (`pc_copy`).
-/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.TVine.Chart

open Finset VineParamContract Struct

variable {V D : Type} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {S : Finset V} {a b : V}

theorem other_inn {X : Finset V} (π : Port2 M S X a b) {e : Bond M S} (he : e ∈ portSet (M := M) (S := S) X)
    (h : e ≠ π.out) : e = π.inn := by
  rw [π.set_eq, mem_insert, mem_singleton] at he
  rcases he with he | he
  · exact absurd he h
  · exact he

theorem other_out {X : Finset V} (π : Port2 M S X a b) {e : Bond M S} (he : e ∈ portSet (M := M) (S := S) X)
    (h : e ≠ π.inn) : e = π.out := by
  rw [π.set_eq, mem_insert, mem_singleton] at he
  rcases he with he | he
  · exact he
  · exact absurd he h

namespace Lay

variable (L : Lay M S a b) (hB : M.IsBlock S a b)

omit [DecidableEq D] in
theorem H_succ_sub (k : ℕ) : L.H (k + 1) ⊆ L.H k := by
  intro v hv
  obtain ⟨l, hl, hls, hvl⟩ := (L.mem_H (k + 1) v).mp hv
  exact (L.mem_H k v).mpr ⟨l, by omega, hls, hvl⟩

include hB

theorem Y_not_H_succ {k : ℕ} (hk : k < L.s) {v : V} (hv : v ∈ L.Y k) : v ∉ L.H (k + 1) := by
  intro h
  obtain ⟨l, hl, hls, hvl⟩ := (L.mem_H (k + 1) v).mp h
  have := L.Y_unique hB hk hls hv hvl
  omega

variable (hM : M.IsMolecule) (hT : M.IsTVine S a b) (hA : AttachInput)
include hM hT hA

/-! ## Pendant rungs -/

theorem pc_pendRung {k : ℕ} (hk : k + 1 < L.s) (hR : IsRungPiece M (L.Y k)) :
    Nonempty (PCell M S a b 2 2 (fun _ c => PairOK c ∧ c.mu = 2) (L.Y k) (S \ L.H k)
      (some (S \ L.H (k + 1))) none 0 0 6) := by
  obtain ⟨u, w, huw, hY, h2⟩ := hR
  have hk' : k < L.s := by omega
  have hu : u ∈ L.Y k := by rw [hY]; simp
  have hw : w ∈ L.Y k := by rw [hY]; simp
  obtain ⟨hua, hub⟩ := L.Y_interior hk' hu
  obtain ⟨hwa, hwb⟩ := L.Y_interior hk' hw
  have huS := L.Y_sub hB hk' hu
  have hwS := L.Y_sub hB hk' hw
  obtain ⟨pti⟩ := L.port_pend hB hM hT hA hk'
  obtain ⟨pto⟩ := L.port_pend hB hM hT hA hk
  have hEi : InEnds pti u w := by
    obtain ⟨h1, h2⟩ := L.pend_in_ends hB hk' pti
    rw [hY, mem_insert, mem_singleton] at h1 h2
    exact inEnds_of pti hua hub hwa hwb h1 h2
  have hEo : OutEnds pto u w := by
    obtain ⟨h1, h2⟩ := L.pend_out_ends hB hk pto
    rw [hY, mem_insert, mem_singleton] at h1 h2
    exact outEnds_of pto hua hub hwa hwb h1 h2
  obtain ⟨d₀, d₁, hdd, hd₀, hd₁⟩ := two_bonds huS hwS h2
  have hnot : ∀ v, v ∈ L.Y k → v ∉ S \ L.H k := fun v hv h => (mem_sdiff.mp h).2 (L.Y_sub_H hk' hv)
  have hin : ∀ v, v ∈ L.Y k → v ∈ S \ L.H (k + 1) := fun v hv =>
    mem_sdiff.mpr ⟨L.Y_sub hB hk' hv, L.Y_not_H_succ hB hk' hv⟩
  obtain ⟨c, hc, φ, hφA, -, heO, heI, p, hp, hp1, hp2⟩ := place_rung pendRungTable pendRungTable_ok
    pendRungTable_cover hM huw (hB.1 huS) (hB.1 hwS) (deg4 hB huS hua hub) (deg4 hB hwS hwa hwb) d₀ d₁ hdd hd₀
    hd₁ pti pto (sdiff_subset_sdiff le_rfl (L.H_succ_sub k)) (hnot u hu) (hnot w hw) (hin u hu) (hin w hw) hEi hEo
  obtain ⟨hv, hok, hrc, hrel, hex, hmu⟩ := pendRungTable_ok c hc
  have hoB : c.outB = none := outB_none_of rungShape hrc (by decide)
  exact ⟨{
    cfg := c
    emb := φ
    valid := hv
    ok := ⟨hok, hmu⟩
    rel := hrel
    extra := fun x => (extra_none hex hoB x).elim
    atoms := by rw [hY]; exact atoms_two hφA
    pin := pti
    bO := heO
    bI := heI
    oM := by
      intro X hX pt
      obtain rfl := Option.some.inj hX
      exact ⟨p, hp, hp1.trans (port2_out_eq pto pt), hp2.trans (port2_inn_eq pto pt)⟩
    oB := by intro X hX; cases hX }⟩

/-! ## The (D) core -/

theorem pc_pendCore (hs : 1 ≤ L.s) (hD : IsCoreD M (L.Y (L.s - 1))) :
    Nonempty (PCell M S a b 3 3 (fun _ c => CoreOK c) (L.Y (L.s - 1)) (S \ L.H (L.s - 1)) none none 0 0 7) := by
  obtain ⟨x, y, z, hxy, hyz, hxz, hY, hbxy, hbyz, hbxz⟩ := hD
  have hk : L.s - 1 < L.s := by omega
  have hx : x ∈ L.Y (L.s - 1) := by rw [hY]; simp
  have hy : y ∈ L.Y (L.s - 1) := by rw [hY]; simp
  have hz : z ∈ L.Y (L.s - 1) := by rw [hY]; simp
  obtain ⟨hxa, hxb⟩ := L.Y_interior hk hx
  obtain ⟨hya, hyb⟩ := L.Y_interior hk hy
  obtain ⟨hza, hzb⟩ := L.Y_interior hk hz
  have hxS := L.Y_sub hB hk hx
  have hyS := L.Y_sub hB hk hy
  have hzS := L.Y_sub hB hk hz
  obtain ⟨pti⟩ := L.port_pend hB hM hT hA hk
  have hnot : ∀ v, v ∈ L.Y (L.s - 1) → v ∉ S \ L.H (L.s - 1) := fun v hv h =>
    (mem_sdiff.mp h).2 (L.Y_sub_H hk hv)
  have hdiff : ∀ v ∈ S, v ∈ S → v ∉ S \ L.H (L.s - 1) → v ∈ L.Y (L.s - 1) := by
    intro v hv _ h
    have hH : v ∈ L.H (L.s - 1) := by
      by_contra h'; exact h (mem_sdiff.mpr ⟨hv, h'⟩)
    obtain ⟨l, hl, hls, hvl⟩ := (L.mem_H _ v).mp hH
    have : l = L.s - 1 := by omega
    rw [← this]; exact hvl
  have hsum := budget (C := L.Y (L.s - 1)) (Xo := S) sdiff_subset hnot (L.Y_sub hB hk) hdiff hy
    (noLoopAt hT hya hyb)
  rw [deg4 hB hyS hya hyb] at hsum
  have hiy : (innerAt (M := M) (S := S) (L.Y (L.s - 1)) y).card = M.bondsBetween y x + M.bondsBetween y z := by
    rw [hY, perm_xyz]; exact card_innerAt_three hxy.symm hxz hyz hyS hxS hzS (noLoopAt hT hya hyb)
  rw [bondsBetween_comm y x] at hiy
  have hny := not_in_of_budget pti hsum (by omega)
  have hmem3 : ∀ v, v ∈ L.Y (L.s - 1) → v = x ∨ v = y ∨ v = z := by
    intro v hv; rw [hY] at hv; simpa only [mem_insert, mem_singleton] using hv
  obtain ⟨hP1, hP2⟩ := L.pend_in_ends hB hk pti
  have hPne : hd pti.out ≠ tl pti.inn := fun h =>
    pti.distinct _ (L.Y_interior hk hP1).1 (L.Y_interior hk hP1).2 ⟨Or.inr rfl, Or.inl h.symm⟩
  obtain ⟨e1, e2⟩ := logic_two hxy hyz hxz (hmem3 _ hP1) (hmem3 _ hP2) hPne
    (by rintro (h | h); exacts [hny (Or.inl h), hny (Or.inr h)])
  have hEi : InEnds pti x z := inEnds_of pti hxa hxb hza hzb e1 e2
  obtain ⟨dxy₀, dxy₁, hdxy, hxy₀, hxy₁⟩ := two_bonds hxS hyS hbxy
  obtain ⟨dyz₀, dyz₁, hdyz, hyz₀, hyz₁⟩ := two_bonds hyS hzS hbyz
  obtain ⟨dxz, hxz₀⟩ := one_bond hxS hzS hbxz
  obtain ⟨c, hc, φ, hφA, -, heO, heI⟩ := place_coreD coreDTable coreDTable_ok coreDTable_cover hM hxy hxz hyz
    (hB.1 hxS) (hB.1 hyS) (hB.1 hzS) (deg4 hB hxS hxa hxb) (deg4 hB hyS hya hyb) (deg4 hB hzS hza hzb)
    dxy₀ hxy₀ dxy₁ hxy₁ dyz₀ hyz₀ dyz₁ hyz₁ dxz hxz₀ hdxy hdyz pti (hnot x hx) (hnot y hy) (hnot z hz) hEi
  obtain ⟨hv, hok, hrc, hrel, hex⟩ := coreDTable_ok c hc
  have hoB : c.outB = none := outB_none_of coreDShape hrc (by decide)
  exact ⟨{
    cfg := c
    emb := φ
    valid := hv
    ok := hok
    rel := hrel
    extra := fun x => (extra_none hex hoB x).elim
    atoms := by rw [hY]; exact atoms_three hφA
    pin := pti
    bO := heO
    bI := heI
    oM := by intro X hX; cases hX
    oB := by intro X hX; cases hX }⟩

/-! ## The copy cell -/

theorem pc_copy {att : Att} (A : L.AttData att) {j : ℕ} (hpb : att = .pb j) :
    Nonempty (PCell M S a b 0 0 (fun _ _ => True) ∅ (L.reg j false) (some (L.reg j true)) (some (S \ L.H 0))
      1 1 3) := by
  subst hpb
  have hcase : 1 ≤ L.s ∧ j ≤ L.r ∧ crossBonds M (L.Z j) (L.Z (j + 1)) = 1 ∧ A.x ∈ L.Z j ∧
      A.x' ∈ L.Z (j + 1) := A.case
  obtain ⟨hs, hj, hc1, -, -⟩ := hcase
  obtain ⟨hαα', hset, -, -, -, -, -, -⟩ := A.pend hs
  obtain ⟨πx⟩ := L.port_reg hB A hM hT hA hj false (Or.inl (by simp [Att.hx]))
  obtain ⟨πe⟩ := L.port_reg hB A hM hT hA hj true (Or.inr (by simp [Att.he]))
  obtain ⟨πb⟩ := L.port_pend hB hM hT hA (k := 0) (by omega)
  have hPx : portSet (M := M) (S := S) (L.reg j false) = cross (L.Z j) (L.Z (j + 1)) ∪ {A.α} := by
    have h := L.portSet_flag hB A hj false (Or.inl (by simp [Att.hx]))
    simpa using h
  have hPe : portSet (M := M) (S := S) (L.reg j true) = cross (L.Z j) (L.Z (j + 1)) ∪ {A.α'} := by
    have h := L.portSet_flag hB A hj true (Or.inr (by simp [Att.he]))
    simpa using h
  have hPb : portSet (M := M) (S := S) (S \ L.H 0) = {A.α, A.α'} := by
    rw [portSet_compl, portSet_eq_cross, hset]
  rw [← card_cross (L.Z_sub hB (by omega)) (L.Z_sub hB (by omega))] at hc1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hc1
  have htZ : t ∈ cross (M := M) (S := S) (L.Z j) (L.Z (j + 1)) := by rw [ht]; exact mem_singleton_self t
  have hαt : A.α ≠ t := fun h => L.α_not_ZZ hB A hs hj (h ▸ htZ)
  have hα't : A.α' ≠ t := fun h => L.α'_not_ZZ hB A hs hj (h ▸ htZ)
  have htx : t ∈ portSet (M := M) (S := S) (L.reg j false) := by rw [hPx]; exact mem_union_left _ htZ
  have hte : t ∈ portSet (M := M) (S := S) (L.reg j true) := by rw [hPe]; exact mem_union_left _ htZ
  have hαx : A.α ∈ portSet (M := M) (S := S) (L.reg j false) := by rw [hPx]; simp
  have hα'e : A.α' ∈ portSet (M := M) (S := S) (L.reg j true) := by rw [hPe]; simp
  have hαb : A.α ∈ portSet (M := M) (S := S) (S \ L.H 0) := by rw [hPb]; simp
  have hα'b : A.α' ∈ portSet (M := M) (S := S) (S \ L.H 0) := by rw [hPb]; simp
  have hZin : ∀ {v h}, v ∈ L.Z j → v ∈ L.reg j h := fun hv => (L.mem_reg_Z hB (by omega) (by omega) hv).mpr le_rfl
  have hcompl := L.reg_sub_compl hB (i := j) (by omega)
  have hK : (A.α = πx.out ∧ t = πx.inn ∧ A.α' = πe.out ∧ t = πe.inn ∧ A.α = πb.out ∧ A.α' = πb.inn) ∨
      (A.α = πx.inn ∧ t = πx.out ∧ A.α' = πe.inn ∧ t = πe.out ∧ A.α = πb.inn ∧ A.α' = πb.out) := by
    rcases mem_cross.mp htZ with ⟨h1, -⟩ | ⟨-, h2⟩
    · have ht1 : t = πx.out := port_out_unique πx htx (hZin h1)
      have ht2 : t = πe.out := port_out_unique πe hte (hZin h1)
      have hα1 : A.α = πx.inn := other_inn πx hαx (ht1 ▸ hαt)
      have hα'1 : A.α' = πe.inn := other_inn πe hα'e (ht2 ▸ hα't)
      have hα2 : A.α = πb.inn := port_inn_unique πb hαb (by rw [hα1]; exact hcompl πx.inn_hd)
      have hα'2 : A.α' = πb.out := other_out πb hα'b (hα2 ▸ hαα'.symm)
      exact Or.inr ⟨hα1, ht1, hα'1, ht2, hα2, hα'2⟩
    · have ht1 : t = πx.inn := port_inn_unique πx htx (hZin h2)
      have ht2 : t = πe.inn := port_inn_unique πe hte (hZin h2)
      have hα1 : A.α = πx.out := other_out πx hαx (ht1 ▸ hαt)
      have hα'1 : A.α' = πe.out := other_out πe hα'e (ht2 ▸ hα't)
      have hα2 : A.α = πb.out := port_out_unique πb hαb (by rw [hα1]; exact hcompl πx.out_tl)
      have hα'2 : A.α' = πb.inn := other_inn πb hα'b (hα2 ▸ hαα'.symm)
      exact Or.inl ⟨hα1, ht1, hα'1, ht2, hα2, hα'2⟩
  have hα'x : A.α' ≠ πx.out ∧ A.α' ≠ πx.inn := by
    rcases hK with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
    · exact ⟨h1 ▸ hαα'.symm, h2 ▸ hα't⟩
    · exact ⟨h2 ▸ hα't, h1 ▸ hαα'.symm⟩
  obtain ⟨c, -, hv, hrel, hex, φ, heO, heI, ⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩, -⟩ :=
    place_copy πx πe πb t A.α A.α' hK hα'x
  exact ⟨{
    cfg := c
    emb := φ
    valid := hv
    ok := trivial
    rel := hrel
    extra := extra_some φ sdiff_subset πb hex hq hq1 hq2
    atoms := fun v => ⟨fun h => absurd h (Finset.notMem_empty v), fun ⟨u, _⟩ => u.elim0⟩
    pin := πx
    bO := heO
    bI := heI
    oM := by
      intro X hX pt
      obtain rfl := Option.some.inj hX
      exact ⟨p, hp, hp1.trans (port2_out_eq πe pt), hp2.trans (port2_inn_eq πe pt)⟩
    oB := by
      intro X hX pt
      obtain rfl := Option.some.inj hX
      exact ⟨q, hq, hq1.trans (port2_out_eq πb pt), hq2.trans (port2_inn_eq πb pt)⟩ }⟩

end Lay

end WaveTurbulence.TVine.Chart
