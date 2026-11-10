/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecCertDefs
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecSpec
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecContract
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecHX3
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecEng
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecMerge
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecFree
public import WaveTurbulence.Foundations.VineEst.VineEstS5C.P4.W2.RecInd

/-! # P4-W2 (session 18, step 4b): `termCertWG_rec`, the certificate of a term with exceptional records (kinds 0, 1, 3)

For a term `ψ0` of the top level with the row form `RowFormNE .. (pexOf recs) (bexOf recs) (xqOf recs)`, records `recs` with `RecSpec` (`kd ≠ 2`), the modulated term carries
`TermCertWG` (the top-level `TermCertW` with `R'' = R`; `termCertW_of_G`) at every size `β' ≥ q`, and `q ≤ certBeta P (recEng ..) (3^(order1+1)) Rb` where `Rb` is the native row bound
`C * 2 rowBoundH` off the exceptional rows, `bnd r` at the pair row of the record `r` and `1` at its branch row.  Ingredients: `badClauseP_rec`, `rows_merge` of the `RepConcl` of every record,
`freeDict_rec` with `hcontract_of_records` and `hX_rec`, `hind_exc`.
-/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
namespace WaveTurbulence.VineEstS5C.P4.W2
open VineParamContract TTree Reg Reg.Skeleton RegRed MeasureTheory WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS5A
  WaveTurbulence.VineEstS5C WaveTurbulence.VineEstS3 WaveTurbulence.VineEstS3Par.Eng WaveTurbulence.DegenVine WaveTurbulence.DegenVinePar
  WaveTurbulence.VineEstS5C.P2 WaveTurbulence.VineEstS5C.P3 WaveTurbulence.VineEstS5C.P4 WaveTurbulence.VineEstS4
  WaveTurbulence.VineEstS5B
open scoped ENNReal

theorem abs_sub_nat_le (a b D : ℕ) (ha : a ≤ D) (hb : b ≤ D) : |(a : ℝ) - b| ≤ D := by
  have h1 := (Nat.cast_le (α := ℝ)).2 ha
  have h2 := (Nat.cast_le (α := ℝ)).2 hb
  have h3 := Nat.cast_nonneg (α := ℝ) a
  have h4 := Nat.cast_nonneg (α := ℝ) b
  rw [abs_le]
  constructor <;> linarith


variable {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree}
variable {R : CLRegionData G U a b} {n : ℕ}

theorem prod_split_le {ι κ : Type*} [Fintype ι] [DecidableEq ι] (b Rn : ι → ℝ≥0∞) (S : Finset κ) (e1 e2 : κ → ι)
    (hinj1 : Set.InjOn e1 ↑S) (hinj2 : Set.InjOn e2 ↑S) (hdisj : ∀ k ∈ S, ∀ k' ∈ S, e1 k ≠ e2 k') (bnd : κ → ℝ≥0∞)
    (hn : ∀ ρ, ρ ∉ (S.image e1 ∪ S.image e2) → b ρ ≤ Rn ρ) (hr : ∀ k ∈ S, b (e1 k) * b (e2 k) ≤ bnd k) :
    ∏ ρ, b ρ ≤ (∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), Rn ρ) * ∏ k ∈ S, bnd k := by
  classical
  have hd : Disjoint (S.image e1) (S.image e2) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k', hk', h⟩ := Finset.mem_image.mp hx'
    exact hdisj k hk k' hk' h.symm
  have h1 : ∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), b ρ ≤ ∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), Rn ρ :=
    Finset.prod_le_prod' fun ρ hρ => hn ρ (Finset.mem_sdiff.mp hρ).2
  have h2 : ∏ ρ ∈ S.image e1 ∪ S.image e2, b ρ ≤ ∏ k ∈ S, bnd k := by
    rw [Finset.prod_union hd, Finset.prod_image hinj1, Finset.prod_image hinj2, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod' hr
  calc ∏ ρ, b ρ = (∏ ρ ∈ Finset.univ \ (S.image e1 ∪ S.image e2), b ρ) * ∏ ρ ∈ S.image e1 ∪ S.image e2, b ρ :=
        (Finset.prod_sdiff (Finset.subset_univ _)).symm
    _ ≤ _ := mul_le_mul' h1 h2

/-- The body of `termCertWG_rec` for the constant `C` (all the data of the chain, the families and the records are bound inside). -/
def TermRecBody {A : ℝ} (d : ℕ) (η : ℝ) (C : ℝ≥0∞) : Prop :=
    ∀ (P : WTParams), P.d = d → P.η = η →
      ∀ {w : ℕ} {G : Garden w} {U : Finset (GBranch G.tree)} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}, ∀ (Z0 : AmbP A P) (hA : 6561 ≤ A)
      (hgate : CoherentGateH P) (hinc : IncoherentGateH P) (hC1 : 1 ≤ P.C₁) (hL1 : 1 ≤ P.L)
      (hw : 0 ≤ P.gamma1 - Real.sqrt P.η) (hηγ : P.η ≤ P.γ) {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
      (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
      (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G) (hG : G.IsPlain)
      (layer : GNode (RD.forest hG) → ℕ) (hLayer : IsLayering (RD.garden hG) layer) (hlay : ∀ x, layer x ≤ p)
      (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4) (hl1 : clLocalOrder1 R ≤ P.N 1 ^ 4)
      (centre : Fin 4 → Mom P.d) (wBar : Mom P.d) (lam : ℝ)
      (hcoh : RowCoherent hM9 B RD hG layer hLayer
        (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar)
        P.L P.γ P.δ h p)
      (ψ0 : PsiT G P.d) (Dm : (Fin 3 → ℝ) → (GBranch G.tree → ℝ) → Prop) (recs : List (ExcRec G P.d))
      (hNE : RowFormNE RD hG P.L P.γ P.δ h layer hLayer R wBar ψ0 Dm (pexOf recs) (bexOf recs) (xqOf recs))
      (hDm : ∀ t u, u a = t 0 → (Dm t u ↔ DomX R (fun v => layer (RD.coreBranch hG v).toNode) (bexOf recs) (t 0) (t 1) (t 2) u))
      (hnp : (recs.map ExcRec.p0).Nodup) (hnb : (recs.map ExcRec.bj).Nodup)
      (hreg : ∀ r ∈ recs, r.p0 ∈ clRegionalPairs hG U) (hbjI : ∀ r ∈ recs, r.bj ∈ clInteriorBranches R)
      (hblkinj : ∀ r ∈ recs, ∀ r' ∈ recs, r.blk = r'.blk → r = r')
      (blkOf : ∀ r (hr : r ∈ recs), (assemblyPairBij hG B hM9 ⟨r.p0, hreg r hr⟩).1.val = r.blk)
      (hbjl : ∀ r ∈ recs, ∀ i : Fin (assemblyShape hM9 B).I, r.blk = i.val →
        r.bj = (assemblyClockAtomEquiv hM9 B (.inl ⟨i, 0⟩)).1)
      (hnorR : ∀ r ∈ recs, ∀ i : Fin (assemblyShape hM9 B).I, r.blk = i.val → (assemblyShape hM9 B).nor i = false)
      (kd : ExcRec G P.d → ℕ) (zc : ExcRec G P.d → Prop)
      (addr : ExcRec G P.d → Finset ((assemblyShape hM9 B).TVar × (assemblyShape hM9 B).TVar)) (bnd : ExcRec G P.d → ℝ≥0∞)
      (hspec : ∀ r (hr : r ∈ recs),
        RecSpec (P := P) (κ0 := kparOf P.L P.γ P.δ h wBar) B RD hG layer hM9 (ne_of_gt (lt_of_lt_of_le one_pos hL1)) r (hreg r hr) (hbjI r hr)
          (kd r) (zc r) (addr r) (bnd r))
      (hfreeR : ∀ i : Fin n, (∀ r ∈ recs, r.blk ≠ i.val) → (assemblyPieceAt B i).vineType.IsBad = true → ¬ AClause hM9 B RD hG layer i →
        ∃ v : (assemblyShape hM9 B).VIdx, v.1 = i ∧
          1 ≤ max (rowCoupleG hM9 B RD hG layer hLayer v) (rowTreeG hM9 B RD hG layer hLayer v))
      (Bx : Set (Fin 3 → ℝ)) (K : Set (Fin 4 → Mom P.d))
      (hBx : Bx ⊆ WaveTurbulence.VineEstS3Par.Eng.outBox
        (natEng hM9 B RD hG layer hLayer (qOutOf RD hG layer a b R) centre wBar lam))
      (hext : ∀ tt ∈ Bx, ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1)
      (hK : K = WaveTurbulence.VineEstS3Par.Eng.outSet
        (natEng hM9 B RD hG layer hLayer (qOutOf RD hG layer a b R) centre wBar lam) P.L P.γ P.η),
      ∃ q : ℝ≥0∞, (∀ β', q ≤ β' → TermCertWG (A := A) B hG (kparOf P.L P.γ P.δ h wBar) R (modPsi b lam ψ0) Bx K β') ∧
        ∃ Rb : Row (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) → ℝ≥0∞,
          q ≤ certBeta P (recEng hM9 B RD hG layer hLayer recs kd zc addr centre wBar lam) ((3 : ℝ) ^ (clLocalOrder1 R + 1)) Rb ∧
          (∀ ρ, (∀ r (hr : r ∈ recs), ρ ≠ Sum.inl (assemblyPairBij hG B hM9 ⟨r.p0, hreg r hr⟩) ∧
              ρ ≠ Sum.inr (assemblyBranchBij hM9 B ⟨r.bj, hbjI r hr⟩)) →
            Rb ρ = C * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh
              (recW hM9 B RD hG layer hLayer recs kd zc centre wBar lam) ρ)) ∧
          ∀ r (hr : r ∈ recs), Rb (Sum.inl (assemblyPairBij hG B hM9 ⟨r.p0, hreg r hr⟩)) = bnd r ∧
            Rb (Sum.inr (assemblyBranchBij hM9 B ⟨r.bj, hbjI r hr⟩)) = 1

/-- **The certificate of a term with records** (see the module docstring). -/
theorem termCertWG_rec {A : ℝ} (d : ℕ) (η : ℝ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, 1 ≤ C ∧ C ≠ ⊤ ∧ TermRecBody (rowSel := VineEst.RowSel.plain) (A := A) d η C := by
  classical
  obtain ⟨C0, hC00, hall⟩ := natRows_family d η hd
  refine ⟨C0 + 1, le_add_self, ENNReal.add_ne_top.2 ⟨hC00, ENNReal.one_ne_top⟩, ?_⟩
  unfold TermRecBody
  intro P hPd hPη w G U a b R n Z0 hA hgate hinc hC1 hL1 hw hηγ p hp h Bh hB hBpos hM9 B RD hG layer hLayer hlay hord hl1
    centre wBar lam hcoh ψ0 Dm recs hNE hDm hnp hnb hreg hbjI hblkinj blkOf hbjl hnorR kd zc addr bnd hspec hfreeR Bx K hBx hext hK
  have hd' : 1 ≤ P.d := hPd ▸ hd
  have hL0 : 0 < P.L := by linarith
  set C : ℝ≥0∞ := C0 + 1 with hCdef
  set qOut := qOutOf RD hG layer a b R with hqOut
  set bk := recBk B RD hG layer hM9 recs kd zc with hbk
  set W := recW hM9 B RD hG layer hLayer recs kd zc centre wBar lam with hW
  set wN := 30 * P.d - 1 with hwNd
  set wDec := 30 * P.d with hwDecd
  set cons := consX hM9 B (layC RD hG layer) (bexOf recs) (recAdd B hM9 recs zc addr) with hcons
  set g := recG B hM9 hG recs kd (rowCoupleG hM9 B RD hG layer hLayer) with hg
  set g' := rowTreeG hM9 B RD hG layer hLayer with hg'
  have hI := assemblyShape_I_pos hM9 B
  -- record bookkeeping
  obtain ⟨vpf, vbf, hvpf, hvbf⟩ := exists_row_maps hM9 B hG recs hreg hbjI
  have hvp : ∀ r ∈ recs, (assemblyPairOf hM9 B hG (vpf r)).1 = r.p0 := fun r hr => by
    rw [hvpf r hr, assemblyPairOf_bij hM9 B hG]
  have hvb : ∀ r ∈ recs, (assemblyBranchOf hM9 B (vbf r)).1 = r.bj := fun r hr => by
    rw [hvbf r hr, assemblyBranchOf_bij hM9 B]
  have hblk : ∀ r ∈ recs, ((vpf r).1 : ℕ) = r.blk := fun r hr => by rw [hvpf r hr]; exact blkOf r hr
  -- eligibility of the native rows
  have hel : ∀ v, CoupleEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v ∧
      TreeEligible hM9 B RD hG W P.L P.γ P.δ h layer hLayer (P.N (p + 1) ^ 4) p v := fun v =>
    eligible_of hM9 B RD hG layer hLayer W rfl rfl P.L P.γ P.δ h (P.N (p + 1) ^ 4) p hlay
      (rowSizes_of_order hM9 B RD hG hord) hcoh v
  have hqq : ∀ v, (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).2 ≤
      (rowQ hM9 B RD hG W P.L P.γ P.δ h layer hLayer (Sum.inr v)).1 := fun v => (hel v).2.1
  have hη6 : 6 * P.η ^ 6 ≤ P.η := Z0.hθη
  obtain ⟨Rw0, hRW0, hRS0, hRb0, hAe0, hWs0⟩ := hall P hPd hPη hgate hinc hη6 Z0.hη1 hC1 Z0.hδ hL1 hw hp hB hBpos hM9 B RD hG layer hLayer hlay W
    hel hqq wN wDec (by omega) (by omega) bk cons g g'
  obtain ⟨Mx, hmass, hMx⟩ := exists_mix_native hM9 B hG W hL0.ne' wBar
  have hq : ∀ v, W.q v + 1 ≤ P.D := fun v => Nat.succ_le_of_lt (lt_of_le_of_lt (hlay _) hp)
  have hqo : ∀ c, W.qOut c + 1 ≤ P.D := by
    intro c
    refine Nat.succ_le_of_lt (lt_of_le_of_lt ?_ hp)
    fin_cases c <;> simp only [W, recW, termW, step3W, hqOut, qOutOf] <;> exact hlay _
  have hS := structAdm_engDatum hM9 B hG W (L := P.L) (γ := P.γ) (η := P.η) hA hq hqo wN wDec (by omega) (by omega) bk cons g g'
  have hkd : ∀ r ∈ recs, kd r ≤ 3 := fun r hr => (hspec r hr).1
  have hm2 : ∀ r ∈ recs, kd r = 2 → ∀ i : Fin (assemblyShape hM9 B).I, r.blk = i.val → 0 < (assemblyShape hM9 B).m i := by
    intro r hr hk2 i hi
    have hi' : (assemblyPairBij hG B hM9 ⟨r.p0, hreg r hr⟩).1 = i := Fin.ext ((blkOf r hr).trans hi)
    rw [← hi']
    exact (hspec r hr).2.1 hk2
  have hbad : BadClauseP (engDatum hM9 B hG W wN wDec bk cons g g') := by
    refine badClauseP_rec B RD hG layer hLayer hM9 hG W wN wDec recs kd zc addr hblkinj hkd hm2
      (fun r hr => ?_) (fun r hr i hi => ?_) (fun r hr hk3 => ?_) hfreeR
    · exact ⟨(vpf r).1, (hblk r hr).symm, hbjl r hr _ (hblk r hr).symm⟩
    · have hi' : (assemblyPairBij hG B hM9 ⟨r.p0, hreg r hr⟩).1 = i := Fin.ext ((blkOf r hr).trans hi)
      rw [← hi']
      exact (hspec r hr).2.2.1
    · exact ⟨vpf r, hvp r hr, hblk r hr⟩
  have hgap : ∀ i (hh : (engDatum hM9 B hG W wN wDec bk cons g g').S.nor i = false ∧
      (engDatum hM9 B hG W wN wDec bk cons g g').badKind i = 2 ∧ 0 < (engDatum hM9 B hG W wN wDec bk cons g g').S.m i),
      |(((engDatum hM9 B hG W wN wDec bk cons g g').q (.inl ⟨i, ⟨1, by omega⟩⟩) : ℕ) : ℝ) -
        (((engDatum hM9 B hG W wN wDec bk cons g g').q (.inr (.inl ⟨i, ⟨0, hh.2.2⟩⟩)) : ℕ) : ℝ)| ≤ (P.D : ℝ) :=
    fun i hh => abs_sub_nat_le _ _ P.D (Nat.le_of_succ_le (hq _)) (Nat.le_of_succ_le (hq _))
  let Z := ambW_engDatum Z0 hM9 B hG W wN wDec bk cons g g' hS hbad Mx (P.D : ℝ) (Nat.cast_nonneg _) hgap (by omega)
    (by rw [assemblyShape_M]; exact hl1)
  have hleafmem : ∀ tt ∈ Bx, WaveTurbulence.VineEstS3.leafT qOut (LeafPos B (Lvl.top B)) (LeafNeg B (Lvl.top B)) tt ∈
      WaveTurbulence.VineEstS3.Eng.outBox (sourceSumintDatum hM9 B hG W) := fun tt htt =>
    leafT_mem_boxQ qOut _ _ (hBx htt)
  -- the effective output times
  set Bx' : Set (Fin 3 → ℝ) := (fun tt => WaveTurbulence.VineEstS3.leafT qOut (LeafPos B (Lvl.top B)) (LeafNeg B (Lvl.top B)) tt) '' Bx
    with hBx'def
  have hBx'sub : Bx' ⊆ outBox (engDatum hM9 B hG W wN wDec bk cons g g') := by
    rintro _ ⟨tt, htt, rfl⟩
    exact leafT_mem_boxQ qOut _ _ (hBx htt)
  have hext' : ∀ tt ∈ Bx', ((layC RD hG layer a : ℕ) : ℝ) < tt 0 ∧ tt 0 < (layC RD hG layer a : ℕ) + 1 := by
    rintro _ ⟨tt, htt, rfl⟩
    beta_reduce
    rw [WaveTurbulence.VineEstS3.leafT_zero qOut _ _ tt]
    exact hext tt htt
  have hrc := fun r (hr : r ∈ recs) => (hspec r hr).2.2.2.2 W wN wDec (by omega) (by omega) bk (bexOf recs) (recAdd B hM9 recs zc addr) g g'
    rfl Bx' hBx'sub hext' (fun hz => addr_subset_recAdd B hM9 recs zc addr hr hz)
  choose! ε Xr hεabs hPU hzero hlink using hrc
  have hinjp : ∀ k ∈ recs.toFinset, ∀ k' ∈ recs.toFinset, vpf k = vpf k' → k = k' := by
    intro k hk k' hk' hkk
    have h1 : k.p0 = k'.p0 := by
      rw [← hvp k (List.mem_toFinset.mp hk), ← hvp k' (List.mem_toFinset.mp hk'), hkk]
    exact List.inj_on_of_nodup_map hnp (List.mem_toFinset.mp hk) (List.mem_toFinset.mp hk') h1
  have hinjb : ∀ k ∈ recs.toFinset, ∀ k' ∈ recs.toFinset, vbf k = vbf k' → k = k' := by
    intro k hk k' hk' hkk
    have h1 : k.bj = k'.bj := by
      rw [← hvb k (List.mem_toFinset.mp hk), ← hvb k' (List.mem_toFinset.mp hk'), hkk]
    exact List.inj_on_of_nodup_map hnb (List.mem_toFinset.mp hk) (List.mem_toFinset.mp hk') h1
  obtain ⟨Rw', hRw'1, hRw'2⟩ := rows_merge (P := P) hI Rw0 recs.toFinset vpf vbf hinjp hinjb ε
    (fun r => f0Of P.η (vpf r).1 (kd r)) Xr bnd Bx'
    (fun k hk => by
      have := hPU k (List.mem_toFinset.mp hk)
      rwa [← hvpf k (List.mem_toFinset.mp hk), ← hvbf k (List.mem_toFinset.mp hk)] at this)
  have hnonexc : ∀ ρ, NonExc hM9 B hG W wN wDec bk cons g g' (vpSet hM9 B hG recs) (vbSet hM9 B recs) ρ → Rw' ρ = Rw0 ρ := by
    intro ρ hρ
    refine hRw'1 ρ fun k hk => ⟨fun h' => ?_, fun h' => ?_⟩
    · have hk' := List.mem_toFinset.mp hk
      exact hρ.1 (vpf k) h' ((mem_vpSet hM9 B hG recs _).mpr (by rw [hvp k hk']; exact mem_pexOf.mpr ⟨k, hk', rfl⟩))
    · have hk' := List.mem_toFinset.mp hk
      exact hρ.2 (vbf k) h' ((mem_vbSet hM9 B recs _).mpr (by rw [hvb k hk']; exact mem_bexOf.mpr ⟨k, hk', rfl⟩))
  have hRW : ∀ ρ (cl : Fin 3 → ℝ), NonExc hM9 B hG W wN wDec bk cons g g' (vpSet hM9 B hG recs) (vbSet hM9 B recs) ρ →
      ![cl 0, cl 1] ∈ rowBx hM9 B RD hG layer hLayer W P.L P.γ P.δ h ρ → ∀ r k,
      (Rw' ρ).W cl r k = (assemblyClockedS hM9 B RD hG W P.L P.γ P.δ h layer hLayer).W ρ ![cl 0, cl 1] k := by
    intro ρ cl hρ hcl r k
    rw [hnonexc ρ hρ]
    exact hRW0 ρ cl hcl r k
  have hRS : ∀ ρ i, NonExc hM9 B hG W wN wDec bk cons g g' (vpSet hM9 B hG recs) (vbSet hM9 B recs) ρ →
      (Rw' ρ).slot i = natSlot hM9 B hG ρ i := by
    intro ρ i hρ
    rw [hnonexc ρ hρ]
    exact hRS0 ρ i
  have hAe' : ∀ ρ, (Rw' ρ).Ae hI := by
    intro ρ
    by_cases hex : ∃ k ∈ recs.toFinset, ρ = Sum.inl (vpf k) ∨ ρ = Sum.inr (vbf k)
    · obtain ⟨k, hk, hρ | hρ⟩ := hex
      · subst hρ; exact (hRw'2 k hk).1
      · subst hρ; exact (hRw'2 k hk).2.1
    · push_neg at hex
      rw [hRw'1 ρ fun k hk => hex k hk]
      exact hAe0 ρ
  have hWs' : ∀ ρ cl r k, (Rw' ρ).W cl r k = ∑' m, (Rw' ρ).c m r k * WaveTurbulence.VineEstS3.FS.fsPhase m cl := by
    intro ρ cl r k
    by_cases hex : ∃ k ∈ recs.toFinset, ρ = Sum.inl (vpf k) ∨ ρ = Sum.inr (vbf k)
    · obtain ⟨k', hk, hρ | hρ⟩ := hex
      · subst hρ; exact (hRw'2 k' hk).2.2.1 cl r k
      · subst hρ; exact (hRw'2 k' hk).2.2.2.1 cl r k
    · push_neg at hex
      rw [hRw'1 ρ fun k hk => hex k hk]
      exact hWs0 ρ cl r k
  have hbkr : ∀ r ∈ recs, bk ((vpf r).1) = bkVal (kd r) (zc r) := fun r hr =>
    recBk_of_rec B RD hG layer hM9 recs kd zc hblkinj hr _ (hblk r hr).symm
  have hbkn : ∀ i, (∀ r ∈ recs, (vpf r).1 ≠ i) → bk i ≠ 1 ∧ bk i ≠ 2 := by
    intro i hne
    have hn : ∀ r ∈ recs, r.blk ≠ i.val := fun r hr h' => hne r hr (Fin.ext ((hblk r hr).trans h'))
    rw [hbk, recBk_of_not B RD hG layer hM9 recs kd zc i hn]
    rcases canonBadKind_cases hM9 B RD hG layer i with h' | h' <;> rw [h'] <;> decide
  have hLP : LeafPos B (Lvl.top B) ↔ (b.child R.positive).1.2 ∉ (G.tree (b.child R.positive).1.1).branching := by
    unfold LeafPos; rw [top_region_eq B]; exact Iff.rfl
  have hLN : LeafNeg B (Lvl.top B) ↔ (b.child R.negative).1.2 ∉ (G.tree (b.child R.negative).1.1).branching := by
    unfold LeafNeg; rw [top_region_eq B]; exact Iff.rfl
  have hD : ∀ tt ∈ Bx, ∀ (β : Fin 4 → (Fin P.d → ℤ))
      (hβ : ((G.sign (Lvl.top B).c.a.toNode : ℤ) • (β 0 - β 1)) = β 2 - β 3),
      sumintBoundary (G.sign (Lvl.top B).c.a.toNode) (fun j => W.wBar + latticePoint P.L (β j)) ∈
        outSet (engDatum hM9 B hG W wN wDec bk cons g g') P.L P.γ P.η →
      FreeDict hM9 B hG W hL0.ne' P.γ P.δ P.η W.wBar β hβ
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B hG W wN wDec bk cons g g').qOut (LeafPos B (Lvl.top B)) (LeafNeg B (Lvl.top B)) tt)
        (modPsi b lam ψ0) wN wDec bk cons g g' Mx (allCR Rw') := by
    intro tt0 htt0 β hβ hout
    have hmemB' : WaveTurbulence.VineEstS3.leafT qOut (LeafPos B (Lvl.top B)) (LeafNeg B (Lvl.top B)) tt0 ∈ Bx' := ⟨tt0, htt0, rfl⟩
    have hr1 : ‖sumintBoundary (G.sign a.toNode) (fun j => wBar + latticePoint P.L (β j)) 0 -
        sumintBoundary (G.sign a.toNode) (fun j => wBar + latticePoint P.L (β j)) 1‖ ≤ 1 := by
      refine hout.2.2.2.trans ?_
      exact Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    refine freeDict_rec hM9 B RD hG W hL0.ne' P.γ P.δ P.η h layer hLayer wBar β hβ _ (hleafmem tt0 htt0) (modPsi b lam ψ0) ψ0 lam
      (fun x t u => rfl) Dm (pexOf recs) (bexOf recs) (xqOf recs) hNE hDm wN wDec bk (recAdd B hM9 recs zc addr) g g' Mx Rw'
      (vpSet hM9 B hG recs) (vbSet hM9 B recs) (mem_vpSet hM9 B hG recs) (mem_vbSet hM9 B recs) hRW hRS (fun v => rfl)
      (fun x => hMx β hβ x) rfl ?_ ?_ ?_ ?_
    · by_cases hh : LeafPos B (Lvl.top B)
      · refine Or.inr ?_
        rw [WaveTurbulence.VineEstS3.leafT_one]
        simp only [hh, if_true]
        exact qOutOf_one_le hM9 B RD hG layer hLayer hI
      · exact Or.inl (not_not.mp (mt hLP.mpr hh))
    · by_cases hh : LeafNeg B (Lvl.top B)
      · refine Or.inr ?_
        rw [WaveTurbulence.VineEstS3.leafT_two]
        simp only [hh, if_true]
        exact qOutOf_two_le hM9 B RD hG layer hLayer hI
      · exact Or.inl (not_not.mp (mt hLN.mpr hh))
    · intro x
      exact (hcontract_of_records hM9 B recs hnp hreg zc addr (fun r hr => (hspec r hr).2.2.2.1) _
        (clExtendIndices R ((clNormalizedChainEquiv hL0.ne' B wBar β hβ hM9).symm x).1)
        (fun τ p => qRow RD hG P.L P.γ P.δ h layer hLayer wBar _ (clExtendIndices R ((clNormalizedChainEquiv hL0.ne' B wBar β hβ hM9).symm x).1)
          (clLocalClock R _ (assemblyClockEquiv hM9 B τ)) p)
        (fun τ v => tRow RD hG P.L P.γ P.δ h layer hLayer wBar _ (clExtendIndices R ((clNormalizedChainEquiv hL0.ne' B wBar β hβ hM9).symm x).1)
          (clLocalClock R _ (assemblyClockEquiv hM9 B τ)) v)).mono (fun τ h' _ => h')
    · intro x
      refine hX_rec hM9 B hG W hL0.ne' P.η wBar β hβ _ x wN wDec bk cons g g' Rw' Bx' hmemB' hr1 recs hnp hnb hreg kd zc
        (fun r => (vpf r).1) (fun r hr r' hr' h' => hblkinj r hr r' hr' (by rw [← hblk r hr, ← hblk r' hr', h'])) hkd hbkr hbkn
        (fun r hr => hnorR r hr _ (hblk r hr).symm) vpf vbf hvp hvb (fun r hr => ⟨ε r, Xr r, bnd r, hRw'2 r (List.mem_toFinset.mpr hr), hzero r hr, ?_⟩)
      intro tt τ
      have := hlink r hr β hβ x tt τ
      rwa [← hvpf r hr, ← hvbf r hr] at this
  have hind' : ∀ (t : Fin 3 → ℝ) (β'' : Fin 4 → Mom P.d) (κ : CLLocalDecoration R P.L W.wBar β'') (u : GBranch G.tree → ℝ),
      u (Lvl.top B).c.a = t 0 → modPsi b lam ψ0 (clExtendIndices R κ.1) t u = modPsi b lam ψ0 (clExtendIndices R κ.1)
        (WaveTurbulence.VineEstS3.leafT (engDatum hM9 B hG W wN wDec bk cons g g').qOut (LeafPos B (Lvl.top B)) (LeafNeg B (Lvl.top B)) t) u := by
    intro t β'' κ u hu
    show Complex.exp _ * ψ0 _ t u = Complex.exp _ * ψ0 _ _ u
    congr 1
    refine hind_exc RD hG P.L P.γ P.δ h layer hLayer wBar ψ0 Dm recs hNE hDm t _
      (WaveTurbulence.VineEstS3.leafT_zero qOut _ _ t).symm ?_ ?_ β'' κ u hu
    · by_cases hh : LeafPos B (Lvl.top B)
      · exact Or.inl (hLP.mp hh)
      · exact Or.inr (by rw [WaveTurbulence.VineEstS3.leafT_one]; simp [hh])
    · by_cases hh : LeafNeg B (Lvl.top B)
      · exact Or.inl (hLN.mp hh)
      · exact Or.inr (by rw [WaveTurbulence.VineEstS3.leafT_two]; simp [hh])
  -- the bound on the product of the row sizes
  let e1 : ExcRec G P.d → Row (engDatum hM9 B hG W wN wDec bk cons g g') := fun k => Sum.inl (vpf k)
  let e2 : ExcRec G P.d → Row (engDatum hM9 B hG W wN wDec bk cons g g') := fun k => Sum.inr (vbf k)
  let Rb : Row (engDatum hM9 B hG W wN wDec bk cons g g') → ℝ≥0∞ := fun ρ =>
    if h1 : ∃ k ∈ recs.toFinset, ρ = e1 k then bnd h1.choose
    else if ∃ k ∈ recs.toFinset, ρ = e2 k then 1
    else C * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ)
  have hRbl : ∀ k ∈ recs.toFinset, Rb (e1 k) = bnd k := by
    intro k hk
    have h1 : ∃ k' ∈ recs.toFinset, e1 k = e1 k' := ⟨k, hk, rfl⟩
    dsimp only [Rb]
    rw [dif_pos h1]
    have := hinjp _ h1.choose_spec.1 k hk (Sum.inl.inj h1.choose_spec.2).symm
    rw [this]
  have hRbr : ∀ k ∈ recs.toFinset, Rb (e2 k) = 1 := by
    intro k hk
    have h1 : ¬ ∃ k' ∈ recs.toFinset, e2 k = e1 k' := by
      rintro ⟨k', -, h'⟩; exact Sum.inr_ne_inl h'
    have h2 : ∃ k' ∈ recs.toFinset, e2 k = e2 k' := ⟨k, hk, rfl⟩
    dsimp only [Rb]
    rw [dif_neg h1, if_pos h2]
  have hRbn : ∀ ρ, (∀ k ∈ recs.toFinset, ρ ≠ e1 k ∧ ρ ≠ e2 k) →
      Rb ρ = C * ENNReal.ofReal (2 * rowBoundH hM9 B RD hG layer hLayer P Bh W ρ) := by
    intro ρ hρ
    have h1 : ¬ ∃ k' ∈ recs.toFinset, ρ = e1 k' := by
      rintro ⟨k', hk', h'⟩; exact (hρ k' hk').1 h'
    have h2 : ¬ ∃ k' ∈ recs.toFinset, ρ = e2 k' := by
      rintro ⟨k', hk', h'⟩; exact (hρ k' hk').2 h'
    dsimp only [Rb]
    rw [dif_neg h1, if_neg h2]
  have hprod : ∏ ρ, (Rw' ρ).b ≤ ∏ ρ, Rb ρ := by
    have h1 := prod_split_le (fun ρ => (Rw' ρ).b) Rb recs.toFinset e1 e2
      (fun k hk k' hk' h' => hinjp k hk k' hk' (Sum.inl.inj h')) (fun k hk k' hk' h' => hinjb k hk k' hk' (Sum.inr.inj h')) 
      (fun k _ k' _ => Sum.inl_ne_inr) bnd
      (fun ρ hρ => by
        have hcond : ∀ k ∈ recs.toFinset, ρ ≠ e1 k ∧ ρ ≠ e2 k := fun k hk =>
          ⟨fun h' => hρ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k, hk, h'.symm⟩)),
           fun h' => hρ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨k, hk, h'.symm⟩))⟩
        rw [hRw'1 ρ hcond, hRbn ρ hcond]
        exact (hRb0 ρ).trans (mul_le_mul' (le_self_add) le_rfl))
      (fun k hk => (hRw'2 k hk).2.2.2.2.1)
    have hexc : ∏ ρ ∈ recs.toFinset.image e1 ∪
        recs.toFinset.image e2, Rb ρ = ∏ k ∈ recs.toFinset, bnd k := by
      have hd : Disjoint (recs.toFinset.image e1)
          (recs.toFinset.image e2) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨k', -, h'⟩ := Finset.mem_image.mp hx'
        exact Sum.inr_ne_inl h'
      have hI1 : Set.InjOn e1 ↑recs.toFinset :=
        fun k hk k' hk' h' => hinjp k hk k' hk' (Sum.inl.inj h')
      have hI2 : Set.InjOn e2 ↑recs.toFinset :=
        fun k hk k' hk' h' => hinjb k hk k' hk' (Sum.inr.inj h')
      rw [Finset.prod_union hd, Finset.prod_image hI1, Finset.prod_image hI2,
        Finset.prod_congr rfl hRbl, Finset.prod_congr rfl hRbr, Finset.prod_const_one, mul_one]
    refine h1.trans (le_of_eq ?_)
    rw [← hexc]
    exact Finset.prod_sdiff (Finset.subset_univ _)
  refine ⟨Regref.traceConst (r := 3) (2 * P.η ^ 8) WaveTurbulence.VineEstS3.chiUnit ^ 2 * (Z.pre * ∏ ρ, (Rw' ρ).b),
    fun β' hβ' => ⟨n, hM9, B, W, wN, wDec, bk, cons, g, g', Z, Rw', hL0.ne', hAe', hWs', rfl, hBx, hK, hind', hD, hβ'⟩,
    Rb, ?_, ?_, ?_⟩
  · rw [← hmass]
    exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hprod)
  · intro ρ hρ
    refine hRbn ρ fun k hk => ?_
    have hk' := List.mem_toFinset.mp hk
    constructor
    · show ρ ≠ Sum.inl (vpf k)
      rw [hvpf k hk']; exact (hρ k hk').1
    · show ρ ≠ Sum.inr (vbf k)
      rw [hvbf k hk']; exact (hρ k hk').2
  · intro r hr
    refine ⟨?_, ?_⟩
    · rw [← hvpf r hr]; exact hRbl r (List.mem_toFinset.mpr hr)
    · rw [← hvbf r hr]; exact hRbr r (List.mem_toFinset.mpr hr)

end WaveTurbulence.VineEstS5C.P4.W2
