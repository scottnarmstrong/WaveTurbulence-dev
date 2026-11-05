/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceRealType1
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceChainRoot
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceType2Fold
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMomentumHomogeneity
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceNstarRoots

/-! # Exact recursive Mstar and Nstar identification of the original source folds -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links Reg TTree

variable {d w : ℕ} {F : Mom d → ℝ} {B : ℝ}

mutual
/-- The complete original real source fold equals the literal recursive
Mstar, with positive factor2 for each link. The local special condition
permits ambient marks outside the current recursive sub-code. -/
theorem realCplFold_eq_Mstar (hd : 3 ≤ d) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (Q : RegCpl) (hdom : Q.dominant = true) (Z : Finset (Fin w × Path))
    (a b : Fin w × Path) (hab : Indep a b)
    (hZ : ∀ z ∈ (Q.linksAt a b).map Prod.fst, z ∈ Z →
      ∃ i : Fin 3, (z,addrExt z [i]) ∈ Q.linksAt a b) (k : Mom d) :
    realCplFold F Q Z a b k = (2:ℝ)^(Q.linksAt a b).length*Q.Mstar F Z a b k := by
  classical
  cases Q with
  | triv =>
    simp only [realCplFold,RegCpl.linksAt,List.map_nil,addressAppAlong,cplLeafProduct_triv,
      Complex.ofReal_re,List.length_nil,pow_zero,one_mul,RegCpl.Mstar]
  | type1 c Q₁ Q₂ Q₃ =>
    have h₃ := (Bool.and_eq_true_iff.mp hdom).2
    have h₁₂ := (Bool.and_eq_true_iff.mp hdom).1
    have h₁ := (Bool.and_eq_true_iff.mp h₁₂).1
    have h₂ := (Bool.and_eq_true_iff.mp h₁₂).2
    have hnd := source_chosen_nodup (.type1 c Q₁ Q₂ Q₃) a b hab
    have hZ₁ := special_on_sublinks _ (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0]))
      (fun l hl => List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hl))) hnd Z hZ
    have hZ₂ := special_on_sublinks _ (Q₂.linksAt (addrExt b [1]) (addrExt a [1]))
      (fun l hl => List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hl))) hnd Z hZ
    have hZ₃ := special_on_sublinks _ (Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2]))
      (fun l hl => List.mem_cons_of_mem _ (List.mem_append_right _ hl)) hnd Z hZ
    have hr := type1_root_not_mem_locally_special c Q₁ Q₂ Q₃ a b hab Z hZ
    have hi₁ (r : Mom d) := realCplFold_eq_Mstar hd hB hF Q₁ h₁ Z _ _ (hab.ext _ _) hZ₁ r
    have hi₂ (r : Mom d) := realCplFold_eq_Mstar hd hB hF Q₂ h₂ Z _ _ (hab.symm.ext _ _) hZ₂ r
    have hi₃ (r : Mom d) := realCplFold_eq_Mstar hd hB hF Q₃ h₃ Z _ _ (hab.ext _ _) hZ₃ r
    let n₁ := (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0])).length
    let n₂ := (Q₂.linksAt (addrExt b [1]) (addrExt a [1])).length
    let n₃ := (Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2])).length
    let M₁ := Q₁.Mstar F Z (addrExt a [0]) (addrExt b [c.partner 0])
    let M₂ := Q₂.Mstar F Z (addrExt b [1]) (addrExt a [1])
    let M₃ := Q₃.Mstar F Z (addrExt a [2]) (addrExt b [c.partner 2])
    have he : (fun k₁ k₂ k₃ =>
        realCplFold F Q₁ Z (addrExt a [0]) (addrExt b [c.partner 0]) k₁ *
        realCplFold F Q₂ Z (addrExt b [1]) (addrExt a [1]) k₂ *
        realCplFold F Q₃ Z (addrExt a [2]) (addrExt b [c.partner 2]) k₃) =
        (fun k₁ k₂ k₃ => ((2:ℝ)^n₁*2^n₂*2^n₃)*(M₁ k₁*M₂ k₂*M₃ k₃)) := by
      funext k₁ k₂ k₃
      rw [hi₁,hi₂,hi₃]
      change (2^n₁*M₁ k₁)*(2^n₂*M₂ k₂)*(2^n₃*M₃ k₃) = _
      ring
    have hn : ((RegCpl.type1 c Q₁ Q₂ Q₃).linksAt a b).length = n₁+n₂+n₃+1 := by
      simp only [RegCpl.linksAt,List.length_cons,List.length_append]
      rfl
    rw [realCplFold_type1 hd c Q₁ Q₂ Q₃ hB hF Z a b hab k hr,he,resIntegral_const_mul,
      RegCpl.Mstar,hn]
    simp only [pow_add,pow_succ]
    ring
  | type2 Xp Xm Qlp =>
    have hq := (Bool.and_eq_true_iff.mp hdom).2
    have hpm := (Bool.and_eq_true_iff.mp hdom).1
    have hp := (Bool.and_eq_true_iff.mp hpm).1
    have hm := (Bool.and_eq_true_iff.mp hpm).2
    have hnd := source_chosen_nodup (.type2 Xp Xm Qlp) a b hab
    have hZp := special_on_sublinks _ (Xp.linksAt 1 a)
      (fun l hl => List.mem_append_left _ (List.mem_append_left _ hl)) hnd Z hZ
    have hZm := special_on_sublinks _ (Xm.linksAt (-1) b)
      (fun l hl => List.mem_append_left _ (List.mem_append_right _ hl)) hnd Z hZ
    have hZq := special_on_sublinks _ (Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath))
      (fun l hl => List.mem_append_right _ hl) hnd Z hZ
    apply Complex.ofReal_injective
    rw [ofReal_realCplFold hd (.type2 Xp Xm Qlp) (by omega) (by omega) hB hF Z a b hab k 0,
      addressAppAlong_type2 hd hB hF Xp Xm hp hm Qlp Z a b hab k 0,
      addressAppAlong_chain_eq_Nstar hd hB hF Xp hp Z 1 a hZp k (fun _ => k) 0,
      addressAppAlong_chain_eq_Nstar hd hB hF Xm hm Z (-1) b hZm k (fun _ => k) 0,
      ← ofReal_realCplFold hd Qlp (by omega) (by omega) hB hF Z _ _ (hab.ext _ _) k 0,
      realCplFold_eq_Mstar hd hB hF Qlp hq Z _ _ (hab.ext _ _) hZq k]
    simp only [RegCpl.linksAt,List.length_append,RegCpl.Mstar,Complex.ofReal_mul,
      Complex.ofReal_pow,Complex.ofReal_ofNat,pow_add]
    ring
termination_by structural Q

/-- The complete original paired-chain source fold equals the literal
recursive Nstar with one positive factor2 per link. -/
theorem addressAppAlong_chain_eq_Nstar (hd : 3 ≤ d) (hB : 0 ≤ B)
    (hF : Fourier.spatialNorm (40*d) (40*d) (fun k => (F k:ℂ)) ≤ ENNReal.ofReal B)
    (X : RegChain) (hdom : X.dominant = true) (Z : Finset (Fin w × Path))
    (ζ : ℤˣ) (a : Fin w × Path)
    (hZ : ∀ z ∈ (X.linksAt ζ a).map Prod.fst, z ∈ Z →
      ∃ i : Fin 3, (z,addrExt z [i]) ∈ X.linksAt ζ a)
    (k : Mom d) (cont : Fin w × Path → Mom d)
    (θ : Fin w × Path → Mom d × Mom d) :
    addressAppAlong Z ((X.linksAt ζ a).map Prod.fst)
      (fun θ => chainLeafProduct (fun k => (F k:ℂ)) θ X ζ a k cont) θ =
    (2:ℂ)^(X.linksAt ζ a).length*(X.Nstar F Z ζ a k:ℂ) := by
  classical
  cases X with
  | nil => simp only [RegChain.linksAt,List.map_nil,addressAppAlong,chainLeafProduct_nil,
      List.length_nil,pow_zero,RegChain.Nstar,Complex.ofReal_one,one_mul]
  | pair m Qr Qg inner rest =>
    cases inner with
    | pair mi Qri Qgi ii ri => simp [RegChain.dominant,RegChain.isNil] at hdom
    | nil =>
      have hs := (Bool.and_eq_true_iff.mp hdom).2
      have hrg := (Bool.and_eq_true_iff.mp hdom).1
      have hg := (Bool.and_eq_true_iff.mp hrg).2
      have hr := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hrg).1).2
      let ar := (miniRedRoots m ζ a).1
      let br := (miniRedRoots m ζ a).2
      let ag := (miniGreenRoots m ζ a).1
      let bg := (miniGreenRoots m ζ a).2
      let ζs := slotSign (slotSign ζ m.c) m.lone
      let as := addrExt a [m.c,m.lone]
      have hnd := source_chain_chosen_nodup (.pair m Qr Qg .nil rest) ζ a
      have hZr := special_on_sublinks _ (Qr.linksAt ar br) (fun l hl => by
        rw [chain_linksAt_pair_nil_roots]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hl))) hnd Z hZ
      have hZg := special_on_sublinks _ (Qg.linksAt ag bg) (fun l hl => by
        rw [chain_linksAt_pair_nil_roots]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _ hl))) hnd Z hZ
      have hZs := special_on_sublinks _ (rest.linksAt ζs as) (fun l hl => by
        rw [chain_linksAt_pair_nil_roots]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ hl)) hnd Z hZ
      have hfr : realCplFold F Qr Z ar br =
          fun r => (2:ℝ)^(Qr.linksAt ar br).length*Qr.Mstar F Z ar br r := by
        funext r
        exact realCplFold_eq_Mstar hd hB hF Qr hr Z ar br (miniRedRoots_indep m ζ a) hZr r
      have hfg : realCplFold F Qg Z ag bg =
          fun r => (2:ℝ)^(Qg.linksAt ag bg).length*Qg.Mstar F Z ag bg r := by
        funext r
        exact realCplFold_eq_Mstar hd hB hF Qg hg Z ag bg (miniGreenRoots_indep m ζ a) hZg r
      have hactual := addressAppAlong_chain_pair_nil_root hd hB hF m Qr Qg rest hs Z ζ a k cont 1 θ
      simp only [one_mul] at hactual
      rw [hactual,addressAppAlong_chain_eq_Nstar hd hB hF rest hs Z ζs as hZs k cont 0,
        hfr,hfg,binaryMomentumFunction_const_mul,Nstar_pair_nil_roots]
      split_ifs <;> simp only [pvResonantIntegral_const_mul,resIntegral_const_mul,
        chain_linksAt_pair_nil_roots,List.length_cons,List.length_append,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,pow_add,pow_succ] <;> ring
termination_by structural X
end

end WaveTurbulence.RegAsymp
