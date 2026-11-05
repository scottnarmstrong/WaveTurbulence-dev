/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.PartitionEncloseConstructor

/-! # Legality of the literal outer-pair enclosure construction -/

public section
namespace WaveTurbulence.Reg.PairPartition

/-- Enclosing a legal partition by a first/last outer pair preserves legality. -/
theorem enclose_legal {n : ℕ} (P : PairPartition n) (hP : P.Legal) : P.enclose.Legal := by
  intro a b c d hAB hBC hCD hAC hBD
  have haPos : 0 < a.val := by
    by_contra hn
    have ha0 : a = 0 := Fin.ext (by change a.val = 0; omega)
    have hh := hAC
    rw [ha0] at hh
    change enclosePartner P 0 = c at hh
    rw [enclosePartner_zero] at hh
    have hc := congrArg Fin.val hh
    change n+1 = c.val at hc
    have hd := d.isLt
    change c.val < d.val at hCD
    omega
  have hdLt : d.val < n+1 := by
    by_contra hn
    have hdLast : d = Fin.last (n+1) := Fin.ext (by change d.val = n+1; have := d.isLt; omega)
    have hh := congrArg P.enclose.pair hBD
    rw [P.enclose.involutive,hdLast] at hh
    change b = enclosePartner P (Fin.last (n+1)) at hh
    rw [enclosePartner_last] at hh
    have hb := congrArg Fin.val hh
    change b.val = 0 at hb
    change a.val < b.val at hAB
    omega
  have hab : a.val < b.val := hAB
  have hbc : b.val < c.val := hBC
  have hcd : c.val < d.val := hCD
  let A : Fin n := ⟨a.val-1,by omega⟩
  let B : Fin n := ⟨b.val-1,by omega⟩
  let C : Fin n := ⟨c.val-1,by omega⟩
  let D : Fin n := ⟨d.val-1,by omega⟩
  have hA : A.castSucc.succ = a := Fin.ext (by change (a.val-1)+1 = a.val; omega)
  have hB : B.castSucc.succ = b := Fin.ext (by change (b.val-1)+1 = b.val; omega)
  have hC : C.castSucc.succ = c := Fin.ext (by change (c.val-1)+1 = c.val; omega)
  have hD : D.castSucc.succ = d := Fin.ext (by change (d.val-1)+1 = d.val; omega)
  have hpAC : P.pair A = C := by
    rw [← hA,← hC] at hAC
    change enclosePartner P A.castSucc.succ = C.castSucc.succ at hAC
    rw [enclosePartner_inner] at hAC
    have hv := congrArg Fin.val hAC
    exact Fin.ext (Nat.add_right_cancel hv)
  have hpBD : P.pair B = D := by
    rw [← hB,← hD] at hBD
    change enclosePartner P B.castSucc.succ = D.castSucc.succ at hBD
    rw [enclosePartner_inner] at hBD
    have hv := congrArg Fin.val hBD
    exact Fin.ext (Nat.add_right_cancel hv)
  exact hP A B C D (by change a.val-1 < b.val-1; omega)
    (by change b.val-1 < c.val-1; omega) (by change c.val-1 < d.val-1; omega) hpAC hpBD

end WaveTurbulence.Reg.PairPartition
