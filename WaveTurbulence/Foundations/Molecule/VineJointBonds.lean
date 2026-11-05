/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineExpansionInvariant
import Mathlib.Tactic

/-! # Joint bonds are unchanged by interior rung insertion (TARGET defvine) -/

public section
namespace WaveTurbulence.Vine

/-- A joint-to-joint edge, in either recorded order. -/
@[expose] def isJointBond (e : ℕ×ℕ) : Bool := decide (e=(0,1) ∨ e=(1,0))

/-- The template's sigma, retaining parallel-edge multiplicity. -/
@[expose] def templateSigma (T : VineTemplate) : ℕ := T.bonds.countP isJointBond

/-- TARGET defvine: only I and V have bonds between the joints. -/
theorem template_sigma (X : VineType) :
    templateSigma X.template = match X with | .I => 2 | .V => 1 | _ => 0 := by
  cases X <;> rfl

private theorem erase_countP {es : List (ℕ×ℕ)} {e : ℕ×ℕ}
    (he : e ∈ es) (hn : isJointBond e = false) :
    (es.erase e).countP isJointBond = es.countP isJointBond := by
  have hp := List.Perm.countP_eq isJointBond (List.perm_cons_erase he)
  simpa only [List.countP_cons,hn,Bool.false_eq_true,ite_false,Nat.add_zero] using hp.symm

private theorem nonjoint_of_fst (e : ℕ×ℕ) (h : 2 ≤ e.1) : isJointBond e = false := by
  simp only [isJointBond,decide_eq_false_iff_not,not_or]
  constructor <;> intro he <;> have hh := congrArg Prod.fst he <;> simp only at hh <;> omega

private theorem rail_nonjoint (a b : ℕ) (ws : List ℕ) (ha : 2 ≤ a)
    (hw : ∀ w ∈ ws, 2 ≤ w) : (railBonds a ws b).countP isJointBond = 0 := by
  apply List.countP_eq_zero.mpr
  intro e he
  have hf := (List.of_mem_zip he).1
  have ha' : e.1 ∈ a::ws := hf
  apply Bool.eq_false_iff.mp (nonjoint_of_fst e ?_)
  rcases List.mem_cons.mp ha' with h | h
  · exact h ▸ ha
  · exact hw _ h

/-- Interior slots cannot create or remove a joint-to-joint bond. -/
theorem insertRungs_sigma (T : VineTemplate) (s : (ℕ×ℕ)×(ℕ×ℕ)) (k : ℕ)
    (hn : 2 ≤ T.n) (h1 : s.1 ∈ T.bonds) (h2 : s.2 ∈ T.bonds.erase s.1)
    (ha : 2 ≤ s.1.1) (hb : 2 ≤ s.2.1) :
    templateSigma (insertRungs T s k) = templateSigma T := by
  by_cases hk : k=0
  · rw [hk,insertRungs_zero]
  · have hu : ∀ w ∈ (List.range k).map (T.n+·), 2 ≤ w := by
      intro w hw
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
      omega
    have hv : ∀ w ∈ (List.range k).map (T.n+k+·), 2 ≤ w := by
      intro w hw
      obtain ⟨i,_hi,rfl⟩ := List.mem_map.mp hw
      omega
    have hrung : ((((List.range k).map (T.n+·)).zip ((List.range k).map (T.n+k+·))).flatMap
        (fun p => [p,p])).countP isJointBond = 0 := by
      apply List.countP_eq_zero.mpr
      intro e he
      obtain ⟨p,hp,he⟩ := List.mem_flatMap.mp he
      have heq : e=p := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using he
      subst e
      exact Bool.eq_false_iff.mp (nonjoint_of_fst p (hu _ (List.of_mem_zip hp).1))
    simp only [templateSigma,insertRungs,hk,ite_false,List.countP_append,
      rail_nonjoint _ _ _ ha hu,rail_nonjoint _ _ _ hb hv,hrung,Nat.add_zero]
    rw [erase_countP h2 (nonjoint_of_fst s.2 hb),erase_countP h1 (nonjoint_of_fst s.1 ha)]

end WaveTurbulence.Vine
