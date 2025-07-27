import Mathlib.Tactic

/- simple implementation of the natural numbers, withjout using the default implementation -/

/- declaration of the type-/

inductive NAT where
  | zero : NAT
  | succ : NAT → NAT


open NAT

/- definitions -/

def one : NAT := succ zero
def two : NAT := succ (succ zero)

theorem zero_ne_succ (a : NAT) : succ a ≠ zero := by
  simp


/- addition -/

def NAT.add (a : NAT) (b : NAT) : NAT :=
  match b with
  | zero => a
  | succ n => succ (add a n)

theorem NAT.add_zero (a : NAT) : add a zero = a := by
  rfl

theorem NAT.zero_add (a : NAT) : add zero a = a := by
  induction a with
  | zero => rw [add_zero]
  | succ n ih =>
      simp [add]
      exact ih

lemma NAT.add_succ (a b : NAT) : add (succ a) b = add a (succ b) := by
  induction b with
  | zero => rw [add, add, add_zero]
  | succ n ih =>
      simp [add]
      exact ih

theorem NAT.add_assoc (a b c : NAT) : add (add a b) c = add a (add b c) := by
  induction c with
  | zero => rw[add_zero, add_zero]
  | succ n ih =>
        rw [add, add, add, ih]
        

theorem NAT.add_comm (a b : NAT) : add a b = add b a := by
  induction a with
  | zero => rw [add_zero, zero_add]
  | succ n ih =>
      simp [add]
      rw [←  ih]
      apply add_succ

example (a : NAT) : add a two = add two a := by 
    apply NAT.add_comm
