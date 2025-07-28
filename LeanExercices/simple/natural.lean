
/- simple implementation of the natural numbers, without using the default implementation -/

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

theorem NAT.add_succ (a b : NAT) : add (succ a) b = add a (succ b) := by
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


/- multiplication -/

def NAT.mult (a b : NAT) : NAT :=
  match b with
  | zero => zero
  | succ n => add (mult a n) a

theorem NAT.mult_zero (a : NAT) : mult a zero = zero := by
  rfl

theorem NAT.zero_mult (a : NAT) : mult zero a = zero := by
  induction a  with
  | zero => rw[mult]
  | succ n ih =>
     rw[mult, ih, add_zero]

theorem NAT.mult_one (a : NAT) : mult a one = a := by
   rw [one, mult, mult_zero, zero_add]

theorem NAT.one_mult (a : NAT) : mult one a = a := by
   rw [one]
   induction a with
   | zero => rw[mult_zero]
   | succ n ih => rw[mult, ih, add, add_zero]

theorem mult_distrib (a b c : NAT) : mult a (add b c) = add (mult a b) (mult a c) := by
   induction c with
   | zero => rw [add_zero, mult_zero, add_zero]
   | succ n ih => rw [add, mult, mult, ih, add_assoc]

theorem distrib_mult (a b c : NAT) : mult (add a b) c = add (mult a c) (mult b c) := by
   induction c with
   | zero => rw [mult_zero, mult_zero, mult_zero, add_zero]
   | succ n ih =>
      rw [mult, mult, mult, ih]
      conv =>
        rhs
        rw [add_assoc]
        pattern a.add _
        rw (config := { occs := .pos [2]}) [add_comm]
        rw [← add_assoc]
        rw (config := { occs := .pos [1]}) [add_comm]
      rw [add_assoc]

theorem mult_assoc (a b c : NAT) : mult (mult a b) c = mult a (mult b c) := by
  induction c with
  | zero => rw [mult_zero, mult_zero, mult_zero]
  | succ n ih => rw [mult, mult, mult_distrib, ih]

theorem mult_succ (a b : NAT) : mult (succ a) b = add (mult a b) b := by
  induction b with
  | zero => rw [mult_zero, mult_zero, add_zero]
  | succ n ih =>
      rw [mult, ih, mult, add_assoc, add_assoc, add]
      rw (config := { occs := .pos [2]}) [add]
      rw (config := { occs := .pos [2]}) [add_comm]

theorem mult_comm (a b : NAT) : mult a b = mult b a := by
  induction b with
  | zero => rw [mult_zero, zero_mult]
  | succ n ih => rw [mult, ih, mult_succ]
