import Smt

inductive Color where
  | red
  | green
  | blue

example : Color.red ≠ Color.blue := by
  intro hrb
  nomatch hrb

set_option trace.smt true in
example : Color.red ≠ Color.blue := by
  smt +trust +showQuery
  grind


inductive mynat where
 | zero
 | succ (n : mynat)

set_option trace.smt true in
example : .zero ≠ mynat.succ .zero := by
  smt +trust +showQuery
  grind
inductive mynat' where
 | zero
 | succ :  mynat' → mynat' → mynat'

set_option trace.smt true in
example : .zero ≠ mynat'.succ .zero .zero := by
  smt +trust +showQuery
  grind

set_option trace.smt true in
example : ([mynat'.zero, mynat'.zero] : List mynat') ≠ [mynat'.succ mynat'.zero mynat'.zero] := by
  smt +trust +showQuery
  grind

example {p q r : U → Prop} : (∀ x, p x ∧ q x ∧ r x) = ((∀ x, p x) ∧ (∀ x, q x) ∧ (∀ x, r x)) := by
  smt
