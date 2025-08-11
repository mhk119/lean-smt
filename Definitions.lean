prelude
import Init.Classical
import Init.Core
import Init.Data.AC
import Init.Data.Int
import Init.Data.List.Basic
import Init.Data.List.Notation

inductive XOr (p q : Prop) : Prop where
  | inl : p → ¬q → XOr p q
  | inr : ¬p → q → XOr p q

theorem XOr.elim {p q r : Prop} (h : XOr p q) (h₁ : p → ¬q → r) (h₂ : ¬p → q → r) : r := match h with
  | inl hp hnq => h₁ hp hnq
  | inr hnp hq => h₂ hnp hq

theorem XOr.symm (h : XOr p q) : XOr q p := h.elim (flip inr) (flip inl)

namespace XOr

@[macro_inline] instance [dp : Decidable p] [dq : Decidable q] : Decidable (XOr p q) :=
  match dp with
  | isTrue   hp =>
    match dq with
    | isTrue   hq => isFalse (·.elim (fun _ hnq => hnq hq) (fun hnp _ => hnp hp))
    | isFalse hnq => isTrue (.inl hp hnq)
  | isFalse hnp =>
    match dq with
    | isTrue   hq => isTrue (.inr hnp hq)
    | isFalse hnq => isFalse (·.elim (fun hp _ => hnp hp) (fun _ hq => hnq hq))

end XOr

def andN : List Prop → Prop
  | []      => True
  | p :: [] => p
  | p :: ps => p ∧ andN ps

@[simp] theorem andN_append : andN (ps ++ qs) = (andN ps ∧ andN qs) := by
  match ps, qs with
  | [], _
  | [p], []
  | [p], q :: qs       => simp [andN]
  | p₁ :: p₂ :: ps, qs =>
    rw [List.cons_append, andN, andN, andN_append, and_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem andN_cons_append : andN (p :: ps) = (p ∧ andN ps) := by
  cases ps <;> simp only [andN, and_true]

def orN : List Prop → Prop
  | []      => False
  | p :: [] => p
  | p :: qs => p ∨ orN qs

@[simp] theorem orN_append : orN (ps ++ qs) = (orN ps ∨ orN qs) := by
  match ps, qs with
  | [], _
  | [p], []
  | [p], q :: qs       => simp [orN]
  | p₁ :: p₂ :: ps, qs =>
    rw [List.cons_append, orN, orN, orN_append, or_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem orN_cons_append : orN (p :: ps) = (p ∨ orN ps) := by
  cases ps <;> simp only [orN, or_false]

def impliesN (ps : List Prop) (q : Prop) : Prop := match ps with
  | [] => q
  | p :: ps => p → impliesN ps q

def notN : List Prop → List Prop := List.map Not

namespace Smt.Reconstruct.Prop

theorem and_assoc_eq : ((p ∧ q) ∧ r) = (p ∧ (q ∧ r)) := by
  simp [and_assoc]

theorem and_comm_eq : (p ∧ q) = (q ∧ p) := by
  simp [and_comm]

theorem or_assoc_eq : ((a ∨ b) ∨ c) = (a ∨ (b ∨ c)) := by
  simp [or_assoc]

theorem or_comm_eq : (p ∨ q) = (q ∨ p) := by
  simp [or_comm]

instance : Std.Associative And := ⟨@and_assoc_eq⟩

instance : Std.Commutative And := ⟨@and_comm_eq⟩

instance : Std.IdempotentOp And := ⟨and_self⟩

instance : Std.LawfulIdentity And True where
  left_id := true_and
  right_id := and_true

instance : Std.Associative Or := ⟨@or_assoc_eq⟩

instance : Std.Commutative Or := ⟨@or_comm_eq⟩

instance : Std.IdempotentOp Or := ⟨or_self⟩

instance : Std.LawfulIdentity Or False where
  left_id := false_or
  right_id := or_false

end Smt.Reconstruct.Prop

namespace Smt.Reconstruct.Builtin

class Absorb (mul : α → α → α) where
  zero : α
  /-- Zero is a left absorbing element for multiplication -/
  zero_mul : ∀ (a : α), mul zero a = zero
  /-- Zero is a right absorbing element for multiplication -/
  mul_zero : ∀ (a : α), mul a zero = zero

instance : Absorb And where
  zero := False
  zero_mul := false_and
  mul_zero := and_false

instance : Absorb Or where
  zero := True
  zero_mul := true_or
  mul_zero := or_true

instance : @Absorb Int (· * ·) where
  zero := 0
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero

instance : @Absorb (BitVec w) (· &&& ·) where
  zero := 0#w
  zero_mul := @BitVec.zero_and w
  mul_zero := @BitVec.and_zero w

instance : @Absorb (BitVec w) (· ||| ·) where
  zero := BitVec.allOnes w
  zero_mul := @BitVec.allOnes_or w
  mul_zero := @BitVec.or_allOnes w

instance : @Absorb (BitVec w) (· * ·) where
  zero := 0#w
  zero_mul := @BitVec.zero_mul w
  mul_zero := @BitVec.mul_zero w

namespace Absorb

def Context α := Nat → α

inductive Expr where
  | zero
  | atom (v : Nat)
  | op (l r : Expr)
deriving Inhabited, Repr

namespace Expr

def containsZero : Expr → Bool
  | Expr.zero   => true
  | Expr.atom _ => false
  | Expr.op l r => containsZero l || containsZero r

def eval [hα : @Absorb α mul] (ctx : Context α) : Expr → α
  | Expr.zero   => hα.zero
  | Expr.atom v => ctx v
  | Expr.op l r => mul (eval (hα := hα) ctx l) (eval (hα := hα) ctx r)

theorem eval_eq_zero_from_containsZero [hα : @Absorb α mul] (ctx : Context α) (h : containsZero e) :
  eval (hα := hα) ctx e = hα.zero := by
  induction e with
  | zero   => rfl
  | atom v => contradiction
  | op l r ih₁ ih₂ =>
    unfold eval
    simp only [containsZero, Bool.or_eq_true] at h
    cases h <;> rename_i h
    · rw [ih₁ h, hα.zero_mul]
    · rw [ih₂ h, hα.mul_zero]

end Expr

end Smt.Reconstruct.Builtin.Absorb

theorem Eq.same_root (hac : a = c) (hbc : b = c) : a = b := hac ▸ hbc ▸ rfl

theorem Eq.trans₂ {a b c d : α} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) : a = d :=
  h₁ ▸ h₂ ▸ h₃

theorem ite_congr' {α} [Decidable c₁] [Decidable c₂] {x₁ x₂ y₁ y₂ : α} (h₁ : c₁ = c₂) (h₂ : x₁ = x₂) (h₃ : y₁ = y₂) : ite c₁ x₁ y₁ = ite c₂ x₂ y₂ := by
  congr

namespace Smt.Reconstruct.Builtin

theorem iteElim1 [hc : Decidable c] : ite c a b → ¬ c ∨ a := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inr h
  | isFalse hnc => exact Or.inl hnc

theorem iteElim2 [hc : Decidable c] : ite c a b → c ∨ b := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inl hc
  | isFalse hnc => exact Or.inr h

theorem notIteElim1 [hc : Decidable c] : ¬ ite c a b → ¬ c ∨ ¬ a := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inr h
  | isFalse hnc => exact Or.inl hnc

theorem notIteElim2 [hc : Decidable c] : ¬ ite c a b → c ∨ ¬ b := by
  intros h
  cases hc with
  | isTrue hc   => exact Or.inl hc
  | isFalse hnc => exact Or.inr h

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match Classical.em q with
                     | Or.inl pq => Or.inr pq
                     | Or.inr npq => False.elim (npq (h npp))

theorem notNotElim : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match Classical.em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem cnfItePos1 [h : Decidable c] : ¬ (ite c a b) ∨ ¬ c ∨ a := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isTrue _    => exact Or.inr hite'
  | isFalse hnc => exact Or.inl hnc

theorem cnfItePos2 [h : Decidable c] : ¬ (ite c a b) ∨ c ∨ b := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isFalse _ => exact Or.inr hite'
  | isTrue hc => exact Or.inl hc

theorem cnfItePos3 [h : Decidable c] : ¬ (ite c a b) ∨ a ∨ b := by
  apply orImplies
  intro hite
  have hite' := notNotElim hite
  match h with
  | isFalse _ => exact Or.inr hite'
  | isTrue _  => exact Or.inl hite'

theorem cnfIteNeg1 [h : Decidable c] : (ite c a b) ∨ ¬ c ∨ ¬ a := by
  apply orImplies
  intro hnite
  match h with
  | isTrue _    => exact Or.inr hnite
  | isFalse hnc => exact Or.inl hnc

theorem cnfIteNeg2 [h : Decidable c] : (ite c a b) ∨ c ∨ ¬ b   := by
  apply orImplies
  intro hnite
  match h with
  | isFalse _ => exact Or.inr hnite
  | isTrue hc => exact Or.inl hc

theorem cnfIteNeg3 [h : Decidable c] : (ite c a b) ∨ ¬ a ∨ ¬ b := by
  apply orImplies
  intro hnite
  match h with
  | isFalse _ => exact Or.inr hnite
  | isTrue _  => exact Or.inl hnite

theorem scopes : ∀ {ps : List Prop} {q : Prop}, impliesN ps q → andN ps → q :=
  by intros ps q h
     match ps with
     | []   => intro; exact h
     | [p]  => unfold andN
               unfold impliesN at h
               exact h
     | p₁::p₂::ps => unfold andN
                     unfold impliesN at h
                     intro ⟨hp₁, hps⟩
                     revert hps
                     exact scopes (h hp₁)

end Smt.Reconstruct.Builtin

namespace Smt.Reconstruct.Builtin

-- https://github.com/cvc5/cvc5/blob/main/src/theory/builtin/rewrites

-- ITE

theorem ite_true_cond : ite True x y = x := rfl
theorem ite_false_cond : ite False x y = y := rfl
theorem ite_not_cond [h : Decidable c] : ite (¬c) x y = ite c y x :=
  h.byCases (fun hc => if_pos hc ▸ if_neg (not_not_intro hc) ▸ rfl)
            (fun hnc => if_pos hnc ▸ if_neg hnc ▸ rfl)
theorem ite_eq_branch [h : Decidable c] : ite c x x = x :=
  h.byCases (if_pos · ▸ rfl) (if_neg · ▸ rfl)

theorem ite_then_lookahead [h : Decidable c] : ite c (ite c x y) z = ite c x z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_else_lookahead [h : Decidable c] : ite c x (ite c y z) = ite c x z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_then_neg_lookahead [h : Decidable c] : ite c (ite (¬c) x y) z = ite c y z :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ ite_not_cond (c := c) ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ rfl)
theorem ite_else_neg_lookahead [h : Decidable c] : ite c x (ite (¬c) y z) = ite c x y :=
  h.byCases (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
            (fun hc => if_neg hc ▸ if_neg hc ▸ ite_not_cond (c := c) ▸ if_neg hc ▸ rfl)

end Smt.Reconstruct.Builtin

namespace Int

protected def abs (x : Int) : Int :=
  if x < 0 then -x else x

theorem abs_eq (hb : 0 ≤ b) : a.abs = b ↔ a = b ∨ a = -b := by
  unfold Int.abs
  omega

theorem abs_nonneg (x : Int) : 0 ≤ x.abs := by
  unfold Int.abs
  omega

theorem abs_of_nonpos (h : a ≤ 0) : a.abs = -a := by
  unfold Int.abs
  omega

theorem abs_of_nonneg {a : Int} (h : 0 ≤ a) : a.abs = a := by
  unfold Int.abs
  omega

theorem abs_mul (a b : Int) : (a * b).abs = a.abs * b.abs := by
  rw [Int.abs_eq (Int.mul_nonneg (Int.abs_nonneg a) (Int.abs_nonneg b))]
  rcases Int.le_total a 0 with ha | ha <;> rcases Int.le_total b 0 with hb | hb <;>
    simp only [Int.abs_of_nonpos, Int.abs_of_nonneg, true_or, or_true, eq_self_iff_true, Int.neg_mul,
      Int.mul_neg, Int.neg_neg, *]

def addN : List Int → Int
  | []      => 0
  | [x]     => x
  | x :: xs => x + addN xs

@[simp] theorem addN_append : addN (xs ++ ys) = addN xs + addN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [addN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, addN, addN, addN_append, Int.add_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem addN_cons_append : addN (x :: xs) = x + addN xs := by
  cases xs <;> simp only [addN, Int.add_zero]

def mulN : List Int → Int
  | []      => 1
  | [x]     => x
  | x :: xs => x * mulN xs

@[simp] theorem mulN_append : mulN (xs ++ ys) = mulN xs * mulN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [mulN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, mulN, mulN, mulN_append, Int.mul_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem mulN_cons_append : mulN (x :: xs) = x * mulN xs := by
  cases xs <;> simp only [mulN, Int.mul_one]

protected theorem cast_pos' {x : Nat} : x ≠ 0 → (0 : Int) < x := by
  intro h
  have h' := Nat.zero_lt_of_ne_zero h
  exact Int.ofNat_pos.mpr h'

protected theorem gcd_def (i j : Int) : i.gcd j = i.natAbs.gcd j.natAbs :=
  rfl

protected theorem gcd_def' (i : Int) (j : Nat) : i.gcd (ofNat j) = i.natAbs.gcd j :=
  Int.gcd_def _ _

theorem gcd_ne_zero_iff {i j : Int} : gcd i j ≠ 0 ↔ i ≠ 0 ∨ j ≠ 0 := by
  constructor
  · intro h
    let tmp := not_congr gcd_eq_zero_iff |>.mp h
    if h_i : i = 0 then
      simp [h_i] at tmp
      exact Or.inr tmp
    else
      exact Or.inl h_i
  · intro h gcd_zero
    rw [gcd_eq_zero_iff] at gcd_zero
    simp [gcd_zero.1, gcd_zero.2] at h

protected theorem dvd_mul_left_of_dvd {i j : Int} (k : Int) : i ∣ j → i ∣ k * j
| ⟨n, h⟩ => by
  rw [h]
  exists k * n
  rw [
    ← Int.mul_assoc k i n,
    Int.mul_comm k i,
    Int.mul_assoc i k n,
  ]

protected theorem natAbs_gcd_dvd {i : Int} {n : Nat} : ↑(i.natAbs.gcd n) ∣ i := by
  refine ofNat_dvd_left.mpr ?_
  exact Nat.gcd_dvd_left _ _

protected theorem natAbs_gcd_dvd' (i : Int) (n : Nat) : ↑(i.natAbs.gcd n) ∣ i :=
  Int.natAbs_gcd_dvd

protected theorem dvd_mul_right_of_dvd {i j : Int} (k : Int) : i ∣ j → i ∣ j * k :=
  Int.mul_comm j k ▸ Int.dvd_mul_left_of_dvd k

theorem flatten_div_mul_eq_mul_div
  {i1 i2 i3 i4 j : Int}
  (j_pos : j ≠ 0)
  (j_dvd_i1 : j ∣ i1)
  (j_dvd_i4 : j ∣ i4)
: i1 / j * i2 = i3 * (i4 / j) → i1 * i2 = i3 * i4 := by
  intro h
  rw [← Int.mul_eq_mul_left_iff j_pos] at h
  conv at h =>
    lhs
    rw [← Int.mul_assoc]
    rw [← Int.mul_ediv_assoc _ j_dvd_i1]
    rw [Int.mul_ediv_cancel_left _ j_pos]
  conv at h =>
    rhs
    rw [← Int.mul_assoc]
    conv => lhs ; rw [Int.mul_comm]
    rw [Int.mul_assoc]
    rw [← Int.mul_ediv_assoc _ j_dvd_i4]
    rw [Int.mul_ediv_cancel_left _ j_pos]
  assumption

theorem not_lt_of_lt_rev {i j : Int} : i < j → ¬ j < i := by
  omega

theorem lt_of_le_of_ne {i j : Int} : i ≤ j → i ≠ j → i < j := by
  omega

@[simp]
theorem zero_le_natCast {n : Nat} : (0 : Int) ≤ n := by omega

theorem div_nonneg_iff_of_pos' {a b : Int} (h : 0 < b) : 0 ≤ a / b ↔ 0 ≤ a := by
  let tmp := @Int.ediv_nonneg_iff_of_pos a b h
  simp [GE.ge] at tmp
  exact tmp

variable {a b c : Int}

protected theorem le_or_lt (a b : Int) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem div_gcd_nonneg_iff_of_pos
  {b : Nat} (b_pos : 0 < b)
: 0 ≤ a / (a.gcd b) ↔ 0 ≤ a := by
  let nz_den : (0 : Int) < a.gcd b := by
    apply Int.natCast_pos.mpr
    simp [gcd, natAbs_natCast, Nat.gcd_pos_iff, natAbs_pos, ne_eq, b_pos]
  exact Int.ediv_nonneg_iff_of_pos nz_den

protected theorem div_gcd_nonneg_iff_of_nz {b : Nat} (nz_b : b ≠ 0) : 0 ≤ a / (a.gcd b) ↔ 0 ≤ a :=
  Nat.pos_of_ne_zero nz_b |> Int.div_gcd_nonneg_iff_of_pos

example (a b : Int) : ¬ a ≤ b → b < a := by exact fun a_1 => Int.lt_of_not_ge a_1

theorem mul_pos_iff_of_pos_right (c_pos : 0 < c) : 0 < b * c ↔ 0 < b := ⟨
  by
    intro bc_nonneg
    apply Decidable.byContradiction
    intro h_b'
    have h_b := Int.not_le.mp h_b'
    have := Int.not_lt.mp h_b'
    cases Int.le_iff_lt_or_eq.mp this with
    | inl n =>
        have := Int.not_le.mpr (Int.mul_neg_of_neg_of_pos n c_pos)
        have := Int.lt_of_not_ge this
        have := Int.lt_trans bc_nonneg this
        simp at this
    | inr n => rw [n] at bc_nonneg; simp at bc_nonneg
  ,
  by
    intro b_pos
    apply Int.mul_pos b_pos c_pos
⟩

end Int

private theorem Int.mul_eq_zero_left {x y : Int} (hx : x ≠ 0) (hxy : x * y = 0) : y = 0 := by
  rewrite [Int.mul_eq_zero] at hxy
  exact hxy.resolve_left hx

private def uncurry {p₁ p₂ p₃ : Prop} : (p₁ → p₂ → p₃) → (p₁ ∧ p₂) → p₃ := by
  intros h₁ h₂
  have ⟨ht₁, ht₂⟩ := h₂
  exact h₁ ht₁ ht₂

namespace Smt.Reconstruct.Int

variable {a b c d x₁ x₂ y₁ y₂ : Int}

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  have r₁ : a + c < a + d := Int.add_lt_add_left h₂ a
  have r₂ : a + d < b + d := Int.add_lt_add_right h₁ d
  exact Int.lt_trans r₁ r₂

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  have r₁ : a + c ≤ a + d := Int.add_le_add_left h₂ a
  have r₂ : a + d < b + d := Int.add_lt_add_right h₁ d
  exact Int.lt_of_le_of_lt r₁ r₂

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  rewrite [h₂]
  exact Int.add_lt_add_right h₁ d

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  have r₁ : a + c < a + d := Int.add_lt_add_left h₂ a
  have r₂ : a + d ≤ b + d := Int.add_le_add_right h₁ d
  exact Int.lt_of_lt_of_le r₁ r₂

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  have r₁ : a + c ≤ a + d := Int.add_le_add_left h₂ a
  have r₂ : a + d ≤ b + d := Int.add_le_add_right h₁ d
  exact Int.le_trans r₁ r₂

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₂]
  exact Int.add_le_add_right h₁ d

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  rewrite [h₁]
  exact Int.add_lt_add_left h₂ b

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rewrite [h₁]
  exact Int.add_le_add_left h₂ b

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  rw [h₁, h₂]

theorem mul_abs₁ (h₁ : x₁.abs = y₁.abs) (h₂ : x₂.abs = y₂.abs) : (x₁ * x₂).abs = (y₁ * y₂).abs := by
  rw [Int.abs_mul x₁ x₂, Int.abs_mul y₁ y₂, h₁, h₂]

theorem mul_abs₂ (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs = y₂.abs ∧ x₂.abs ≠ 0) : (x₁ * x₂).abs > (y₁ * y₂).abs := by
  rewrite [Int.abs_mul, Int.abs_mul]
  apply Int.mul_lt_mul h₁ (Int.le_of_eq h₂.left.symm) _ (Int.abs_nonneg x₁)
  rewrite [← h₂.left]
  exact Int.lt_of_le_of_ne (Int.abs_nonneg x₂) h₂.right.symm

theorem mul_abs₃ (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs > y₂.abs) : (x₁ * x₂).abs > (y₁ * y₂).abs := by
  rw [Int.abs_mul, Int.abs_mul]
  apply Int.mul_lt_mul' (Int.le_of_lt h₁) h₂ (Int.abs_nonneg y₂)
  cases Int.le_iff_eq_or_lt.mp (Int.abs_nonneg y₁) <;> rename_i h
  · rewrite [h]; exact h₁
  · exact Int.lt_trans h h₁

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c - 1 :=
  Int.le_sub_one_of_lt h

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c + 1 :=
  h

theorem trichotomy₁ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_right (or_assoc.mpr tr) (Int.not_lt.mpr h₁)) h₂

theorem trichotomy₂ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_left tr (Int.not_lt.mpr h₂)) (Int.not_lt.mpr h₁)

theorem trichotomy₃ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_right (or_assoc.mpr tr) (Int.not_lt.mpr h₂)) h₁

theorem trichotomy₄ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_left (Or.resolve_left tr (Int.not_lt.mpr h₂)) h₁

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_right (Or.resolve_left tr (Int.not_lt.mpr h₁)) (Int.not_lt.mpr h₂)

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  have tr := Int.lt_trichotomy a b
  exact Or.resolve_left (Or.resolve_left tr (Int.not_lt.mpr h₁)) h₂

theorem abs_elim : x.abs = if x < 0 then -x else x :=
  rfl

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  constructor
  · apply Int.sub_neg_of_lt
  · apply Int.lt_of_sub_neg

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  apply propext
  constructor
  · exact Int.sub_nonpos_of_le
  · exact Int.le_of_sub_nonpos

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  simp only [Int.sub_eq_zero]

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  simp only [ge_iff_le, eq_iff_iff]
  constructor
  · exact Int.sub_nonneg_of_le
  · exact Int.le_of_sub_nonneg

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  simp only [gt_iff_lt, eq_iff_iff]
  constructor
  · exact Int.sub_pos_of_lt
  · exact Int.lt_of_sub_pos

theorem lt_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, Int.mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem lt_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply lt_of_sub_eq_pos (by omega) (by omega) h

theorem le_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, Int.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply le_of_sub_eq_pos (by omega) (by omega) h

theorem eq_of_sub_eq {c₁ c₂ : Int} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  apply propext
  apply Iff.intro
  · intro ha
    rewrite [ha, Int.sub_self, Int.mul_zero, eq_comm, Int.mul_eq_zero] at h
    omega
  · intro hb
    rewrite [hb, Int.sub_self, Int.mul_zero, Int.mul_eq_zero] at h
    omega

theorem ge_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, ge_iff_le, Int.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem ge_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply ge_of_sub_eq_pos (by omega) (by omega) h

theorem gt_of_sub_eq_pos {c₁ c₂ : Int} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Int} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Int.mul_zero c, gt_iff_lt, Int.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Int} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rewrite [← Int.mul_eq_mul_left_iff (by decide : -1 ≠ 0), ← Int.mul_assoc (-1), ← Int.mul_assoc (-1)] at h
  apply gt_of_sub_eq_pos (by omega) (by omega) h

theorem mul_sign₁ (ha : a < 0) (hb : b < 0) : a * b > 0 := by
  have h := Int.mul_lt_mul_of_neg_right ha hb
  simp at h
  exact h

theorem mul_sign₃ (ha : a < 0) (hb : b > 0) : a * b < 0 := by
  have h := Int.mul_lt_mul_of_pos_right ha hb
  simp at h
  exact h

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  have h := Int.mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₆ (ha : a > 0) (hb : b > 0) : a * b > 0 := by
  have h := Int.mul_lt_mul_of_pos_left hb ha
  simp at h
  exact h

theorem mul_sign₀ (ha : a ≠ 0) : a * a > 0 :=
  match Int.lt_trichotomy a 0 with
  | .inl hn         => mul_sign₁ hn hn
  | .inr (.inl hz)  => absurd hz ha
  | .inr (.inr hp)  => mul_sign₆ hp hp

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 :=
  match Int.lt_trichotomy b 0 with
  | .inl hn         => mul_sign₄ (mul_sign₁ ha hn) hn
  | .inr (.inl hz)  => absurd hz hb
  | .inr (.inr hp)  => mul_sign₃ (mul_sign₃ ha hp) hp

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 :=
  match Int.lt_trichotomy b 0 with
  | .inl hn         => mul_sign₁ (mul_sign₄ ha hn) hn
  | .inr (.inl hz)  => absurd hz hb
  | .inr (.inr hp)  => mul_sign₆ (mul_sign₆ ha hp) hp

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b :=
  Int.mul_lt_mul_of_pos_left h.2 h.1

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b :=
  Int.mul_le_mul_of_nonneg_left h.2 (Int.le_of_lt h.1)

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b :=
  mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b :=
  mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

theorem mul_neg_lt (h : c < 0 ∧ a < b) : c * a > c * b :=
  Int.mul_lt_mul_of_neg_left h.2 h.1

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b :=
  Int.mul_le_mul_of_nonpos_left (Int.le_of_lt h.1) h.2

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b :=
  mul_neg_lt h

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by
  rw [h.2]

end Smt.Reconstruct.Int

namespace Smt.Reconstruct.Int.PolyNorm

abbrev Var := Nat

def Context := Var → Int

structure Monomial where
  coeff : Int
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

def neg (m : Monomial) : Monomial :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial) (_ : m₁.vars = m₂.vars) : Monomial :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial) : Monomial :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert (x : Var) : List Var → List Var
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def eval (ctx : Context) (m : Monomial) : Int :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem eval_neg {m : Monomial} : m.neg.eval ctx = -m.eval ctx := by
  simp only [neg, eval, Int.neg_mul_eq_neg_mul]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons, ih, assoc]

end

-- Can be generalized.
theorem foldl_mul_insert {ctx : Context} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [mul.insert]
  | cons x ys ih =>
    by_cases h : y ≤ x
    · simp [mul.insert, h, foldl_assoc Int.mul_assoc (ctx y) (ctx x), Int.mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, Int.mul_comm,
                 foldl_assoc Int.mul_assoc, ih]
      rw [←Int.mul_assoc, Int.mul_comm (ctx x) (ctx y), Int.mul_assoc]

theorem eval_add {m n : Monomial} (h : m.vars = n.vars) :
  (m.add n h).eval ctx = m.eval ctx + n.eval ctx := by
  simp only [add, eval, Int.add_mul, h]

theorem eval_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).eval ctx = m₁.eval ctx * m₂.eval ctx := by
  simp only [eval, mul, Int.mul_assoc]; congr 1
  rw [← Int.mul_assoc, Int.mul_comm _ m₂.coeff, Int.mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp [Int.mul_assoc]
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc Int.mul_assoc, ih]

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

def neg (p : Polynomial) : Polynomial :=
  p.map Monomial.neg

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial) : Polynomial :=
  p.foldr insert q
where
  insert (m : Monomial) : Polynomial → Polynomial
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial) : Polynomial :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial) (p : Polynomial) : Polynomial :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial) : Polynomial :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def eval (ctx : Context) (p : Polynomial) : Int :=
  p.foldl (fun acc m => acc + m.eval ctx) 0

theorem foldl_add_insert (ctx : Context) :
  List.foldl (fun z a => z + (Monomial.eval ctx a)) 0 (add.insert m p) =
  (Monomial.eval ctx m) + List.foldl (fun z a => z + (Monomial.eval ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←Int.add_assoc, Int.add_comm, ←Monomial.eval_add heq]
          simp [Monomial.eval, hneq]
        · simp [-Int.add_zero, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Monomial.eval_add, heq, Int.add_assoc]
      · simp only [List.foldl_cons, Int.add_comm 0, ih, Monomial.foldl_assoc Int.add_assoc]
        rw [←Int.add_assoc, Int.add_comm (Monomial.eval ctx n), Int.add_assoc]

theorem eval_neg {p : Polynomial} : p.neg.eval ctx = -p.eval ctx := by
  simp only [eval, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc,Int.neg_add, ←ih, List.map, Monomial.eval_neg]

theorem eval_add {p q : Polynomial} : (p.add q).eval ctx = p.eval ctx + q.eval ctx := by
  simp only [eval, add]
  induction p with
  | nil => simp [add.insert]
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Int.add_assoc]
    rw [← ih, foldl_add_insert]

theorem eval_sub {p q : Polynomial} : (p.sub q).eval ctx = p.eval ctx - q.eval ctx := by
  simp only [sub, eval_neg, eval_add, Int.sub_eq_add_neg]

theorem eval_mulMonomial {p : Polynomial} : (p.mulMonomial m).eval ctx = m.eval ctx * p.eval ctx := by
  simp only [eval, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Int.mul_add, ←ih]
    simp [foldl_add_insert, Monomial.eval_mul]

theorem eval_cons {p : List Monomial} {ctx : Context} : eval ctx (m :: p) = m.eval ctx + eval ctx p := by
  simp only [eval, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]

theorem eval_nil_add : eval ctx (p.add []) = eval ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [eval_add, List.foldr_cons, eval_cons, ih, show eval ctx [] = 0 by rfl]

theorem eval_add_insert {g : Monomial → Polynomial} :
  eval ctx (List.foldl (fun acc m => (g m).add acc) n p) = eval ctx n + eval ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [eval]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons, List.foldr, @ih n]
    rw [ih, @ih ((g k).add []), ← Int.add_assoc, eval_nil_add, eval_add, Int.add_comm _ (eval ctx n)]

theorem eval_foldl {g : Monomial → Polynomial} :
  eval ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).eval ctx + acc) 0 p := by
  induction p with
  | nil => simp [eval]
  | cons n p ih =>
    simp only [List.foldl_cons, Int.add_comm, List.foldr] at *
    rw [Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, ←ih, eval_add_insert, eval_nil_add]

theorem eval_mul {p q : Polynomial} : (p.mul q).eval ctx = p.eval ctx * q.eval ctx := by
  simp only [mul]
  induction p with
  | nil => simp [eval]
  | cons n p ih =>
    simp only [List.foldl_cons, eval_cons, Int.add_mul, ← ih]
    rw [eval_foldl, eval_add_insert, ←eval_mulMonomial, eval_nil_add, eval_foldl]

end Polynomial

inductive Expr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
deriving Inhabited, Repr

namespace Expr

def toPoly : Expr → Polynomial
  | val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | var v => [{ coeff := 1, vars := [v] }]
  | neg a => a.toPoly.neg
  | add a b => Polynomial.add a.toPoly b.toPoly
  | sub a b => Polynomial.sub a.toPoly b.toPoly
  | mul a b => Polynomial.mul a.toPoly b.toPoly

def eval (ctx : Context) : Expr → Int
  | val v => v
  | var v => ctx v
  | neg a => -a.eval ctx
  | add a b => a.eval ctx + b.eval ctx
  | sub a b => a.eval ctx - b.eval ctx
  | mul a b => a.eval ctx * b.eval ctx

theorem eval_toPoly {e : Expr} : e.eval ctx = e.toPoly.eval ctx := by
  induction e with
  | val v =>
    simp only [eval, toPoly]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · simp [Polynomial.eval, Monomial.eval]
  | var v =>
    simp [eval, toPoly, Polynomial.eval, Monomial.eval]
  | neg a ih =>
    simp only [eval, toPoly, Polynomial.eval_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_mul, ih₁, ih₂]

theorem eval_eq_from_toPoly_eq {e₁ e₂ : Expr} (h : e₁.toPoly = e₂.toPoly) : e₁.eval ctx = e₂.eval ctx := by
  rw [eval_toPoly, eval_toPoly, h]

end Smt.Reconstruct.Int.PolyNorm.Expr

namespace Smt.Reconstruct.Int.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t s x : Int}

theorem div_total : (s = 0) = False → t / s = t / s :=
  const _ rfl
theorem div_total_one : t / 1 = t :=
  Int.ediv_one t
theorem div_total_zero : t / 0 = 0 :=
  Int.ediv_zero t

theorem div_total_neg : (s < 0) = True → t / s = -(t / -s) :=
  const _ (Int.ediv_neg t s ▸ Int.neg_neg _ ▸ rfl)

theorem mod_total : (s = 0) = False → t % s = t % s :=
  const _ rfl
theorem mod_total_one : t % 1 = 0 :=
  Int.emod_one t
theorem mod_total_zero : t % 0 = t :=
  Int.emod_zero t

theorem mod_total_neg : (s < 0) = True → t % s = t % -s :=
  const _ (Int.emod_neg t s ▸ rfl)

-- Eliminations

theorem elim_gt : (t > s) = ¬(s ≥ t) :=
  propext Int.not_le.symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext Int.not_le.symm
theorem elim_gt_add_one : (t > s) = (t ≥ Int.addN [s, 1]) :=
  propext Int.lt_iff_add_one_le
theorem elim_lt_add_one : (t < s) = (s ≥ Int.addN [t, 1]) :=
  propext Int.lt_iff_add_one_le
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem leq_norm : (t ≤ s) = ¬(t ≥ Int.addN [s, 1]) :=
  propext ⟨fun hts => Int.not_le.mpr (Int.add_le_add_right hts _),
           Int.not_lt.mp⟩

theorem geq_tighten : (¬(t ≥ s)) = (s ≥ Int.addN [t, 1]) :=
  propext Int.not_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) :=
  propext ⟨Int.sub_nonneg_of_le, Int.le_of_sub_nonneg⟩

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) :=
  propext ⟨(· ▸ And.intro (Int.le_refl t) (Int.le_refl t)), fun ⟨hst, hts⟩ => Int.le_antisymm hts hst⟩

theorem mod_over_mod : (c = 0) = False → Int.addN (ts ++ r % c :: ss) % c = Int.addN (ts ++ r :: ss) % c := by
  simp only [Int.addN_append, Int.addN_cons_append, Int.emod_add_cancel_left, Int.emod_add_cancel_right, Int.emod_emod, implies_true]

theorem divisible_elim {n t : Int} (_ : (n = 0) = False) : (n ∣ t) = (t % n = 0) :=
  propext Int.dvd_iff_emod_eq_zero

-- Absolute value comparisons

theorem abs_eq : (x.abs = y.abs) = (x = y ∨ x = -y) := by
  cases hx : decide (x < 0) <;> cases hy : decide (y < 0) <;> simp_all [Int.abs] <;> omega

theorem abs_gt : (x.abs > y.abs) = ite (x ≥ 0) (ite (y ≥ 0) (x > y) (x > -y)) (ite (y ≥ 0) (-x > y) (-x > -y)) := by
  simp only [Int.abs, gt_iff_lt, ge_iff_le, eq_iff_iff] <;> split <;> split <;> split <;> split <;> omega

-- ITE lifting

theorem geq_ite_lift [h : Decidable c] {t s r : Int} : (ite c t s ≥ r) = ite c (t ≥ r) (s ≥ r) := by
  cases h <;> simp_all

theorem leq_ite_lift [h : Decidable c] {t s r : Int} : (ite c t s ≤ r) = ite c (t ≤ r) (s ≤ r) := by
  cases h <;> simp_all

-- min/max rules

theorem min_lt1 : (ite (t < s) t s ≤ t) = True := by
  cases h : decide (t < s) <;> simp_all [Int.not_lt.mpr]

theorem min_lt2 : (ite (t < s) t s ≤ s) = True := by
  cases h : decide (t < s) <;> simp_all [Int.not_lt.mpr, Int.le_of_lt]

theorem max_geq1 : (ite (t ≥ s) t s ≥ t) = True := by
  cases h : decide (t ≥ s) <;> simp_all [Int.not_le_of_gt, Int.le_of_lt]

theorem max_geq2 : (ite (t ≥ s) t s ≥ s) = True := by
  cases h : decide (t ≥ s) <;> simp_all [Int.not_le_of_gt]

end Smt.Reconstruct.Int.Rewrite

namespace Smt.Reconstruct.Prop

open Nat List Classical

theorem ite_eq (c : Prop) [h : Decidable c] (x y : α) : ite c ((ite c x y) = x) ((ite c x y) = y) := by
  cases h
  all_goals simp_all

theorem notImplies1 : ∀ {P Q : Prop}, ¬ (P → Q) → P := by
  intros P Q h
  cases Classical.em P with
  | inl p  => exact p
  | inr np => apply False.elim
              apply h
              intro p
              exact False.elim (np p)

theorem notImplies2 : ∀ {P Q : Prop}, ¬ (P → Q) → ¬ Q := by
  intros P Q h
  cases Classical.em Q with
  | inl q  => exact False.elim (h (λ _ => q))
  | inr nq => exact nq

theorem equivElim1 : ∀ {P Q : Prop}, Eq P Q → ¬ P ∨ Q := by
  intros P Q h
  rewrite [h]
  cases Classical.em Q with
  | inl q  => exact Or.inr q
  | inr nq => exact Or.inl nq

theorem equivElim2 : ∀ {P Q : Prop}, Eq P Q → P ∨ ¬ Q := by
  intros P Q h
  rewrite [h]
  cases Classical.em Q with
  | inl q  => exact Or.inl q
  | inr nq => exact Or.inr nq

theorem notEquivElim1 : ∀ {P Q : Prop}, ¬ (Eq P Q) → P ∨ Q := by
  intros P Q h
  exact match Classical.em P, Classical.em Q with
  | Or.inl p, _ => Or.inl p
  | _, Or.inl q => Or.inr q
  | Or.inr np, Or.inr nq =>
    absurd (propext (Iff.intro (λ p => absurd p np) (λ q => absurd q nq))) h

theorem notEquivElim2 : ∀ {P Q : Prop}, ¬ (Eq P Q) → ¬ P ∨ ¬ Q := by
  intros P Q h
  exact match Classical.em P, Classical.em Q with
  | Or.inr np, _ => Or.inl np
  | _, Or.inr nq => Or.inr nq
  | Or.inl p, Or.inl q =>
    absurd (propext (Iff.intro (λ _ => q) (λ _ => p))) h

theorem xorElim1 (h : XOr p q) : p ∨ q :=
  match h with
  | .inl hp _ => Or.inl hp
  | .inr _ hq => Or.inr hq

theorem xorElim2 (h : XOr p q) : ¬p ∨ ¬q :=
  match h with
  | .inl _ hnq => Or.inr hnq
  | .inr hnp _ => Or.inl hnp

theorem notXorElim1 (h : ¬XOr p q) : p ∨ ¬q :=
  match Classical.em p, Classical.em q with
  | Or.inl hp, _ => Or.inl hp
  | _, Or.inr hnq => Or.inr hnq
  | Or.inr hnp, Or.inl hq =>
    absurd (.inr hnp hq) h

theorem notXorElim2 (h : ¬XOr p q) : ¬p ∨ q :=
  match Classical.em p, Classical.em q with
  | Or.inr hnp, _ => Or.inl hnp
  | _, Or.inl hq => Or.inr hq
  | Or.inl hp, Or.inr hnq =>
    absurd (.inl hp hnq) h

theorem contradiction : ∀ {P : Prop}, P → ¬ P → False := λ p np => np p

theorem orComm : ∀ {P Q : Prop}, P ∨ Q → Q ∨ P := by
  intros P Q h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

theorem orAssocDir : ∀ {P Q R: Prop}, P ∨ Q ∨ R → (P ∨ Q) ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => exact Or.inl (Or.inl h₁)
  | inr h₂ => cases h₂ with
              | inl h₃ => exact Or.inl (Or.inr h₃)
              | inr h₄ => exact Or.inr h₄

theorem orAssocConv : ∀ {P Q R : Prop}, (P ∨ Q) ∨ R → P ∨ Q ∨ R := by
  intros P Q R h
  cases h with
  | inl h₁ => cases h₁ with
              | inl h₃ => exact Or.inl h₃
              | inr h₄ => exact (Or.inr (Or.inl h₄))
  | inr h₂ => exact Or.inr (Or.inr h₂)

theorem congOrRight : ∀ {P Q R : Prop}, (P → Q) → P ∨ R → Q ∨ R := by
  intros P Q R h₁ h₂
  cases h₂ with
  | inl h₃ => exact Or.inl (h₁ h₃)
  | inr h₄ => exact Or.inr h₄

theorem congOrLeft : ∀ {P Q R : Prop}, (P → Q) → R ∨ P → R ∨ Q := by
  intros P Q R h₁ h₂
  apply orComm
  exact congOrRight h₁ (orComm h₂)

theorem orImplies : ∀ {p q : Prop}, (¬ p → q) → p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp => Or.inl pp
     | Or.inr npp => match Classical.em q with
                     | Or.inl pq => Or.inr pq
                     | Or.inr npq => False.elim (npq (h npp))

theorem orImplies₂ : ∀ {p q : Prop}, (¬ p) ∨ q → p → q := by
  intros P Q h p
  cases h with
  | inl np => exact False.elim (np p)
  | inr q  => exact q

theorem orImplies₃ : ∀ {p q : Prop}, p ∨ q → ¬ p → q := by
  intros P Q h np
  cases h with
  | inl p => exact False.elim (np p)
  | inr q => exact q

def impliesElim : ∀ {p q : Prop}, (p → q) → ¬ p ∨ q :=
  by intros p q h
     exact match Classical.em p with
     | Or.inl pp =>  Or.inr (h pp)
     | Or.inr npp => Or.inl npp

theorem deMorganSmall : ∀ {p q : Prop}, ¬ (p ∨ q) → ¬ p ∧ ¬ q :=
  by intros p q h
     exact match Classical.em p, Classical.em q with
     | Or.inl pp,  _          => False.elim (h (Or.inl pp))
     | Or.inr _,   Or.inl pq  => False.elim (h (Or.inr pq))
     | Or.inr npp, Or.inr npq => And.intro npp npq

theorem deMorganSmall₂ : ∀ {p q : Prop}, ¬ p ∧ ¬ q → ¬ (p ∨ q) :=
  by intros p q h
     have ⟨np, nq⟩ := h
     exact match Classical.em p, Classical.em q with
     | Or.inl pp,  _   => False.elim (np pp)
     | _        ,  Or.inl pq  => False.elim (nq pq)
     | Or.inr npp, Or.inr npq => λ h₂ =>
                                    match h₂ with
                                    | Or.inl pp => False.elim (npp pp)
                                    | Or.inr pq => False.elim (npq pq)

theorem deMorganSmall₃ : ∀ {p q : Prop}, ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
  by intros p q h
     match Classical.em p, Classical.em q with
     | Or.inl hp, Or.inl hq  => exact False.elim (h (And.intro hp hq))
     | _,         Or.inr hnq => exact Or.inr hnq
     | Or.inr hnp, _        => exact Or.inl hnp

theorem notNotElim : ∀ {p : Prop}, ¬ ¬ p → p :=
  by intros p h
     exact match Classical.em p with
     | Or.inl pp => pp
     | Or.inr np => False.elim (h (λ p => np p))

theorem notNotIntro : ∀ {p : Prop}, p → ¬ ¬ p := λ p np => np p

theorem deMorgan : ∀ {l : List Prop}, ¬ orN (notN l) → andN l := by
  intros l h
  exact match l with
  | []   => True.intro
  | [t]  => by
    simp only [andN]
    simp only [notN, orN, map] at h
    cases Classical.em t with
    | inl tt  => exact tt
    | inr ntt => exact False.elim (h ntt)
  | h₁::h₂::t => by
    simp only [orN, notN, map] at h
    have ⟨ t₁, t₂ ⟩ := deMorganSmall h
    have ih := @deMorgan (h₂::t) t₂
    simp [andN]
    have t₁' := notNotElim t₁
    exact ⟨ t₁', andN_cons_append ▸ ih ⟩

theorem deMorgan₂ : ∀ {l : List Prop}, andN l → ¬ orN (notN l) := by
  intros l h
  exact match l with
  | [] => by
    simp [orN, notN]
  | [t] => by
    simp only [orN, notN]
    simp [andN] at h
    exact notNotIntro h
  | h₁::h₂::t => by
    simp only [orN, notN, map]
    simp [andN] at h
    apply deMorganSmall₂
    have nnh₁ := notNotIntro (And.left h)
    have ih := @deMorgan₂ (h₂::t) (And.right (andN_cons_append ▸ h))
    exact ⟨nnh₁, ih⟩

theorem deMorgan₃ : ∀ {l : List Prop}, ¬ orN l → andN (notN l) := by
  intros l h
  exact match l with
  | [] => True.intro
  | [t] => by
    simp only [andN, notN, map]
    simp only [orN, Not] at h
    exact h
  | h₁::h₂::t => by
    simp only [orN, Not] at h
    have ⟨t₁, t₂⟩ := deMorganSmall h
    simp only [orN, Not] at t₂
    simp [andN, notN, map]
    have ih := @deMorgan₃ (h₂::t) t₂
    exact ⟨t₁, andN_cons_append ▸ ih⟩

theorem cnfAndNeg' : ∀ (l : List Prop), andN l ∨ orN (notN l) :=
  by intro l
     apply orComm
     apply orImplies
     intro h
     exact deMorgan h

theorem cnfAndNeg : orN (andN l :: notN l) := by
  cases l with
  | nil => trivial
  | cons l ls =>
    apply cnfAndNeg'

theorem cnfAndPos : ∀ (l : List Prop) (i : Nat), ¬ (andN l) ∨ List.getD l i True :=
  by intros l i
     apply orImplies
     intro h
     have h' := notNotElim h
     match l with
     | [] => exact True.intro
     | [p] =>
       match i with
       | 0 => exact h'
       | _ + 1 => exact True.intro
     | p₁::p₂::ps =>
       match i with
       | 0 => exact And.left h'
       | i' + 1 =>
         have IH :=  cnfAndPos (p₂::ps) i'
         exact orImplies₂ IH (And.right h')

theorem cnfOrNeg : ∀ (l : List Prop) (i : Nat), orN l ∨ ¬ List.getD l i False := by
  intros l i
  apply orImplies
  intros orNl p
  have andNotl := @deMorgan₃ l orNl
  match l with
  | [] => exact False.elim p
  | [h] =>
    match i with
    | 0 => exact absurd p orNl
    | _ + 1 => exact False.elim p
  | h₁::h₂::hs =>
    match i with
    | 0 => have ⟨nh₁p, _⟩ := andNotl
           exact absurd p nh₁p
    | i' + 1 =>
      have IH := cnfOrNeg (h₂::hs) i'
      have orNTail := orImplies₂ (orComm IH) p
      have ⟨_, notOrNTail⟩ := deMorganSmall orNl
      exact absurd orNTail notOrNTail

theorem cnfOrPos' : ∀ (l : List Prop), ¬ orN l ∨ orN l := λ l => orComm (Classical.em (orN l))

theorem cnfOrPos : orN ((¬orN l) :: l) := by
  cases l with
  | nil => exact not_false
  | cons l ls =>
    simp only [orN]
    apply cnfOrPos'

theorem cnfImpliesPos : ∀ {p q : Prop}, ¬ (p → q) ∨ ¬ p ∨ q := by
  intros p q
  match Classical.em p, Classical.em q with
  | _,         Or.inl hq  => exact Or.inr (Or.inr hq)
  | Or.inl hp, Or.inr hnq => apply Or.inl
                             intro f
                             exact absurd (f hp) hnq
  | Or.inr hnp, _         => exact Or.inr (Or.inl hnp)

theorem cnfImpliesNeg1 : ∀ {p q : Prop}, (p → q) ∨ p := by
  intros p q
  apply orComm
  apply orImplies
  exact flip absurd

theorem cnfImpliesNeg2 : ∀ {p q : Prop}, (p → q) ∨ ¬ q := by
  intros p q
  apply orComm
  apply orImplies
  intros hnnq _
  exact notNotElim hnnq

theorem cnfEquivPos1 : ∀ {p q : Prop}, p ≠ q ∨ ¬ p ∨ q := by
  intros _ _
  apply orImplies
  exact equivElim1 ∘ notNotElim

theorem cnfEquivPos2 : ∀ {p q : Prop}, p ≠ q ∨ p ∨ ¬ q := by
  intros _ _
  apply orImplies
  exact equivElim2 ∘ notNotElim

theorem cnfEquivNeg1 : ∀ {p q : Prop}, p = q ∨ p ∨ q := by
  intros _ _
  apply orImplies
  exact notEquivElim1

theorem cnfEquivNeg2 : ∀ {p q : Prop}, p = q ∨ ¬ p ∨ ¬ q := by
  intros _ _
  apply orImplies
  exact notEquivElim2

theorem cnfXorPos1 : ¬(XOr p q) ∨ p ∨ q :=
  orImplies (xorElim1 ∘ notNotElim)

theorem cnfXorPos2 : ¬(XOr p q) ∨ ¬p ∨ ¬q :=
  orImplies (xorElim2 ∘ notNotElim)

theorem cnfXorNeg1 : (XOr p q) ∨ ¬p ∨ q :=
  orImplies notXorElim2

theorem cnfXorNeg2 : (XOr p q) ∨ p ∨ ¬q :=
  orImplies notXorElim1

theorem iteIntro {α : Type u} {c : Prop} {t e : α} : ite c ((ite c t e) = t) ((ite c t e) = e) := by
  match Classical.em c with
  | Or.inl hc  => rw [if_pos hc, if_pos hc]
  | Or.inr hnc => rw [if_neg hnc, if_neg hnc]

theorem congrIte [Decidable c₁] [Decidable c₂] {t₁ t₂ e₁ e₂ : α} :
    c₁ = c₂ → t₁ = t₂ → e₁ = e₂ → ite c₁ t₁ e₁ = ite c₂ t₂ e₂ := by
  intros h₁ h₂ h₃
  simp only [h₁, h₂, h₃]

theorem congrHAdd {α β γ : Type} [HAdd α β γ] : ∀ {a₁ a₂ : α} {b₁ b₂ : β},
    a₁ = a₂ → b₁ = b₂ → a₁ + b₁ = a₂ + b₂ := by
  intros a₁ a₂ b₁ b₂ h₁ h₂
  rw [h₁, h₂]

theorem eqResolve {P Q : Prop} : P → (P = Q) → Q := by
  intros h₁ h₂
  rewrite [← h₂]
  exact h₁

theorem dupOr {P Q : Prop} : P ∨ P ∨ Q → P ∨ Q := λ h =>
  match h with
  | Or.inl p          => Or.inl p
  | Or.inr (Or.inl p) => Or.inl p
  | Or.inr (Or.inr q) => Or.inr q

theorem dupOr₂ {P : Prop} : P ∨ P → P := λ h =>
  match h with
  | Or.inl p => p
  | Or.inr p => p

theorem and_elim (hps : andN ps) (i : Nat) {hi : i < ps.length} : ps[i] := match ps with
  | []  => nomatch hi
  | [_] => match i with
    | 0     => hps
    | _ + 1 => nomatch hi
  | p₁ :: p₂ :: ps => match i with
    | 0     => hps.left
    | i + 1 => Eq.symm (List.getElem_cons_succ p₁ (p₂ :: ps) i hi) ▸ and_elim hps.right i

theorem not_or_elim (hnps : ¬orN ps) (i : Nat) {hi : i < ps.length} : ¬ps[i] := match ps with
  | []  => nomatch hi
  | [_] => match i with
    | 0     => hnps
    | _ + 1 => nomatch hi
  | p₁ :: p₂ :: ps => match i with
    | 0     => (deMorganSmall hnps).left
    | i + 1 => Eq.symm (List.getElem_cons_succ p₁ (p₂ :: ps) i hi) ▸ not_or_elim (deMorganSmall hnps).right i

theorem notAnd : ∀ (l : List Prop), ¬ andN l → orN (notN l) := by
  intros l h
  match l with
  | []         => exact False.elim (h True.intro)
  | [_]        => exact h
  | p₁::p₂::ps => simp [orN, notN, map]
                  match deMorganSmall₃ h with
                  | Or.inl hnp₁ => exact Or.inl hnp₁
                  | Or.inr hnAndTail =>
                    have IH := notAnd (p₂::ps) hnAndTail
                    exact Or.inr (orN_cons_append ▸ IH)

syntax "flipNotAnd " term ("[" term,* "]")? : term
macro_rules
| `(flipNotAnd $premiss:term [ $[$x:term],* ]) => `(notAnd [ $[$x],* ] $premiss)

theorem modusPonens : ∀ {A B : Prop}, A → (A → B) → B := λ x f => f x

theorem trueIntro : ∀ {A : Prop}, A → A = True := by
  intros A h
  exact propext (Iff.intro (λ _ => True.intro) (λ _ => h))

theorem trueImplies {p : Prop} : (True → p) → p := by
  intro htp
  exact htp trivial

theorem trueElim : ∀ {A : Prop}, A = True → A := by
  intros A h
  rewrite [h]
  trivial
theorem trueElim₂ : ∀ {A : Prop}, True = A → A :=
  trueElim ∘ Eq.symm

theorem falseIntro : ∀ {A : Prop}, ¬ A → A = False :=
  λ h => propext (Iff.intro (λ a => h a) (λ ff => False.elim ff))
theorem falseIntro₂ : ∀ {A : Prop}, ¬ A → False = A := Eq.symm ∘ falseIntro

theorem falseElim : ∀ {A : Prop}, A = False → ¬ A := λ h ha =>
  match h with
  | rfl => ha
theorem falseElim₂ : ∀ {A : Prop}, False = A → ¬ A := falseElim ∘ Eq.symm

theorem negSymm {α : Type u} {a b : α} : a ≠ b → b ≠ a := λ h f => h (Eq.symm f)

theorem eq_not_not (p : Prop) : p = ¬¬p := propext (not_not.symm)

theorem orN_cons : orN (t :: l) = (t ∨ orN l) := by
  cases l with
  | nil => simp [orN]
  | cons t' l => simp [orN]

theorem orN_eraseIdx (hj : j < qs.length) : (orN (qs.eraseIdx j) ∨ qs[j]) = (orN qs) := by
  revert j
  induction qs with
  | nil =>
    intro j hj
    simp at hj
  | cons t l ih =>
    intro j hj
    cases j with
    | zero =>
      simp only [eraseIdx_cons_zero, getElem_cons_zero, orN_cons, eraseIdx_cons_succ, getElem_cons_succ]
      rw [or_comm]
    | succ j =>
      simp only [eraseIdx_cons_succ, getElem_cons_succ, orN_cons, eraseIdx, or_assoc]
      congr
      rw [@ih j (by rw [length_cons, succ_lt_succ_iff] at hj; exact hj)]

def subList' (xs : List α) (i j : Nat) : List α :=
  List.drop i (xs.take j)

theorem orN_subList (hps : orN ps) (hpq : ps = subList' qs i j): orN qs := by
  revert i j ps
  induction qs with
  | nil =>
    intro ps i j hp hps
    simp [subList', *] at *; assumption
  | cons t l ih =>
    simp only [subList'] at *
    intro ps i j hp hps
    rw [orN_cons]
    cases j with
    | zero =>
      simp [*, orN] at *
    | succ j =>
      simp only [List.take_succ_cons] at hps
      cases i with
      | zero =>
        simp only [hps, orN_cons, drop_zero] at hp
        exact congOrLeft (fun hp => @ih (drop 0 (take j l)) 0 j (by simp [hp]) rfl) hp
      | succ i =>
        apply Or.inr
        apply @ih ps i j hp
        simp [hps]

theorem length_take (h : n ≤ l.length) : (take n l).length = n := by
  revert n
  induction l with
  | nil => intro n h; simp at h; simp [h]
  | cons t l ih =>
    intro n h
    cases n with
    | zero => simp
    | succ n => simp [ih (by rw [length_cons, succ_le_succ_iff] at h; exact h)]

theorem length_eraseIdx (h : i < l.length) : (eraseIdx l i).length = l.length -1 := by
  revert i
  induction l with
  | nil => simp
  | cons t l ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i =>
      simp
      rw [length_cons, succ_lt_succ_iff] at hi
      rw [ih hi, Nat.sub_add_cancel (zero_lt_of_lt hi)]

theorem take_append (a b : List α) : take a.length (a ++ b) = a := by
  have H3:= take_append_drop a.length (a ++ b)
  apply (append_inj H3 _).1
  rw [length_take]
  rw [length_append]
  apply le_add_right

theorem drop_append (a b : List α): drop a.length (a ++ b) = b := by
  have H3:= take_append_drop a.length (a ++ b)
  apply (append_inj H3 _).2
  rw [length_take]
  rw [length_append]
  apply le_add_right

theorem orN_append_left (hps : orN ps) : orN (ps ++ qs) := by
  apply @orN_subList ps (ps ++ qs) 0 ps.length hps
  simp [subList', take_append]

theorem orN_append_right (hqs : orN qs) : orN (ps ++ qs) := by
  apply @orN_subList qs (ps ++ qs) ps.length (ps.length + qs.length) hqs
  simp only [←length_append, subList', take_length, drop_append]

theorem orN_resolution (hps : orN ps) (hqs : orN qs) (hi : i < ps.length) (hj : j < qs.length) (hij : ps[i] = ¬qs[j]) : orN (ps.eraseIdx i ++ qs.eraseIdx j) := by
  have H1 := orN_eraseIdx hj
  have H2 := orN_eraseIdx hi
  by_cases h : ps[i]
  · simp only [eq_iff_iff, true_iff, iff_true, h, hqs, hij, hps] at *
    apply orN_append_right (by simp [*] at *; exact H1)
  · simp only [hps, hqs, h, eq_iff_iff, false_iff, not_not, iff_true, or_false,
    not_false_eq_true] at *
    apply orN_append_left H2

theorem implies_of_not_and : ¬(andN (ps ++ [¬q])) → impliesN ps q := by
  induction ps with
  | nil => exact notNotElim
  | cons p ps ih =>
    simp only [andN, impliesN]
    intro hnpps hp
    cases ps
    <;> have hnpnps := deMorganSmall₃ hnpps
    <;> match hnpnps with
        | .inl hnp => contradiction
        | .inr hnps => exact ih hnps

end Smt.Reconstruct.Prop

namespace Smt.Reconstruct.Prop

-- https://github.com/cvc5/cvc5/blob/main/src/theory/booleans/rewrites

open Function

theorem bool_double_not_elim : (¬¬t) = t :=
  propext Classical.not_not
theorem bool_not_true (h : t = False) : (¬t) = True := h ▸ propext not_false_iff
theorem bool_not_false (h : t = True) : (¬t) = False := h ▸ propext not_true

theorem bool_eq_true : (t = True) = t :=
  propext ⟨of_eq_true, eq_true⟩
theorem bool_eq_false : (t = False) = ¬t :=
  propext ⟨(· ▸ not_false), eq_false⟩
theorem bool_eq_nrefl : (t = ¬t) = False :=
  propext ⟨(have H : t ↔ ¬t := · ▸ ⟨id, id⟩; have f h := H.mp h h; f (H.mpr f)), False.elim⟩

theorem bool_impl_false1 : (t → False) = ¬t :=
  propext ⟨(·), (·)⟩
theorem bool_impl_false2 : (False → t) = True :=
  propext ⟨const _ trivial, const _ False.elim⟩
theorem bool_impl_true1 {t : Prop} : (t → True) = True :=
  propext ⟨const _ trivial, const _ (const _ trivial)⟩
theorem bool_impl_true2 {t : Prop} : (True → t) = t :=
  propext ⟨(· trivial), const _⟩
theorem bool_impl_elim : (t → s) = orN [¬t, s] :=
  propext ⟨fun hts => (Classical.em t).elim (Or.inr $ hts ·) Or.inl, (fun ht => ·.elim (absurd ht) id)⟩

-- used in proof elaboration
theorem bool_dual_impl_eq : andN [t → s, s → t] = (t = s) :=
  propext ⟨fun ⟨hts, hst⟩ => propext ⟨hts, hst⟩, (· ▸ ⟨id, id⟩)⟩

theorem bool_and_conf : andN (xs ++ w :: (ys ++ (¬w) :: zs)) = False := by
  simp only [andN_append, andN_cons_append]
  exact propext ⟨fun ⟨_, hw, _, hnw, _⟩ => absurd hw hnw, False.elim⟩
theorem bool_and_conf2 : andN (xs ++ (¬w) :: (ys ++ w :: zs)) = False := by
  simp only [andN_append, andN_cons_append]
  exact propext ⟨fun ⟨_, hnw, _, hw, _⟩ => absurd hw hnw, False.elim⟩
theorem bool_or_taut : orN (xs ++ w :: (ys ++ (¬w) :: zs)) = True := by
  simp only [orN_append, orN_cons_append]
  exact propext $ .intro
    (const _ trivial)
    (eq_true (Classical.em w) ▸ (·.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl)))
theorem bool_or_taut2 : orN (xs ++ (¬w) :: (ys ++ w :: zs)) = True := by
  simp only [orN_append, orN_cons_append]
  exact propext $ .intro
    (const _ trivial)
    (eq_true (Classical.em w).symm ▸ (·.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl)))

theorem bool_or_de_morgan : (¬orN (x :: y :: zs)) = andN [¬x, ¬orN (y :: zs)] :=
  propext not_or
theorem bool_implies_de_morgan : (¬(x → y)) = andN [x, ¬y] :=
  propext Classical.not_imp_iff_and_not
theorem bool_and_de_morgan : (¬andN (x :: y :: zs)) = orN [¬x, ¬andN (y :: zs)] :=
  propext Classical.not_and_iff_not_or_not

theorem bool_or_and_distrib :
  orN (andN (y₁ :: y₂ :: ys) :: z₁ :: zs) = andN [orN (y₁ :: z₁ :: zs), orN (andN (y₂ :: ys) :: z₁ :: zs)] :=
  match zs with
  | []
  | _ :: _ => propext and_or_right

-- Used for diamonds preprocessing
theorem bool_implies_or_distrib : (orN (y₁ :: y₂ :: ys) → z) = andN [y₁ → z, orN (y₂ :: ys) → z] :=
  match ys with
  | []
  | _ :: _ => propext or_imp

theorem bool_xor_refl : XOr x x = False :=
  propext ⟨(·.elim absurd (flip absurd)), False.elim⟩
theorem bool_xor_nrefl : (XOr x ¬x) = True :=
  propext ⟨const _ trivial,
           const _ ((Classical.em x).elim (fun hx => .inl hx (· hx)) (fun hnx => .inr hnx hnx))⟩
theorem bool_xor_false : XOr x False = x :=
  propext ⟨(·.elim (flip (const _ id)) (const _ False.elim)), (.inl · not_false)⟩
theorem bool_xor_true : XOr x True = ¬x :=
  propext ⟨(·.elim (const _ (False.elim $ not_true.mp ·)) (flip (const _ id))), (.inr · trivial)⟩
theorem bool_xor_comm : XOr x y = XOr y x :=
  propext ⟨XOr.symm, XOr.symm⟩
theorem bool_xor_elim : (XOr x y) = ((¬x) = y) :=
  propext (Iff.intro
    (·.elim (fun hx hny => propext ⟨(absurd hx ·), (absurd · hny)⟩) (fun hnx hy => propext ⟨const _ hy, const _ hnx⟩))
    (fun hnxy => (Classical.em y).elim (fun hy => XOr.inr (hnxy ▸ hy) hy)
                                       (fun hny => XOr.inl (Classical.not_not.mp (hnxy ▸ hny)) hny)))
theorem bool_not_xor_elim : (¬XOr x y) = (x = y) :=
  propext (Iff.intro
    (fun hnxy => propext (Iff.intro
       (fun hx => Classical.byContradiction (hnxy $ XOr.inl hx ·))
       (fun hy => Classical.byContradiction (hnxy $ XOr.inr · hy))))
    fun hxy => hxy ▸ fun hxx => hxx.elim (fun hx hnx => hnx hx) (· ·))

theorem bool_not_eq_elim1 : (¬x = y) = ((¬x) = y) :=
  propext
    (Iff.intro (bool_not_xor_elim ▸ fun hnnxy => (Classical.not_not.mp hnnxy).elim
      (fun hx hny => propext ⟨(absurd hx ·), (absurd · hny)⟩)
      (fun hnx hy => propext ⟨const _ hy, const _ hnx⟩))
    (@iff_not_self x $ · ▸ · ▸ Iff.rfl))
theorem bool_not_eq_elim2 : (¬x = y) = (x = ¬y) :=
  propext
    (Iff.intro (bool_not_xor_elim ▸ fun hnnxy => (Classical.not_not.mp hnnxy).elim
      (fun hx hny => propext ⟨const _ hny, const _ hx⟩)
      (fun hnx hy => propext ⟨(absurd · hnx), (absurd hy ·)⟩))
    (@iff_not_self y $ · ▸ · ▸ Iff.rfl))

theorem ite_neg_branch [h : Decidable c] : x = ¬y → ite c x y = (c = x) :=
  fun hxny => hxny ▸ h.byCases
    (fun hc => if_pos hc ▸ propext ⟨(propext ⟨const _ ·, const _ hc⟩), (· ▸ hc)⟩)
    (fun hnc => if_neg hnc ▸ propext
      ⟨fun hy => propext ⟨fun hc => False.elim (hnc hc), fun hny => False.elim (hny hy)⟩,
       fun hcny => bool_double_not_elim (t := y) ▸ hcny ▸ hnc⟩)

theorem ite_then_true [h : Decidable c] : ite c True x = orN [c, x] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨const _ (Or.inl hc), const _ trivial⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨Or.inr, (·.elim (absurd · hnc) id)⟩)
theorem ite_else_false [h : Decidable c] : ite c x False = andN [c, x] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨And.intro hc, And.right⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨False.elim, (absurd ·.left hnc)⟩)
theorem ite_then_false [h : Decidable c] : ite c False x = andN [¬c, x] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨False.elim, (absurd hc ·.left)⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨And.intro hnc, And.right⟩)
theorem ite_else_true [h : Decidable c] : ite c x True = orN [¬c, x] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨Or.inr, (·.elim (absurd hc) id)⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨const _ (Or.inl hnc), const _ trivial⟩)

theorem ite_then_lookahead_self [h : Decidable c] : ite c c x = ite c True x := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ eq_true hc)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)
theorem ite_else_lookahead_self [h : Decidable c] : ite c x c = ite c x False := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ eq_false hnc)

theorem ite_then_lookahead_not_self [h : Decidable c] : ite c (¬c) x = ite c False x := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ eq_false (not_not_intro hc))
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)
theorem ite_else_lookahead_not_self [h : Decidable c] : ite c x (¬c) = ite c x True := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ eq_true hnc)

theorem ite_expand [h : Decidable c] : ite c x y = andN [orN [¬c, x], orN [c, y]] := h.byCases
  (fun hc => if_pos hc ▸ propext ⟨(⟨Or.inr ·, Or.inl hc⟩), (·.left.resolve_left (not_not_intro hc))⟩)
  (fun hnc => if_neg hnc ▸ propext ⟨(⟨Or.inl hnc, Or.inr ·⟩), (·.right.resolve_left hnc)⟩)

theorem bool_not_ite_elim [h : Decidable c] : (¬ite c x y) = ite c (¬x) (¬y) := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)

end Smt.Reconstruct.Prop

theorem exists_congr_eq {p q : α → Prop} (h : ∀ a, p a = q a) : (∃ a, p a) = (∃ a, q a) :=
  propext (exists_congr (h · ▸ Iff.rfl))

theorem forall_const_eq (α : Sort u) [Nonempty α] {p q : Prop} (h : p = q) : (α → p) = q :=
  h ▸ propext (forall_const α)

namespace Classical

theorem exists_elim {α} {p : α → Prop} : (∃ x, p x) = ¬∀ x, ¬p x :=
  Eq.symm (propext not_forall_not)

theorem not_forall_eq (p : α → Prop) : (¬∀ (x : α), p x) = ∃ x, ¬p x := propext not_forall

theorem not_not_eq (p : Prop) : (¬¬p) = p := propext not_not

theorem epsilon_spec_aux' {α : Sort u} (h : Nonempty α) (p : α → Prop) : (¬∀ y, p y) → ¬p (@epsilon α h (fun x => ¬p x)) :=
  propext not_forall ▸ epsilon_spec_aux h (fun x => ¬p x)

end Classical

namespace Smt.Reconstruct.Quant

theorem miniscope_and {p q : α → Prop} : (∀ x, p x ∧ q x) = ((∀ x, p x) ∧ (∀ x, q x)) :=
  propext forall_and

/-- A list that can store proofs. Mainly for `miniscope_andN`. -/
inductive PList (α : Sort u) where
  | nil : PList α
  | cons (head : α) (tail : PList α) : PList α

def PList.map (f : α → β) : PList α → PList β
  | .nil        => .nil
  | .cons h t   => .cons (f h) (map f t)

def pAndN : PList Prop → Prop
  | .nil         => True
  | .cons h .nil => h
  | .cons h t    => h ∧ pAndN t

theorem miniscope_andN {ps : PList (α → Prop)} :
  (∀ x, pAndN (ps.map (· x))) = pAndN (ps.map (∀ x, · x)) :=
  match ps with
  | .nil             => propext ⟨fun _ => trivial, fun _ _ => trivial⟩
  | .cons _ .nil     => rfl
  | .cons _ (.cons p₂ ps) => miniscope_and ▸ @miniscope_andN α (.cons p₂ ps) ▸ rfl

theorem miniscope_or_left {p : α → Prop} {q : Prop} : (∀ x, p x ∨ q) = ((∀ x, p x) ∨ q) :=
  propext <| Iff.intro
    (fun hpxq => (Classical.em q).elim (Or.inr ·) (fun hnq => Or.inl (fun x => (hpxq x).resolve_right hnq)))
    (fun hpxq x => hpxq.elim (fun hpx => Or.inl (hpx x)) (Or.inr ·))

theorem miniscope_or_right {p : Prop} {q : α → Prop} : (∀ x, p ∨ q x) = (p ∨ (∀ x, q x)) :=
  propext or_comm ▸ miniscope_or_left ▸ forall_congr (fun _ => propext or_comm)

theorem miniscope_orN {ps : List Prop} {q : α → Prop} {rs : List Prop} :
  (∀ x, orN (ps ++ q x :: rs)) = orN (ps ++ (∀ x, q x) :: rs) :=
  match ps with
  | []             => by cases rs <;> simp [orN, miniscope_or_left]
  | [p]            => miniscope_or_right ▸ @miniscope_orN α [] q rs ▸ rfl
  | p₁ :: p₂ :: ps => miniscope_or_right ▸ @miniscope_orN α (p₂ :: ps) q rs ▸ rfl

theorem miniscope_ite {c : Prop} [h : Decidable c] {p q : α → Prop} :
  (∀ x, ite c (p x) (q x)) = ite c (∀ x, p x) (∀ x, q x) :=
  h.byCases
    (fun hc => if_pos hc ▸ propext ⟨((if_pos hc).mp $ · ·), (if_pos hc ▸ · ·)⟩)
    (fun hnc => if_neg hnc ▸ propext ⟨((if_neg hnc).mp $ · ·), (if_neg hnc ▸ · ·)⟩)

theorem var_elim_eq {t : α} : (∀ x, x ≠ t) = False :=
  propext ⟨fun hnxt => absurd rfl (hnxt t), False.elim⟩

theorem var_elim_eq_or {t : α} {p : α → Prop} : (∀ x, x ≠ t ∨ p x) = p t :=
  propext <| Iff.intro
    (fun hpx => (hpx t).resolve_left (absurd rfl ·))
    (fun hpt x => (Classical.em (x = t)).elim (Or.inr $ · ▸ hpt) (Or.inl ·))

end Smt.Reconstruct.Quant

/-!
# Definitions and properties of `coprime`
-/

namespace Nat

/-!
### `coprime`

See also `nat.coprime_of_dvd` and `nat.coprime_of_dvd'` to prove `nat.Coprime m n`.
-/

/-- `m` and `n` are coprime, or relatively prime, if their `gcd` is 1. -/
@[reducible] def Coprime (m n : Nat) : Prop := gcd m n = 1

-- if we don't inline this, then the compiler computes the GCD even if it already has it
@[inline] instance (m n : Nat) : Decidable (Coprime m n) := inferInstanceAs (Decidable (_ = 1))

theorem coprime_iff_gcd_eq_one : Coprime m n ↔ gcd m n = 1 := .rfl

theorem Coprime.gcd_eq_one : Coprime m n → gcd m n = 1 := id

theorem Coprime.symm : Coprime n m → Coprime m n := (gcd_comm m n).trans

theorem coprime_comm : Coprime n m ↔ Coprime m n := ⟨Coprime.symm, Coprime.symm⟩

theorem Coprime.dvd_of_dvd_mul_right (H1 : Coprime k n) (H2 : k ∣ m * n) : k ∣ m := by
  let t := dvd_gcd (Nat.dvd_mul_left k m) H2
  rwa [gcd_mul_left, H1.gcd_eq_one, Nat.mul_one] at t

theorem Coprime.dvd_of_dvd_mul_left (H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
  H1.dvd_of_dvd_mul_right (by rwa [Nat.mul_comm])

theorem Coprime.gcd_mul_left_cancel (m : Nat) (H : Coprime k n) : gcd (k * m) n = gcd m n :=
  have H1 : Coprime (gcd (k * m) n) k := by
    rw [Coprime, Nat.gcd_assoc, H.symm.gcd_eq_one, gcd_one_right]
  Nat.dvd_antisymm
    (dvd_gcd (H1.dvd_of_dvd_mul_left (gcd_dvd_left _ _)) (gcd_dvd_right _ _))
    (gcd_dvd_gcd_mul_left_left _ _ _)

theorem Coprime.gcd_mul_right_cancel (m : Nat) (H : Coprime k n) : gcd (m * k) n = gcd m n := by
  rw [Nat.mul_comm m k, H.gcd_mul_left_cancel m]

theorem Coprime.gcd_mul_left_cancel_right (n : Nat)
    (H : Coprime k m) : gcd m (k * n) = gcd m n := by
  rw [gcd_comm m n, gcd_comm m (k * n), H.gcd_mul_left_cancel n]

theorem Coprime.gcd_mul_right_cancel_right (n : Nat)
    (H : Coprime k m) : gcd m (n * k) = gcd m n := by
  rw [Nat.mul_comm n k, H.gcd_mul_left_cancel_right n]

theorem coprime_div_gcd_div_gcd
    (H : 0 < gcd m n) : Coprime (m / gcd m n) (n / gcd m n) := by
  rw [coprime_iff_gcd_eq_one, gcd_div (gcd_dvd_left m n) (gcd_dvd_right m n), Nat.div_self H]

theorem not_coprime_of_dvd_of_dvd (dgt1 : 1 < d) (Hm : d ∣ m) (Hn : d ∣ n) : ¬ Coprime m n :=
  fun co => Nat.not_le_of_gt dgt1 <| Nat.le_of_dvd Nat.zero_lt_one <| by
    rw [← co.gcd_eq_one]; exact dvd_gcd Hm Hn

theorem exists_coprime (m n : Nat) :
    ∃ m' n', Coprime m' n' ∧ m = m' * gcd m n ∧ n = n' * gcd m n := by
  cases eq_zero_or_pos (gcd m n) with
  | inl h0 =>
    rw [gcd_eq_zero_iff] at h0
    refine ⟨1, 1, gcd_one_left 1, ?_⟩
    simp [h0]
  | inr hpos =>
    exact ⟨_, _, coprime_div_gcd_div_gcd hpos,
      (Nat.div_mul_cancel (gcd_dvd_left m n)).symm,
      (Nat.div_mul_cancel (gcd_dvd_right m n)).symm⟩

theorem exists_coprime' (H : 0 < gcd m n) :
    ∃ g m' n', 0 < g ∧ Coprime m' n' ∧ m = m' * g ∧ n = n' * g :=
  let ⟨m', n', h⟩ := exists_coprime m n; ⟨_, m', n', H, h⟩

theorem Coprime.mul (H1 : Coprime m k) (H2 : Coprime n k) : Coprime (m * n) k :=
  (H1.gcd_mul_left_cancel n).trans H2

theorem Coprime.mul_right (H1 : Coprime k m) (H2 : Coprime k n) : Coprime k (m * n) :=
  (H1.symm.mul H2.symm).symm

theorem Coprime.coprime_dvd_left (H1 : m ∣ k) (H2 : Coprime k n) : Coprime m n := by
  apply eq_one_of_dvd_one
  rw [Coprime] at H2
  have := Nat.gcd_dvd_gcd_of_dvd_left n H1
  rwa [← H2]

theorem Coprime.coprime_dvd_right (H1 : n ∣ m) (H2 : Coprime k m) : Coprime k n :=
  (H2.symm.coprime_dvd_left H1).symm

theorem Coprime.coprime_mul_left (H : Coprime (k * m) n) : Coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_left _ _)

theorem Coprime.coprime_mul_right (H : Coprime (m * k) n) : Coprime m n :=
  H.coprime_dvd_left (Nat.dvd_mul_right _ _)

theorem Coprime.coprime_mul_left_right (H : Coprime m (k * n)) : Coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_left _ _)

theorem Coprime.coprime_mul_right_right (H : Coprime m (n * k)) : Coprime m n :=
  H.coprime_dvd_right (Nat.dvd_mul_right _ _)

theorem Coprime.coprime_div_left (cmn : Coprime m n) (dvd : a ∣ m) : Coprime (m / a) n := by
  match eq_zero_or_pos a with
  | .inl h0 =>
    rw [h0] at dvd
    rw [Nat.eq_zero_of_zero_dvd dvd] at cmn ⊢
    simp; assumption
  | .inr hpos =>
    let ⟨k, hk⟩ := dvd
    rw [hk, Nat.mul_div_cancel_left _ hpos]
    rw [hk] at cmn
    exact cmn.coprime_mul_left

theorem Coprime.coprime_div_right (cmn : Coprime m n) (dvd : a ∣ n) : Coprime m (n / a) :=
  (cmn.symm.coprime_div_left dvd).symm

theorem coprime_mul_iff_left : Coprime (m * n) k ↔ Coprime m k ∧ Coprime n k :=
  ⟨fun h => ⟨h.coprime_mul_right, h.coprime_mul_left⟩,
   fun ⟨h, _⟩ => by rwa [coprime_iff_gcd_eq_one, h.gcd_mul_left_cancel n]⟩

theorem coprime_mul_iff_right : Coprime k (m * n) ↔ Coprime k m ∧ Coprime k n := by
  rw [@coprime_comm k, @coprime_comm k, @coprime_comm k, coprime_mul_iff_left]

theorem Coprime.gcd_left (k : Nat) (hmn : Coprime m n) : Coprime (gcd k m) n :=
  hmn.coprime_dvd_left <| gcd_dvd_right k m

theorem Coprime.gcd_right (k : Nat) (hmn : Coprime m n) : Coprime m (gcd k n) :=
  hmn.coprime_dvd_right <| gcd_dvd_right k n

theorem Coprime.gcd_both (k l : Nat) (hmn : Coprime m n) : Coprime (gcd k m) (gcd l n) :=
  (hmn.gcd_left k).gcd_right l

theorem Coprime.mul_dvd_of_dvd_of_dvd (hmn : Coprime m n) (hm : m ∣ a) (hn : n ∣ a) : m * n ∣ a :=
  let ⟨_, hk⟩ := hm
  hk.symm ▸ Nat.mul_dvd_mul_left _ (hmn.symm.dvd_of_dvd_mul_left (hk ▸ hn))

@[simp] theorem coprime_zero_left (n : Nat) : Coprime 0 n ↔ n = 1 := by simp [Coprime]

@[simp] theorem coprime_zero_right (n : Nat) : Coprime n 0 ↔ n = 1 := by simp [Coprime]

theorem coprime_one_left : ∀ n, Coprime 1 n := gcd_one_left

theorem coprime_one_right : ∀ n, Coprime n 1 := gcd_one_right

@[simp] theorem coprime_one_left_eq_true (n) : Coprime 1 n = True := eq_true (coprime_one_left _)

@[simp] theorem coprime_one_right_eq_true (n) : Coprime n 1 = True := eq_true (coprime_one_right _)

@[simp] theorem coprime_self (n : Nat) : Coprime n n ↔ n = 1 := by simp [Coprime]

theorem Coprime.pow_left (n : Nat) (H1 : Coprime m k) : Coprime (m ^ n) k := by
  induction n with
  | zero => exact coprime_one_left _
  | succ n ih => have hm := H1.mul ih; rwa [Nat.pow_succ, Nat.mul_comm]

theorem Coprime.pow_right (n : Nat) (H1 : Coprime k m) : Coprime k (m ^ n) :=
  (H1.symm.pow_left n).symm

theorem Coprime.pow {k l : Nat} (m n : Nat) (H1 : Coprime k l) : Coprime (k ^ m) (l ^ n) :=
  (H1.pow_left _).pow_right _

theorem Coprime.eq_one_of_dvd {k m : Nat} (H : Coprime k m) (d : k ∣ m) : k = 1 := by
  rw [← H.gcd_eq_one, gcd_eq_left d]

theorem Coprime.gcd_mul (k : Nat) (h : Coprime m n) : gcd k (m * n) = gcd k m * gcd k n :=
  Nat.dvd_antisymm
    (gcd_mul_right_dvd_mul_gcd k m n)
    ((h.gcd_both k k).mul_dvd_of_dvd_of_dvd
      (gcd_dvd_gcd_mul_right_right ..)
      (gcd_dvd_gcd_mul_left_right ..))

theorem gcd_mul_gcd_of_coprime_of_mul_eq_mul
    (cop : Coprime c d) (h : a * b = c * d) : a.gcd c * b.gcd c = c := by
  apply Nat.dvd_antisymm
  · apply ((cop.gcd_left _).mul (cop.gcd_left _)).dvd_of_dvd_mul_right
    rw [← h]
    apply Nat.mul_dvd_mul (gcd_dvd ..).1 (gcd_dvd ..).1
  · rw [gcd_comm a, gcd_comm b]
    refine Nat.dvd_trans ?_ (gcd_mul_right_dvd_mul_gcd ..)
    rw [h, gcd_mul_right_right d c]; apply Nat.dvd_refl

end Nat

/-! # Basics for the Rational Numbers -/

/--
Rational numbers, implemented as a pair of integers `num / den` such that the
denominator is positive and the numerator and denominator are coprime.
-/
-- `Rat` is not tagged with the `ext` attribute, since this is more often than not undesirable
structure Rat where
  /-- Constructs a rational number from components.
  We rename the constructor to `mk'` to avoid a clash with the smart constructor. -/
  mk' ::
  /-- The numerator of the rational number is an integer. -/
  num : Int
  /-- The denominator of the rational number is a natural number. -/
  den : Nat := 1
  /-- The denominator is nonzero. -/
  den_nz : den ≠ 0 := by decide
  /-- The numerator and denominator are coprime: it is in "reduced form". -/
  reduced : num.natAbs.Coprime den := by decide
  deriving DecidableEq

instance : Inhabited Rat := ⟨{ num := 0 }⟩

instance : ToString Rat where
  toString a := if a.den = 1 then toString a.num else s!"{a.num}/{a.den}"

instance : Repr Rat where
  reprPrec a _ := if a.den = 1 then repr a.num else s!"({a.num} : Rat)/{a.den}"

theorem Rat.den_pos (self : Rat) : 0 < self.den := Nat.pos_of_ne_zero self.den_nz

/--
Auxiliary definition for `Rat.normalize`. Constructs `num / den` as a rational number,
dividing both `num` and `den` by `g` (which is the gcd of the two) if it is not 1.
-/
@[inline] def Rat.maybeNormalize (num : Int) (den g : Nat)
    (dvd_num : ↑g ∣ num) (dvd_den : g ∣ den) (den_nz : den / g ≠ 0)
    (reduced : (num / g).natAbs.Coprime (den / g)) : Rat :=
  if hg : g = 1 then
    { num, den
      den_nz := by simp [hg] at den_nz; exact den_nz
      reduced := by simp [hg, Int.natAbs_natCast] at reduced; exact reduced }
  else { num := num.divExact g dvd_num, den := den.divExact g dvd_den, den_nz, reduced }

theorem Rat.normalize.dvd_num {num : Int} {den g : Nat}
    (e : g = num.natAbs.gcd den) : ↑g ∣ num := by
  rw [e, ← Int.dvd_natAbs, Int.ofNat_dvd]
  exact Nat.gcd_dvd_left num.natAbs den

theorem Rat.normalize.dvd_den {num : Int} {den g : Nat}
    (e : g = num.natAbs.gcd den) : g ∣ den :=
  e ▸ Nat.gcd_dvd_right ..

theorem Rat.normalize.den_nz {num : Int} {den g : Nat} (den_nz : den ≠ 0)
    (e : g = num.natAbs.gcd den) : den / g ≠ 0 :=
  e ▸ Nat.ne_of_gt (Nat.div_gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero den_nz))

theorem Rat.normalize.reduced {num : Int} {den g : Nat} (den_nz : den ≠ 0)
    (e : g = num.natAbs.gcd den) : (num / g).natAbs.Coprime (den / g) :=
  have : Int.natAbs (num / ↑g) = num.natAbs / g := by
    rw [Int.natAbs_ediv_of_dvd (dvd_num e), Int.natAbs_natCast]
  this ▸ e ▸ Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero den_nz))

/--
Construct a normalized `Rat` from a numerator and nonzero denominator.
This is a "smart constructor" that divides the numerator and denominator by
the gcd to ensure that the resulting rational number is normalized.
-/
@[inline] def Rat.normalize (num : Int) (den : Nat := 1) (den_nz : den ≠ 0 := by decide) : Rat :=
  Rat.maybeNormalize num den (num.natAbs.gcd den)
    (normalize.dvd_num rfl) (normalize.dvd_den rfl)
    (normalize.den_nz den_nz rfl) (normalize.reduced den_nz rfl)

/--
Construct a rational number from a numerator and denominator.
This is a "smart constructor" that divides the numerator and denominator by
the gcd to ensure that the resulting rational number is normalized, and returns
zero if `den` is zero.
-/
def mkRat (num : Int) (den : Nat) : Rat :=
  if den_nz : den = 0 then { num := 0 } else Rat.normalize num den den_nz

namespace Rat

/-- Embedding of `Int` in the rational numbers. -/
def ofInt (num : Int) : Rat := { num, reduced := Nat.coprime_one_right _ }

instance : NatCast Rat where
  natCast n := ofInt n
instance : IntCast Rat := ⟨ofInt⟩

instance : OfNat Rat n := ⟨n⟩

/-- Is this rational number integral? -/
@[inline] protected def isInt (a : Rat) : Bool := a.den == 1

/-- Form the quotient `n / d` where `n d : Int`. -/
def divInt : Int → Int → Rat
  | n, .ofNat d => inline (mkRat n d)
  | n, .negSucc d => normalize (-n) d.succ nofun

@[inherit_doc] scoped infixl:70 " /. " => Rat.divInt

/-- Implements "scientific notation" `123.4e-5` for rational numbers. (This definition is
`@[irreducible]` because you don't want to unfold it. Use `Rat.ofScientific_def`,
`Rat.ofScientific_true_def`, or `Rat.ofScientific_false_def` instead.) -/
@[irreducible] protected def ofScientific (m : Nat) (s : Bool) (e : Nat) : Rat :=
  if s then
    Rat.normalize m (10 ^ e) <| Nat.ne_of_gt <| Nat.pow_pos (by decide)
  else
    (m * 10 ^ e : Nat)

/-- Rational number strictly less than relation, as a `Bool`. -/
protected def blt (a b : Rat) : Bool :=
  if a.num < 0 && 0 ≤ b.num then
    true
  else if a.num = 0 then
    0 < b.num
  else if 0 < a.num && b.num ≤ 0 then
    false
  else
    -- `a` and `b` must have the same sign
   a.num * b.den < b.num * a.den

instance : LT Rat := ⟨(·.blt ·)⟩

instance (a b : Rat) : Decidable (a < b) :=
  inferInstanceAs (Decidable (_ = true))

instance : LE Rat := ⟨fun a b => b.blt a = false⟩

instance (a b : Rat) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (_ = false))

/-- Multiplication of rational numbers. (This definition is `@[irreducible]` because you don't
want to unfold it. Use `Rat.mul_def` instead.) -/
@[irreducible] protected def mul (a b : Rat) : Rat :=
  let g1 := Nat.gcd a.num.natAbs b.den
  let g2 := Nat.gcd b.num.natAbs a.den
  { num := a.num.divExact g1 (normalize.dvd_num rfl) * b.num.divExact g2 (normalize.dvd_num rfl)
    den := a.den.divExact g2 (normalize.dvd_den rfl) * b.den.divExact g1 (normalize.dvd_den rfl)
    den_nz := Nat.ne_of_gt <| Nat.mul_pos
      (Nat.div_gcd_pos_of_pos_right _ a.den_pos) (Nat.div_gcd_pos_of_pos_right _ b.den_pos)
    reduced := by
      simp only [Int.divExact_eq_tdiv, Int.natAbs_mul, Int.natAbs_tdiv, Nat.coprime_mul_iff_left]
      refine ⟨Nat.coprime_mul_iff_right.2 ⟨?_, ?_⟩, Nat.coprime_mul_iff_right.2 ⟨?_, ?_⟩⟩
      · exact a.reduced.coprime_div_left (Nat.gcd_dvd_left ..)
          |>.coprime_div_right (Nat.gcd_dvd_right ..)
      · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ b.den_pos)
      · exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right _ a.den_pos)
      · exact b.reduced.coprime_div_left (Nat.gcd_dvd_left ..)
          |>.coprime_div_right (Nat.gcd_dvd_right ..) }

instance : Mul Rat := ⟨Rat.mul⟩

/--
The inverse of a rational number. Note: `inv 0 = 0`. (This definition is `@[irreducible]`
because you don't want to unfold it. Use `Rat.inv_def` instead.)
-/
@[irreducible] protected def inv (a : Rat) : Rat :=
  if h : a.num < 0 then
    { num := -a.den, den := a.num.natAbs
      den_nz := Nat.ne_of_gt (Int.natAbs_pos.2 (Int.ne_of_lt h))
      reduced := Int.natAbs_neg a.den ▸ a.reduced.symm }
  else if h : a.num > 0 then
    { num := a.den, den := a.num.natAbs
      den_nz := Nat.ne_of_gt (Int.natAbs_pos.2 (Int.ne_of_gt h))
      reduced := a.reduced.symm }
  else
    a

/-- Division of rational numbers. Note: `div a 0 = 0`. -/
protected def div : Rat → Rat → Rat := (· * ·.inv)

/-- Division of rational numbers. Note: `div a 0 = 0`.  Written with a separate function `Rat.div`
as a wrapper so that the definition is not unfolded at `.instance` transparency. -/
instance : Div Rat := ⟨Rat.div⟩

theorem add.aux (a b : Rat) {g ad bd} (hg : g = a.den.gcd b.den)
    (had : ad = a.den / g) (hbd : bd = b.den / g) :
    let den := ad * b.den; let num := a.num * bd + b.num * ad
    num.natAbs.gcd g = num.natAbs.gcd den := by
  intro den num
  have ae : ad * g = a.den := had ▸ Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_left ..)
  have be : bd * g = b.den := hbd ▸ Nat.div_mul_cancel (hg ▸ Nat.gcd_dvd_right ..)
  have hden : den = ad * bd * g := by rw [Nat.mul_assoc, be]
  rw [hden, Nat.Coprime.gcd_mul_left_cancel_right]
  have cop : ad.Coprime bd := had ▸ hbd ▸ hg ▸
    Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_left _ a.den_pos)
  have H1 (d : Nat) :
      d.gcd num.natAbs ∣ a.num.natAbs * bd ↔ d.gcd num.natAbs ∣ b.num.natAbs * ad := by
    have := d.gcd_dvd_right num.natAbs
    rw [← Int.ofNat_dvd, Int.dvd_natAbs] at this
    have := Int.dvd_iff_dvd_of_dvd_add this
    rwa [← Int.dvd_natAbs, Int.ofNat_dvd, Int.natAbs_mul,
      ← Int.dvd_natAbs, Int.ofNat_dvd, Int.natAbs_mul] at this
  apply Nat.Coprime.mul
  · have := (H1 ad).2 <| Nat.dvd_trans (Nat.gcd_dvd_left ..) (Nat.dvd_mul_left ..)
    have := (cop.coprime_dvd_left <| Nat.gcd_dvd_left ..).dvd_of_dvd_mul_right this
    exact Nat.eq_one_of_dvd_one <| a.reduced.gcd_eq_one ▸ Nat.dvd_gcd this <|
      Nat.dvd_trans (Nat.gcd_dvd_left ..) (ae ▸ Nat.dvd_mul_right ..)
  · have := (H1 bd).1 <| Nat.dvd_trans (Nat.gcd_dvd_left ..) (Nat.dvd_mul_left ..)
    have := (cop.symm.coprime_dvd_left <| Nat.gcd_dvd_left ..).dvd_of_dvd_mul_right this
    exact Nat.eq_one_of_dvd_one <| b.reduced.gcd_eq_one ▸ Nat.dvd_gcd this <|
      Nat.dvd_trans (Nat.gcd_dvd_left ..) (be ▸ Nat.dvd_mul_right ..)

/--
Addition of rational numbers. (This definition is `@[irreducible]` because you don't want to
unfold it. Use `Rat.add_def` instead.)
-/
@[irreducible] protected def add (a b : Rat) : Rat :=
  let g := a.den.gcd b.den
  if hg : g = 1 then
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos a.den_pos b.den_pos
    have reduced := add.aux a b hg.symm (Nat.div_one _).symm (Nat.div_one _).symm
      |>.symm.trans (Nat.gcd_one_right _)
    { num := a.num * b.den + b.num * a.den, den := a.den * b.den, den_nz, reduced }
  else
    let den := (a.den / g) * b.den
    let num := a.num * ↑(b.den / g) + b.num * ↑(a.den / g)
    let g1  := num.natAbs.gcd g
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos (Nat.div_gcd_pos_of_pos_left _ a.den_pos) b.den_pos
    have e : g1 = num.natAbs.gcd den := add.aux a b rfl rfl rfl
    Rat.maybeNormalize num den g1 (normalize.dvd_num e) (normalize.dvd_den e)
      (normalize.den_nz den_nz e) (normalize.reduced den_nz e)

instance : Add Rat := ⟨Rat.add⟩

/-- Negation of rational numbers. -/
protected def neg (a : Rat) : Rat :=
  { a with num := -a.num, reduced := by rw [Int.natAbs_neg]; exact a.reduced }

instance : Neg Rat := ⟨Rat.neg⟩

theorem sub.aux (a b : Rat) {g ad bd} (hg : g = a.den.gcd b.den)
    (had : ad = a.den / g) (hbd : bd = b.den / g) :
    let den := ad * b.den; let num := a.num * bd - b.num * ad
    num.natAbs.gcd g = num.natAbs.gcd den := by
  have := add.aux a (-b) hg had hbd
  simp only [show (-b).num = -b.num from rfl, Int.neg_mul] at this
  exact this

/-- Subtraction of rational numbers. (This definition is `@[irreducible]` because you don't want to
unfold it. Use `Rat.sub_def` instead.)
-/
@[irreducible] protected def sub (a b : Rat) : Rat :=
  let g := a.den.gcd b.den
  if hg : g = 1 then
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos a.den_pos b.den_pos
    have reduced := sub.aux a b hg.symm (Nat.div_one _).symm (Nat.div_one _).symm
      |>.symm.trans (Nat.gcd_one_right _)
    { num := a.num * b.den - b.num * a.den, den := a.den * b.den, den_nz, reduced }
  else
    let den := (a.den / g) * b.den
    let num := a.num * ↑(b.den / g) - b.num * ↑(a.den / g)
    let g1  := num.natAbs.gcd g
    have den_nz := Nat.ne_of_gt <| Nat.mul_pos (Nat.div_gcd_pos_of_pos_left _ a.den_pos) b.den_pos
    have e : g1 = num.natAbs.gcd den := sub.aux a b rfl rfl rfl
    Rat.maybeNormalize num den g1 (normalize.dvd_num e) (normalize.dvd_den e)
      (normalize.den_nz den_nz e) (normalize.reduced den_nz e)

instance : Sub Rat := ⟨Rat.sub⟩

/-- The floor of a rational number `a` is the largest integer less than or equal to `a`. -/
protected def floor (a : Rat) : Int :=
  if a.den = 1 then
    a.num
  else
    a.num / a.den

/-- The ceiling of a rational number `a` is the smallest integer greater than or equal to `a`. -/
protected def ceil (a : Rat) : Int :=
  if a.den = 1 then
    a.num
  else
    a.num / a.den + 1

end Rat

-- Source: Batteries/Data/Rat/Lemmas.lean

/-! # Additional lemmas about the Rational Numbers -/

namespace Rat

theorem ext : {p q : Rat} → p.num = q.num → p.den = q.den → p = q
  | ⟨_,_,_,_⟩, ⟨_,_,_,_⟩, rfl, rfl => rfl

@[simp] theorem mk_den_one {r : Int} :
    ⟨r, 1, Nat.one_ne_zero, (Nat.coprime_one_right _)⟩ = (r : Rat) := rfl

@[simp] theorem zero_num : (0 : Rat).num = 0 := rfl
@[simp] theorem zero_den : (0 : Rat).den = 1 := rfl
@[simp] theorem one_num : (1 : Rat).num = 1 := rfl
@[simp] theorem one_den : (1 : Rat).den = 1 := rfl

@[simp] theorem maybeNormalize_eq {num den g} (dvd_num dvd_den den_nz reduced) :
    maybeNormalize num den g dvd_num dvd_den den_nz reduced =
    { num := num.divExact g dvd_num, den := den / g, den_nz, reduced } := by
  unfold maybeNormalize; split
  · subst g; simp
  · rfl

theorem normalize_eq {num den} (den_nz) : normalize num den den_nz =
    { num := num / num.natAbs.gcd den
      den := den / num.natAbs.gcd den
      den_nz := normalize.den_nz den_nz rfl
      reduced := normalize.reduced den_nz rfl } := by
  simp only [normalize, maybeNormalize_eq, Int.divExact_eq_ediv]

@[simp] theorem normalize_zero (nz) : normalize 0 d nz = 0 := by
  simp [normalize, Int.zero_tdiv, Int.natAbs_zero, Nat.div_self (Nat.pos_of_ne_zero nz)]; rfl

theorem mk_eq_normalize (num den nz c) : ⟨num, den, nz, c⟩ = normalize num den nz := by
  simp [normalize_eq, c.gcd_eq_one]

theorem normalize_self (r : Rat) : normalize r.num r.den r.den_nz = r := (mk_eq_normalize ..).symm

theorem normalize_mul_left {a : Nat} (d0 : d ≠ 0) (a0 : a ≠ 0) :
    normalize (↑a * n) (a * d) (Nat.mul_ne_zero a0 d0) = normalize n d d0 := by
  simp [normalize_eq, mk'.injEq, Int.natAbs_mul, Nat.gcd_mul_left,
    Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero a0), Int.natCast_mul,
    Int.mul_ediv_mul_of_pos _ _ (Int.ofNat_pos.2 <| Nat.pos_of_ne_zero a0)]

theorem normalize_mul_right {a : Nat} (d0 : d ≠ 0) (a0 : a ≠ 0) :
    normalize (n * a) (d * a) (Nat.mul_ne_zero d0 a0) = normalize n d d0 := by
  rw [← normalize_mul_left (d0 := d0) a0]
  congr 1
  · apply Int.mul_comm
  · apply Nat.mul_comm

theorem normalize_eq_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    normalize n₁ d₁ z₁ = normalize n₂ d₂ z₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  constructor <;> intro h
  · simp only [normalize_eq, mk'.injEq] at h
    have hn₁ := Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left n₁.natAbs d₁
    have hn₂ := Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left n₂.natAbs d₂
    have hd₁ := Int.ofNat_dvd.2 <| Nat.gcd_dvd_right n₁.natAbs d₁
    have hd₂ := Int.ofNat_dvd.2 <| Nat.gcd_dvd_right n₂.natAbs d₂
    rw [← Int.ediv_mul_cancel (Int.dvd_trans hd₂ (Int.dvd_mul_left ..)),
      Int.mul_ediv_assoc _ hd₂, ← Int.natCast_ediv, ← h.2, Int.natCast_ediv,
      ← Int.mul_ediv_assoc _ hd₁, Int.mul_ediv_assoc' _ hn₁,
      Int.mul_right_comm, h.1, Int.ediv_mul_cancel hn₂]
  · rw [← normalize_mul_right _ z₂, ← normalize_mul_left z₂ z₁, Int.mul_comm d₁, h]

theorem maybeNormalize_eq_normalize {num : Int} {den g : Nat} (dvd_num dvd_den den_nz reduced)
    (hn : ↑g ∣ num) (hd : g ∣ den) :
    maybeNormalize num den g dvd_num dvd_den den_nz reduced =
      normalize num den (mt (by simp [·]) den_nz) := by
  simp only [maybeNormalize_eq, mk_eq_normalize, Int.divExact_eq_ediv]
  have : g ≠ 0 := mt (by simp [·]) den_nz
  rw [← normalize_mul_right _ this, Int.ediv_mul_cancel hn]
  congr 1; exact Nat.div_mul_cancel hd

@[simp] theorem normalize_eq_zero (d0 : d ≠ 0) : normalize n d d0 = 0 ↔ n = 0 := by
  have' := normalize_eq_iff d0 Nat.one_ne_zero
  rw [normalize_zero (d := 1)] at this; rw [this]; simp

theorem normalize_num_den' (num den nz) : ∃ d : Nat, d ≠ 0 ∧
    num = (normalize num den nz).num * d ∧ den = (normalize num den nz).den * d := by
  refine ⟨num.natAbs.gcd den, Nat.gcd_ne_zero_right nz, ?_⟩
  simp [normalize_eq, Int.ediv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..),
    Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]

theorem normalize_num_den (h : normalize n d z = ⟨n', d', z', c⟩) :
    ∃ m : Nat, m ≠ 0 ∧ n = n' * m ∧ d = d' * m := by
  have := normalize_num_den' n d z; rwa [h] at this

theorem normalize_eq_mkRat {num den} (den_nz) : normalize num den den_nz = mkRat num den := by
  simp [mkRat, den_nz]

theorem mkRat_num_den (z : d ≠ 0) (h : mkRat n d = ⟨n', d', z', c⟩) :
    ∃ m : Nat, m ≠ 0 ∧ n = n' * m ∧ d = d' * m :=
  normalize_num_den ((normalize_eq_mkRat z).symm ▸ h)

theorem mkRat_def (n d) : mkRat n d = if d0 : d = 0 then 0 else normalize n d d0 := rfl

theorem mkRat_self (a : Rat) : mkRat a.num a.den = a := by
  rw [← normalize_eq_mkRat a.den_nz, normalize_self]

theorem mk_eq_mkRat (num den nz c) : ⟨num, den, nz, c⟩ = mkRat num den := by
  simp [mk_eq_normalize, normalize_eq_mkRat]

@[simp] theorem zero_mkRat (n) : mkRat 0 n = 0 := by simp [mkRat_def]

@[simp] theorem mkRat_zero (n) : mkRat n 0 = 0 := by simp [mkRat_def]

theorem mkRat_eq_zero (d0 : d ≠ 0) : mkRat n d = 0 ↔ n = 0 := by simp [mkRat_def, d0]

theorem mkRat_ne_zero (d0 : d ≠ 0) : mkRat n d ≠ 0 ↔ n ≠ 0 := not_congr (mkRat_eq_zero d0)

theorem mkRat_mul_left {a : Nat} (a0 : a ≠ 0) : mkRat (↑a * n) (a * d) = mkRat n d := by
  if d0 : d = 0 then simp [d0] else
  rw [← normalize_eq_mkRat d0, ← normalize_mul_left d0 a0, normalize_eq_mkRat]

theorem mkRat_mul_right {a : Nat} (a0 : a ≠ 0) : mkRat (n * a) (d * a) = mkRat n d := by
  rw [← mkRat_mul_left (d := d) a0]
  congr 1
  · apply Int.mul_comm
  · apply Nat.mul_comm

theorem mkRat_eq_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    mkRat n₁ d₁ = mkRat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_eq_iff]

@[simp] theorem divInt_ofNat (num den) : num /. (den : Nat) = mkRat num den := by
  simp [divInt, normalize_eq_mkRat]

theorem mk_eq_divInt (num den nz c) : ⟨num, den, nz, c⟩ = num /. (den : Nat) := by
  simp [mk_eq_mkRat]

theorem divInt_self (a : Rat) : a.num /. a.den = a := by rw [divInt_ofNat, mkRat_self]

@[simp] theorem zero_divInt (n) : 0 /. n = 0 := by cases n <;> simp [divInt]

@[simp] theorem divInt_zero (n) : n /. 0 = 0 := mkRat_zero n

theorem neg_divInt_neg (num den) : -num /. -den = num /. den := by
  match den with
  | Nat.succ n =>
    simp only [divInt, Int.neg_ofNat_succ]
    simp [normalize_eq_mkRat, Int.neg_neg]
  | 0 => rfl
  | Int.negSucc n =>
    simp only [divInt, Int.neg_negSucc]
    simp [normalize_eq_mkRat, Int.neg_neg]

theorem divInt_neg' (num den) : num /. -den = -num /. den := by rw [← neg_divInt_neg, Int.neg_neg]

theorem divInt_eq_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ = n₂ /. d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [divInt_neg', Int.ofNat_eq_zero, Int.neg_eq_zero,
    mkRat_eq_iff, Int.neg_mul, Int.mul_neg, Int.eq_neg_comm, eq_comm]

theorem divInt_mul_left {a : Int} (a0 : a ≠ 0) : (a * n) /. (a * d) = n /. d := by
  if d0 : d = 0 then simp [d0] else
  simp [divInt_eq_iff (Int.mul_ne_zero a0 d0) d0, Int.mul_assoc, Int.mul_left_comm]

theorem divInt_mul_right {a : Int} (a0 : a ≠ 0) : (n * a) /. (d * a) = n /. d := by
  simp [← divInt_mul_left (d := d) a0, Int.mul_comm]

theorem divInt_num_den (z : d ≠ 0) (h : n /. d = ⟨n', d', z', c⟩) :
    ∃ m, m ≠ 0 ∧ n = n' * m ∧ d = d' * m := by
  rcases Int.eq_nat_or_neg d with ⟨_, rfl | rfl⟩ <;>
    simp_all [divInt_neg', Int.ofNat_eq_zero, Int.neg_eq_zero]
  · have ⟨m, h₁, h₂⟩ := mkRat_num_den z h; exists m
    simp [Int.ofNat_eq_zero, Int.natCast_mul, h₁, h₂]
  · have ⟨m, h₁, h₂⟩ := mkRat_num_den z h; exists -m
    rw [← Int.neg_inj, Int.neg_neg] at h₂
    simp [Int.ofNat_eq_zero, Int.natCast_mul, h₁, h₂, Int.mul_neg, Int.neg_eq_zero]

@[simp] theorem ofInt_ofNat : ofInt (OfNat.ofNat n) = OfNat.ofNat n := rfl

@[simp] theorem ofInt_num : (ofInt n : Rat).num = n := rfl
@[simp] theorem ofInt_den : (ofInt n : Rat).den = 1 := rfl

@[simp] theorem ofNat_num : (OfNat.ofNat n : Rat).num = OfNat.ofNat n := rfl
@[simp] theorem ofNat_den : (OfNat.ofNat n : Rat).den = 1 := rfl

theorem add_def (a b : Rat) :
    a + b = normalize (a.num * b.den + b.num * a.den) (a.den * b.den)
      (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.add .. = _; delta Rat.add; dsimp only; split
  · exact (normalize_self _).symm
  · have : a.den.gcd b.den ≠ 0 := Nat.gcd_ne_zero_left a.den_nz
    rw [maybeNormalize_eq_normalize _ _ _ _
        (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)
        (Nat.dvd_trans (Nat.gcd_dvd_right ..) <|
         Nat.dvd_trans (Nat.gcd_dvd_right ..) (Nat.dvd_mul_left ..)),
      ← normalize_mul_right _ this]; congr 1
    · simp only [Int.add_mul, Int.mul_assoc, Int.ofNat_mul_ofNat,
        Nat.div_mul_cancel (Nat.gcd_dvd_left ..), Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]
    · rw [Nat.mul_right_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]

theorem add_def' (a b : Rat) : a + b = mkRat (a.num * b.den + b.num * a.den) (a.den * b.den) := by
  rw [add_def, normalize_eq_mkRat]

theorem normalize_add_normalize (n₁ n₂) {d₁ d₂} (z₁ z₂) :
    normalize n₁ d₁ z₁ + normalize n₂ d₂ z₂ =
    normalize (n₁ * d₂ + n₂ * d₁) (d₁ * d₂) (Nat.mul_ne_zero z₁ z₂) := by
  cases e₁ : normalize n₁ d₁ z₁; rcases normalize_num_den e₁ with ⟨g₁, zg₁, rfl, rfl⟩
  cases e₂ : normalize n₂ d₂ z₂; rcases normalize_num_den e₂ with ⟨g₂, zg₂, rfl, rfl⟩
  simp only [add_def]; rw [← normalize_mul_right _ (Nat.mul_ne_zero zg₁ zg₂)]; congr 1
  · rw [Int.add_mul]; simp [Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · simp [Nat.mul_left_comm, Nat.mul_comm]

theorem mkRat_add_mkRat (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    mkRat n₁ d₁ + mkRat n₂ d₂ = mkRat (n₁ * d₂ + n₂ * d₁) (d₁ * d₂) := by
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_add_normalize, normalize_eq_mkRat]

theorem divInt_add_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ + n₂ /. d₂ = (n₁ * d₂ + n₂ * d₁) /. (d₁ * d₂) := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [← Int.natCast_mul, Int.ofNat_eq_zero, Int.neg_eq_zero, divInt_neg', Int.mul_neg,
    Int.neg_add, Int.neg_mul, mkRat_add_mkRat]

@[simp] theorem neg_num (a : Rat) : (-a).num = -a.num := rfl
@[simp] theorem neg_den (a : Rat) : (-a).den = a.den := rfl

theorem neg_normalize (n d z) : -normalize n d z = normalize (-n) d z := by
  simp only [normalize, maybeNormalize_eq, Int.divExact_eq_tdiv, Int.natAbs_neg, Int.neg_tdiv]
  rfl

theorem neg_mkRat (n d) : -mkRat n d = mkRat (-n) d := by
  if z : d = 0 then simp [z]; rfl else simp [← normalize_eq_mkRat z, neg_normalize]

theorem neg_divInt (n d) : -(n /. d) = -n /. d := by
  rcases Int.eq_nat_or_neg d with ⟨_, rfl | rfl⟩ <;> simp [divInt_neg', neg_mkRat]

theorem sub_def (a b : Rat) :
    a - b = normalize (a.num * b.den - b.num * a.den) (a.den * b.den)
      (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.sub .. = _; delta Rat.sub; dsimp only; split
  · exact (normalize_self _).symm
  · have : a.den.gcd b.den ≠ 0 := Nat.gcd_ne_zero_left a.den_nz
    rw [maybeNormalize_eq_normalize _ _ _ _
        (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)
        (Nat.dvd_trans (Nat.gcd_dvd_right ..) <|
         Nat.dvd_trans (Nat.gcd_dvd_right ..) (Nat.dvd_mul_left ..)),
      ← normalize_mul_right _ this]; congr 1
    · simp only [Int.sub_mul, Int.mul_assoc, ← Int.natCast_mul,
        Nat.div_mul_cancel (Nat.gcd_dvd_left ..), Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]
    · rw [Nat.mul_right_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]

theorem sub_def' (a b : Rat) : a - b = mkRat (a.num * b.den - b.num * a.den) (a.den * b.den) := by
  rw [sub_def, normalize_eq_mkRat]

protected theorem sub_eq_add_neg (a b : Rat) : a - b = a + -b := by
  simp [add_def, sub_def, Int.neg_mul, Int.sub_eq_add_neg]

theorem divInt_sub_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ - n₂ /. d₂ = (n₁ * d₂ - n₂ * d₁) /. (d₁ * d₂) := by
  simp only [Rat.sub_eq_add_neg, neg_divInt,
    divInt_add_divInt _ _ z₁ z₂, Int.neg_mul, Int.sub_eq_add_neg]

theorem mul_def (a b : Rat) :
    a * b = normalize (a.num * b.num) (a.den * b.den) (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.mul .. = _; delta Rat.mul; dsimp only
  have H1 : a.num.natAbs.gcd b.den ≠ 0 := Nat.gcd_ne_zero_right b.den_nz
  have H2 : b.num.natAbs.gcd a.den ≠ 0 := Nat.gcd_ne_zero_right a.den_nz
  simp only [Int.divExact_eq_tdiv, Nat.divExact_eq_div]
  rw [mk_eq_normalize, ← normalize_mul_right _ (Nat.mul_ne_zero H1 H2)]; congr 1
  · rw [Int.natCast_mul, ← Int.mul_assoc, Int.mul_right_comm (Int.tdiv ..),
      Int.tdiv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..), Int.mul_assoc,
      Int.tdiv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)]
  · rw [← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_right_comm (_/_),
      Nat.div_mul_cancel (Nat.gcd_dvd_right ..), Nat.mul_assoc,
      Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]

protected theorem mul_comm (a b : Rat) : a * b = b * a := by
  simp [mul_def, normalize_eq_mkRat, Int.mul_comm, Nat.mul_comm]

@[simp] protected theorem zero_mul (a : Rat) : 0 * a = 0 := by simp [mul_def]
@[simp] protected theorem mul_zero (a : Rat) : a * 0 = 0 := by simp [mul_def]
@[simp] protected theorem one_mul (a : Rat) : 1 * a = a := by simp [mul_def, normalize_self]
@[simp] protected theorem mul_one (a : Rat) : a * 1 = a := by simp [mul_def, normalize_self]

theorem normalize_mul_normalize (n₁ n₂) {d₁ d₂} (z₁ z₂) :
    normalize n₁ d₁ z₁ * normalize n₂ d₂ z₂ =
    normalize (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero z₁ z₂) := by
  cases e₁ : normalize n₁ d₁ z₁; rcases normalize_num_den e₁ with ⟨g₁, zg₁, rfl, rfl⟩
  cases e₂ : normalize n₂ d₂ z₂; rcases normalize_num_den e₂ with ⟨g₂, zg₂, rfl, rfl⟩
  simp only [mul_def]; rw [← normalize_mul_right _ (Nat.mul_ne_zero zg₁ zg₂)]; congr 1
  · simp [Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm]
  · simp [Nat.mul_left_comm, Nat.mul_comm]

theorem mkRat_mul_mkRat (n₁ n₂ : Int) (d₁ d₂) :
    mkRat n₁ d₁ * mkRat n₂ d₂ = mkRat (n₁ * n₂) (d₁ * d₂) := by
  if z₁ : d₁ = 0 then simp [z₁] else if z₂ : d₂ = 0 then simp [z₂] else
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_mul_normalize, normalize_eq_mkRat]

theorem divInt_mul_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    (n₁ /. d₁) * (n₂ /. d₂) = (n₁ * n₂) /. (d₁ * d₂) := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [← Int.natCast_mul, divInt_neg', Int.mul_neg, Int.neg_mul, mkRat_mul_mkRat]

theorem inv_def (a : Rat) : a.inv = a.den /. a.num := by
  unfold Rat.inv; split
  · next h => rw [mk_eq_divInt, ← Int.natAbs_neg,
      Int.natAbs_of_nonneg (Int.le_of_lt <| Int.neg_pos_of_neg h), neg_divInt_neg]
  split
  · next h => rw [mk_eq_divInt, Int.natAbs_of_nonneg (Int.le_of_lt h)]
  · next h₁ h₂ =>
    apply (divInt_self _).symm.trans
    simp [Int.le_antisymm (Int.not_lt.1 h₂) (Int.not_lt.1 h₁)]

@[simp] protected theorem inv_zero : (0 : Rat).inv = 0 := by unfold Rat.inv; rfl

@[simp] theorem inv_divInt (n d : Int) : (n /. d).inv = d /. n := by
  if z : d = 0 then simp [z] else
  cases e : n /. d; rcases divInt_num_den z e with ⟨g, zg, rfl, rfl⟩
  simp [inv_def, divInt_mul_right zg]

theorem div_def (a b : Rat) : a / b = a * b.inv := rfl

theorem ofScientific_true_def : Rat.ofScientific m true e = mkRat m (10 ^ e) := by
  unfold Rat.ofScientific; rw [normalize_eq_mkRat]; rfl

theorem ofScientific_false_def : Rat.ofScientific m false e = (m * 10 ^ e : Nat) := by
  unfold Rat.ofScientific; rfl

theorem ofScientific_def : Rat.ofScientific m s e =
    if s then mkRat m (10 ^ e) else (m * 10 ^ e : Nat) := by
  cases s; exact ofScientific_false_def; exact ofScientific_true_def

@[simp] theorem intCast_den (a : Int) : (a : Rat).den = 1 := rfl

@[simp] theorem intCast_num (a : Int) : (a : Rat).num = a := rfl

/-!
The following lemmas are later subsumed by e.g. `Int.cast_add` and `Int.cast_mul` in Mathlib
but it is convenient to have these earlier, for users who only need `Int` and `Rat`.
-/

@[simp, norm_cast] theorem intCast_inj {a b : Int} : (a : Rat) = (b : Rat) ↔ a = b := by
  constructor
  · rintro ⟨⟩; rfl
  · simp_all

theorem intCast_zero : ((0 : Int) : Rat) = (0 : Rat) := rfl

theorem intCast_one : ((1 : Int) : Rat) = (1 : Rat) := rfl

@[simp, norm_cast] theorem intCast_add (a b : Int) :
    ((a + b : Int) : Rat) = (a : Rat) + (b : Rat) := by
  rw [add_def]
  simp [normalize_eq]

@[simp, norm_cast] theorem intCast_neg (a : Int) : ((-a : Int) : Rat) = -(a : Rat) := rfl

@[simp, norm_cast] theorem intCast_sub (a b : Int) :
    ((a - b : Int) : Rat) = (a : Rat) - (b : Rat) := by
  rw [sub_def]
  simp [normalize_eq]

@[simp, norm_cast] theorem intCast_mul (a b : Int) :
    ((a * b : Int) : Rat) = (a : Rat) * (b : Rat) := by
  rw [mul_def]
  simp [normalize_eq]

variable (x y a b c q : Rat)

protected def abs (x : Rat) := if x < 0 then -x else x

protected def pow (m : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => Rat.pow m n * m

instance : NatPow Rat where
  pow := Rat.pow

def ceil' (r : Rat) := -((-r).floor)

theorem num_divInt_den (q : Rat) : q.num /. q.den = q :=
  divInt_self _

theorem mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : Rat) = n /. d :=
  (num_divInt_den _).symm

theorem divInt_num (q : Rat) : (q.num /. q.den).num = q.num := by
  simp [mkRat, q.den_nz, normalize, Rat.reduced]

theorem divInt_num'
  {n : Int} {d : Nat}
  (nz_d : d ≠ 0 := by omega)
  (reduced : n.natAbs.Coprime d := by assumption)
: (n /. d).num = n := by
  simp [mkRat, nz_d, normalize, reduced]

theorem divInt_den (q : Rat) : (q.num /. q.den).den = q.den := by
  simp [mkRat, q.den_nz, normalize, Rat.reduced]

theorem divInt_den'
  {n : Int} {d : Nat}
  (nz_d : d ≠ 0 := by omega)
  (reduced : n.natAbs.Coprime d := by assumption)
: (n /. d).den = d := by
  simp [mkRat, nz_d, normalize, reduced]

@[elab_as_elim]
def numDenCasesOn.{u} {C : Rat → Sort u}
: ∀ (a : Rat) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
| ⟨n, d, h, c⟩, H => by rw [mk'_eq_divInt]; exact H n d (Nat.pos_of_ne_zero h) c

@[elab_as_elim]
def numDenCasesOn'.{u} {C : Rat → Sort u} (a : Rat)
  (H : ∀ (n : Int) (d : Nat), d ≠ 0 → C (n /. d))
: C a :=
  numDenCasesOn a fun n d h _ => H n d (Nat.pos_iff_ne_zero.mp h)

@[elab_as_elim]
def numDenCasesOn''.{u} {C : Rat → Sort u} (a : Rat)
  (H : ∀ (n : Int) (d : Nat) (nz red), C (mk' n d nz red))
: C a :=
  numDenCasesOn a fun n d h h' ↦ by
    let h_pos := Nat.pos_iff_ne_zero.mp h
    rw [← mk_eq_divInt _ _ h_pos h']
    exact H n d h_pos _

theorem normalize_eq_mk'
  (n : Int) (d : Nat) (h : d ≠ 0) (c : Nat.gcd (Int.natAbs n) d = 1)
: normalize n d h = mk' n d h c :=
  (mk_eq_normalize ..).symm

protected theorem normalize_den_ne_zero
: ∀ {d : Int} {n : Nat}, (h : n ≠ 0) → (normalize d n h).den ≠ 0 := by
  intro d n nz
  simp only [Rat.normalize_eq, ne_eq]
  intro h
  apply nz
  rw [← Nat.zero_mul (d.natAbs.gcd n)]
  apply Nat.div_eq_iff_eq_mul_left _ _ |>.mp
  · assumption
  · exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero nz)
  · exact Nat.gcd_dvd_right _ _

protected theorem eq_mkRat : ∀ a : Rat, a = mkRat a.num a.den := fun a => by
  simp [Rat.mkRat_def, a.den_nz, Rat.normalize_eq, a.reduced]

@[simp]
theorem mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by
  congr
  apply Nat.coprime_zero_left d |>.mp w

theorem eq_iff_mul_eq_mul {p q : Rat} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← num_divInt_den p, ← num_divInt_den q]
  apply Rat.divInt_eq_iff <;>
    · rw [← Int.natCast_zero, Ne, Int.ofNat_inj]
      apply den_nz

protected theorem not_le {q q' : Rat} : ¬q ≤ q' ↔ q' < q := by
  exact (Bool.not_eq_false _).to_iff

protected theorem not_lt {q q' : Rat} : ¬q < q' ↔ q' ≤ q := by
  rw [not_congr (Rat.not_le (q := q') (q' := q)) |>.symm]
  simp only [Decidable.not_not]

protected theorem lt_iff_blt {x y : Rat} : x < y ↔ x.blt y := by
  simp only [LT.lt]

protected theorem le_iff_blt {x y : Rat} : x ≤ y ↔ ¬ y.blt x := by
  simp [LE.le]

protected theorem lt_asymm {x y : Rat} : x < y → ¬ y < x := by
  simp [Rat.lt_iff_blt, Rat.blt]
  intro h
  cases h with
  | inl h =>
    simp only [h, implies_true, Int.not_lt_of_lt_rev h.1, or_false, if_false_left, not_and,
      Int.not_lt, true_and]
    intro nz_ynum ynum_neg
    have z_ynum : y.num = 0 := Int.le_antisymm ynum_neg h.right
    contradiction
  | inr h =>
    split at h
    case isTrue xnum_0 =>
      simp only [Int.not_lt_of_lt_rev h, xnum_0, Int.lt_irrefl, imp_self, or_false, Int.zero_mul,
        if_false_left, not_and, Int.not_lt, true_and]
      intro nz_ynum ynum_neg
      have z_ynum : y.num = 0 := Int.le_antisymm ynum_neg (Int.le_of_lt h)
      contradiction
    case inr xnum_ne_0 =>
      let ⟨h, h'⟩ := h
      simp only [Int.not_lt_of_lt_rev h', and_false, if_false_right, not_and, Int.not_lt]
      cases h
      case inl h =>
        simp only [h, implies_true, and_true]
        intro _
        apply Int.lt_of_le_of_ne h xnum_ne_0
      case inr h =>
        constructor <;> intros <;> simp_all [Int.lt_asymm]

protected theorem add_comm : a + b = b + a := by
  simp [add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]

@[simp]
protected theorem add_zero : ∀ a : Rat, a + 0 = a
| ⟨num, den, _h, _h'⟩ => by
  simp [Rat.add_def]
  simp only [Rat.normalize_eq_mkRat, Rat.mk_eq_normalize]

@[simp]
protected theorem zero_add : 0 + a = a :=
  Rat.add_comm a 0 ▸ Rat.add_zero a

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
  numDenCasesOn' b fun n₂ d₂ h₂ =>
  numDenCasesOn' c fun n₃ d₃ h₃ => by
    simp only [
      ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂,
      Rat.divInt_add_divInt, Int.mul_eq_zero, or_self, h₃
    ]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    congr 2
    ac_rfl

protected theorem mul_eq_zero_iff : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · simp only [Rat.mul_def, Rat.normalize_eq_zero]
    intro h
    cases Int.mul_eq_zero.mp h
    · apply Or.inl
      rw [Rat.eq_mkRat a, Rat.mkRat_eq_zero]
      assumption
      exact a.den_nz
    · apply Or.inr
      rw [Rat.eq_mkRat b, Rat.mkRat_eq_zero]
      assumption
      exact b.den_nz
  · intro
    | .inl h => simp only [h, Rat.zero_mul]
    | .inr h => simp only [h, Rat.mul_zero]

protected theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  simp only [not_congr (Rat.mul_eq_zero_iff a b), not_or, ne_eq]

@[simp]
theorem neg_neg : - -q = q := by
  rw [← Rat.mkRat_self q]
  simp [Rat.neg_mkRat]

@[simp]
theorem num_eq_zero : q.num = 0 ↔ q = 0 := by
  induction q
  constructor
  · rintro rfl
    exact mk'_zero _ _ _
  · exact congrArg num

theorem num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := not_congr (num_eq_zero q)

@[simp]
theorem num_nonneg : 0 ≤ q.num ↔ 0 ≤ q := by
  simp [Int.le_iff_lt_or_eq, instLE, Rat.blt, Int.not_lt]
  omega

theorem nonneg_iff_sub_nonpos : 0 ≤ q ↔ -q ≤ 0 := by
  rw [← num_nonneg]
  conv => rhs; simp [LE.le, Rat.blt]
  rfl

theorem nonneg_sub_iff_nonpos : 0 ≤ -q ↔ q ≤ 0 := by
  simp [nonneg_iff_sub_nonpos, Rat.neg_neg]

@[simp]
theorem num_nonpos : q.num ≤ 0 ↔ q ≤ 0 := by
  conv => lhs ; rw [← Int.neg_nonneg]
  simp only [Rat.neg_num q ▸ @num_nonneg (-q)]
  conv => rhs ; rw [← nonneg_sub_iff_nonpos]

theorem not_nonpos : ¬ q ≤ 0 ↔ 0 < q := by
  simp [Rat.lt_iff_blt, Rat.blt]
  rw [← num_nonpos]
  exact Int.not_le

@[simp]
theorem num_pos : 0 < q.num ↔ 0 < q := by
  let tmp := not_congr (num_nonpos (q := q))
  rw [Int.not_le] at tmp
  simp [tmp, Rat.not_nonpos]

theorem pos_iff_neg_nonpos : 0 < q ↔ -q < 0 := by
  rw [← num_pos]
  conv => rhs ; simp [Rat.lt_iff_blt] ; unfold Rat.blt ; simp
  constructor <;> intro h
  · apply Or.inl
    exact (num_pos q).mp h
  · let h : 0 < q := by
      cases h
      case inl h => exact h
      case inr h => exact h.2.2
    apply (num_pos q).mpr h

@[simp]
theorem num_neg : q.num < 0 ↔ q < 0 := by
  let tmp := @num_pos (-q)
  simp [Rat.neg_num q, Int.lt_neg_of_lt_neg] at tmp
  rw [tmp]
  apply Rat.neg_neg q ▸ Rat.pos_iff_neg_nonpos (q := -q)

@[simp]
theorem num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num :=
  rfl

@[simp]
protected theorem le_refl : x ≤ x := by
  simp [Rat.le_iff_blt, Rat.blt]
  if h : x = 0 then
    simp [h]
    rw [← Rat.num_neg, Rat.zero_num]
    exact Int.lt_irrefl 0
  else
    simp [h]
    rw [← Rat.num_neg, ← Rat.num_pos]
    omega

protected theorem lt_irrefl : ¬ x < x := by
  simp [Rat.not_lt, Rat.le_refl]

protected theorem le_of_lt : x < y → x ≤ y := by
  intro h_lt
  apply Decidable.byContradiction
  intro h
  let _ := Rat.not_le.mp h
  let _ := Rat.lt_asymm h_lt
  contradiction

protected theorem ne_of_lt : x < y → x ≠ y := by
  intro h_lt h_eq
  exact Rat.lt_irrefl x (h_eq ▸ h_lt)

protected theorem nonneg_total : 0 ≤ x ∨ 0 ≤ -x := by
  rw [← num_nonneg (q := -x), ← num_nonneg (q := x)]
  rw [Rat.neg_num, Int.neg_nonneg]
  exact Int.le_total _ _

protected theorem nonneg_antisymm : 0 ≤ x → 0 ≤ -x → x = 0 := by
  rw [← Rat.num_eq_zero, ← Rat.num_nonneg, ← Rat.num_nonneg, Rat.num_neg_eq_neg_num]
  omega

protected theorem neg_sub : -(x - y) = y - x := by
  cases x with | mk' nx dx _ _ =>
  cases y with | mk' ny dy _ _ =>
  simp only [Neg.neg, Rat.sub_eq_add_neg]
  simp only [Rat.neg, Int.neg_mul, add_def, normalize_eq, mk'.injEq]
  rw [Nat.mul_comm dx dy]
  constructor
  · rw [← Int.neg_ediv_of_dvd]
    rw [← Int.sub_eq_add_neg, Int.neg_sub]
    rw [← Int.sub_eq_add_neg]
    rw [← Int.natAbs_neg, Int.neg_sub]
    · conv => lhs ; arg 1 ; arg 2 ; rw [← Int.natAbs_natCast (dy * dx)]
      exact Int.natAbs_gcd_dvd' (nx * ↑dy + -(ny * ↑dx)) (↑(dy * dx) : Int).natAbs
  · rw [← Int.sub_eq_add_neg]
    rw [← Int.sub_eq_add_neg]
    rw [← Int.natAbs_neg, Int.neg_sub]

@[simp]
protected theorem sub_self : x - x = 0 :=
  numDenCasesOn' x fun nx dx h_dx => by
    rw [Rat.divInt_sub_divInt _ _ (Int.natCast_ne_zero.mpr h_dx) (Int.natCast_ne_zero.mpr h_dx)]
    simp

protected theorem add_neg_self : x + -x = 0 :=
  Rat.sub_eq_add_neg x x ▸ Rat.sub_self x

protected theorem eq_neg_of_add_eq_zero_left : x + y = 0 → x = - y :=
  numDenCasesOn'' x fun nx dx h_dx h_dx_red =>
  numDenCasesOn'' y fun ny dy h_dy h_dy_red => by
    simp only [Rat.neg_divInt, Rat.add_def, Neg.neg]
    simp only [Rat.neg, normalize_eq_zero]
    simp only [eq_iff_mul_eq_mul, ← Int.neg_mul_eq_neg_mul]
    intro h
    apply Int.eq_neg_of_eq_neg
    exact Int.neg_eq_of_add_eq_zero h |>.symm

protected theorem le_iff_sub_nonneg (x y : Rat) : x ≤ y ↔ 0 ≤ y - x :=
  numDenCasesOn'' x fun nx dx h_dx _ =>
  numDenCasesOn'' y fun ny dy h_dy _ => by
    let dy_dx_nz : dy * dx ≠ 0 :=
      Nat.mul_ne_zero h_dy h_dx
    change Rat.blt _ _ = false ↔ _
    unfold Rat.blt
    simp only
      [ Bool.and_eq_true, decide_eq_true_eq, Bool.ite_eq_false_distrib,
        decide_eq_false_iff_not, Rat.not_lt, ite_eq_left_iff,
        not_and, Rat.not_le, ← Rat.num_nonneg ]
    if h : ny < 0 ∧ 0 ≤ nx then
      simp only [h, and_self, ↓reduceIte, Bool.true_eq_false, num_nonneg, false_iff]
      simp only [Rat.sub_def, Rat.not_le, normalize_eq, Rat.neg]
      simp [← Rat.num_neg]
      apply Int.ediv_neg_of_neg_of_pos
      · apply Int.sub_neg_of_lt
        apply Int.lt_of_lt_of_le (b := 0)
        · apply Int.mul_neg_of_neg_of_pos h.1
          apply Int.natCast_pos.mpr
          apply Nat.pos_of_ne_zero h_dx
        · apply Int.mul_nonneg h.2
          exact Int.zero_le_natCast
      · apply Int.natCast_pos.mpr
        apply Nat.pos_iff_ne_zero.mpr
        exact Nat.gcd_ne_zero_right dy_dx_nz
    else
      simp [h]
      split
      case isTrue nb_0 =>
        simp [nb_0, Rat.sub_eq_add_neg, Rat.zero_add, Rat.nonneg_sub_iff_nonpos, ← Rat.num_nonpos]
      case isFalse nb_nz =>
        simp only [Rat.sub_def, normalize_eq, ← Rat.num_nonneg]
        if ny_pos : 0 < ny then
          simp only [ny_pos, forall_const]
          if h_na : 0 < nx then
            simp_all only [not_and, Int.not_le, forall_const]
            rw [← Int.sub_nonneg]
            apply Iff.symm
            apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz
          else
            let na_nonpos := Int.not_lt.mp h_na
            simp_all only [not_and, Int.not_le, false_implies, true_iff, ge_iff_le]
            apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz |>.mpr
            · apply Int.sub_nonneg_of_le
              apply Int.le_trans (b := 0)
              apply Int.mul_nonpos_of_nonpos_of_nonneg
              · exact Int.not_lt.mp h_na
              · exact Int.natCast_nonneg ↑dy
              · apply Int.mul_nonneg _ (Int.natCast_nonneg ↑dx)
                exact Int.le_of_lt ny_pos
        else
          simp [ny_pos, Int.not_lt, ← Int.sub_nonneg]
          rw [Int.sub_zero]
          rw [Int.sub_zero]
          apply Iff.symm
          apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz

protected theorem sub_nonneg {a b : Rat} : 0 ≤ a - b ↔ b ≤ a := by
  rw [Rat.le_iff_sub_nonneg b a]

@[simp]
theorem divInt_nonneg_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 ≤ a /. b ↔ 0 ≤ a := by
  cases hab : a /. b with | mk' n d hd hnd =>
  rw [mk'_eq_divInt, divInt_eq_iff (Int.ne_of_lt hb).symm (mod_cast hd)] at hab
  rw [
    ← Rat.num_nonneg, ← Int.mul_nonneg_iff_of_pos_right hb, ← hab,
    Int.mul_nonneg_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd),
  ]

theorem divInt_pos_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 < a /. b ↔ 0 < a := by
  cases hab : a /. b with | mk' n d hd hnd =>
  rw [mk'_eq_divInt, divInt_eq_iff (Int.ne_of_lt hb).symm (mod_cast hd)] at hab
  rw [ ← Rat.num_pos, <- Int.mul_pos_iff_of_pos_right hb, <- hab,
       Int.mul_pos_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd)]

theorem divInt_neg_iff_of_neg_right {a b : Int} (hb : 0 < b) : 0 > a /. b ↔ 0 > a := by
  have f : ¬ (0 ≤ a /. b) ↔ ¬ (0 ≤ a) := not_congr (divInt_nonneg_iff_of_pos_right hb)
  rw [Int.not_le, Rat.not_le] at f
  exact f

protected theorem divInt_le_divInt
  {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d)
: a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [Rat.sub_eq_add_neg, Rat.neg_divInt, Int.ne_of_gt b0, Int.ne_of_gt d0, Int.mul_pos d0 b0]
  rw [Rat.divInt_add_divInt]
  simp only [Rat.divInt_nonneg_iff_of_pos_right (Int.mul_pos d0 b0), Int.neg_mul]
  rw [← Int.sub_nonneg (a := c * b)]
  rw [← Int.sub_eq_add_neg]
  · apply Int.lt_iff_le_and_ne.mp d0 |>.2 |>.symm
  · apply Int.lt_iff_le_and_ne.mp b0 |>.2 |>.symm

theorem mul_assoc (a b c : Rat) : a * b * c = a * (b * c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, Int.mul_comm, Nat.mul_assoc, Int.mul_left_comm, mkRat_mul_mkRat]

theorem cast_lt1 {a b : Int} : Rat.ofInt a < Rat.ofInt b -> a < b := by
  intro h
  simp [Rat.instLT, Rat.ofInt] at h
  simp [Rat.blt] at h
  cases h with
  | inl h =>
    let ⟨h1, h2⟩ := h
    exact Int.lt_of_lt_of_le h1 h2
  | inr h =>
    cases Classical.em (a = 0) with
    | inl ha => simp [ha] at h; exact lt_of_eq_of_lt ha h
    | inr ha =>
      simp [ha] at h
      exact h.2

theorem cast_lt2 {a b : Int} : a < b → Rat.ofInt a < Rat.ofInt b := by
  intro h
  simp only [instLT, ofInt, mk_den_one]
  simp [Rat.blt]
  cases Classical.em (a = 0) with
  | inl ha => simp [ha]; rw [ha] at h; exact h
  | inr ha =>
      simp only [ha, ↓reduceIte]
      right
      constructor
      · omega
      · exact h

theorem cast_lt {a b : Int} : a < b ↔ Rat.ofInt a < Rat.ofInt b :=
  ⟨ Rat.cast_lt2, Rat.cast_lt1 ⟩

theorem cast_le1 {a b : Int} : Rat.ofInt a ≤ Rat.ofInt b -> a ≤ b := by
  intro h
  simp only [instLE, ofInt, mk_den_one] at h
  simp [Rat.blt] at h
  cases Classical.em (b = 0) with
  | inl hb =>
    simp [hb] at h
    rw [hb]
    exact h
  | inr hb =>
    simp [hb] at h
    let ⟨h1, h2⟩ := h
    cases Classical.em (a ≤ b) with
    | inl hab => exact hab
    | inr hab =>
      have : ¬ a ≤ b → ¬ (b ≤ 0 ∨ 0 < a) := fun a_1 a => hab (h2 a)
      have := this hab
      rw [not_or] at this
      let ⟨h3, h4⟩ := this
      rw [Int.not_le] at h3
      rw [Int.not_lt] at h4
      have := Int.lt_of_le_of_lt h4 h3
      exact Int.le_of_lt this

theorem cast_le2 {a b : Int} : a ≤ b → Rat.ofInt a ≤ Rat.ofInt b := by
  intro h
  simp [Rat.instLE, Rat.ofInt]
  simp [Rat.blt]
  cases Classical.em (b = 0) with
  | inl hb =>
    simp [hb]
    rw [hb] at h
    exact h
  | inr hb =>
    simp [hb]
    constructor <;> omega

theorem cast_le {a b : Int} : a ≤ b ↔ Rat.ofInt a ≤ Rat.ofInt b :=
  ⟨ Rat.cast_le2, Rat.cast_le1 ⟩

theorem cast_ge {a b : Int} : a ≥ b ↔ Rat.ofInt a ≥ Rat.ofInt b :=
  ⟨ Rat.cast_le2, Rat.cast_le1 ⟩

theorem cast_gt {a b : Int} : a > b ↔ Rat.ofInt a > Rat.ofInt b :=
  ⟨ Rat.cast_lt2, Rat.cast_lt1 ⟩

theorem cast_eq {a b : Int} : a = b ↔ Rat.ofInt a = Rat.ofInt b := by
  constructor
  · intro h; rw [h]
  · intro h; exact Rat.intCast_inj.mp h

theorem floor_def' (a : Rat) : a.floor = a.num / a.den := by
  rw [Rat.floor]
  split
  · next h => simp [h]
  · next => rfl

theorem intCast_eq_divInt (z : Int) : (z : Rat) = z /. 1 := mk'_eq_divInt

theorem le_floor {z : Int} : ∀ {r : Rat}, z ≤ Rat.floor r ↔ (z : Rat) ≤ r
  | ⟨n, d, h, c⟩ => by
    simp only [Rat.floor_def']
    rw [mk'_eq_divInt]
    have h' := Int.ofNat_lt.2 (Nat.pos_of_ne_zero h)
    conv =>
      rhs
      rw [Rat.intCast_eq_divInt, Rat.divInt_le_divInt Int.zero_lt_one h', Int.mul_one]
    exact Int.le_ediv_iff_mul_le h'

theorem mul_add (a b c : Rat) : a * (b + c) = a * b + a * c :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz =>
      Rat.numDenCasesOn' c fun c_num c_den c_den_nz => by
        have a_den_nz' : (a_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr a_den_nz
        have b_den_nz' : (b_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr b_den_nz
        have c_den_nz' : (c_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr c_den_nz
        have ab_den_nz : (a_den * b_den : Int) ≠ 0 := Int.mul_ne_zero a_den_nz' b_den_nz'
        have bc_den_nz : (b_den * c_den : Int) ≠ 0 := Int.mul_ne_zero b_den_nz' c_den_nz'
        have ac_den_nz : (a_den * c_den : Int) ≠ 0 := Int.mul_ne_zero a_den_nz' c_den_nz'
        have abc_den_nz : (a_den * (b_den * c_den) : Int) ≠ 0 := Int.mul_ne_zero a_den_nz' bc_den_nz
        have abac_den_nz : (a_den * b_den * (a_den * c_den) : Int) ≠ 0 := Int.mul_ne_zero ab_den_nz ac_den_nz
        rw [Rat.divInt_mul_divInt a_num b_num a_den_nz' b_den_nz']
        rw [Rat.divInt_mul_divInt a_num c_num a_den_nz' c_den_nz']
        rw [Rat.divInt_add_divInt (a_num * b_num) (a_num * c_num) ab_den_nz ac_den_nz]
        rw [Rat.divInt_add_divInt b_num c_num b_den_nz' c_den_nz']
        rw [Rat.divInt_mul_divInt a_num (b_num * c_den + c_num * b_den) a_den_nz' bc_den_nz]
        rw [Rat.divInt_eq_iff abc_den_nz abac_den_nz]
        rw [Int.mul_assoc]
        rw [Int.mul_comm _ (a_den * (b_den * c_den))]
        rw [Int.mul_assoc a_num b_num]
        rw [Int.mul_assoc a_num c_num]
        rw [<- Int.mul_add a_num]
        rw [Int.mul_comm b_num (a_den * c_den)]
        rw [Int.mul_assoc a_den c_den b_num]
        rw [Int.mul_comm c_num (a_den * b_den)]
        rw [Int.mul_assoc a_den b_den c_num]
        rw [<- Int.mul_add a_den]
        simp [Int.mul_assoc, Int.mul_comm]
        rw [<- Int.mul_assoc a_den (b_num * c_den + c_num * b_den)]
        rw [Int.mul_comm a_den (b_num * c_den + c_num * b_den)]
        simp [Int.mul_assoc]
        rw [<- Int.mul_assoc b_den a_den c_den]
        rw [Int.mul_comm b_den a_den]
        rw [Int.mul_assoc a_den b_den c_den]

@[simp]
protected theorem neg_zero : -(0:Rat) = 0 := rfl

protected theorem add_mul (a b c : Rat) : (a + b) * c = a * c + b * c := by
  simp [Rat.mul_comm, Rat.mul_add]

protected theorem neg_add (a b : Rat) : -(a + b) = -a + -b := by
  rw [←Rat.sub_eq_add_neg, ←Rat.neg_neg b, ←Rat.sub_eq_add_neg, Rat.neg_sub]
  simp [Rat.sub_eq_add_neg, Rat.add_comm, Rat.neg_neg]

theorem neg_eq_neg_one_mul (a : Rat) : -a = -1 * a :=
  numDenCasesOn a fun n d h h1 => by
    simp [Rat.neg_mkRat, Rat.mul_def, Rat.normalize_eq_mkRat]
    simp [← Rat.divInt_ofNat]
    rw [divInt_num' (Nat.pos_iff_ne_zero.mp h) h1, divInt_den' (Nat.pos_iff_ne_zero.mp h) h1]

protected theorem neg_mul (a b : Rat) : -(a * b) = -a * b := by
  rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul a, Rat.mul_assoc]

protected theorem mul_neg (a b : Rat) : a * -b = -(a * b) := by
  rw [neg_eq_neg_one_mul (a * b), neg_eq_neg_one_mul b, ← Rat.mul_assoc, Rat.mul_comm a, Rat.mul_assoc]

protected theorem mul_div_right_comm (a b c : Rat) : a * b / c = a / c * b := by
  rw [div_def, div_def, Rat.mul_assoc, Rat.mul_comm b c.inv, Rat.mul_assoc]

protected theorem zero_div (a : Rat) : 0 / a = 0 := by
  simp [div_def]

protected theorem add_div (a b c : Rat) : (a + b) / c = a / c + b / c := by
  simp [div_def, Rat.add_mul]

theorem le_total (a b : Rat) : a ≤ b ∨ b ≤ a := by
  simpa only [← Rat.le_iff_sub_nonneg, Rat.neg_sub] using Rat.nonneg_total (b - a)

theorem divInt_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a /. b := by
  have : 0 = b ∨ 0 < b := Int.le_iff_eq_or_lt.mp hb
  obtain rfl | hb := this
  · simp
  rwa [divInt_nonneg_iff_of_pos_right hb]

theorem mul_nonneg {a b : Rat} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : Int) := mod_cast Nat.pos_of_ne_zero h₁
      have d₂0 : 0 < (d₂ : Int) := mod_cast Nat.pos_of_ne_zero h₂
      simp only [d₁0, d₂0, Int.mul_pos, divInt_nonneg_iff_of_pos_right,
        divInt_mul_divInt _ _ (Ne.symm (Int.ne_of_lt d₁0)) (Ne.symm (Int.ne_of_lt d₁0))]
      intro h1 h2
      have h1' : 0 ≤ Rat.divInt n₁ d₁ := divInt_nonneg h1 (Int.ofNat_zero_le d₁)
      have h2' : 0 ≤ Rat.divInt n₂ d₂ := divInt_nonneg h2 (Int.ofNat_zero_le d₂)
      rw [divInt_mul_divInt n₁ n₂ (Int.ofNat_ne_zero.mpr h₁) ((Int.ofNat_ne_zero.mpr h₂))]
      apply divInt_nonneg
      · exact Int.mul_nonneg h1 h2
      · exact Lean.Omega.Int.ofNat_mul_nonneg

def addN : List Rat → Rat
  | []      => 0
  | [x]     => x
  | x :: xs => x + addN xs

@[simp] theorem addN_append : addN (xs ++ ys) = addN xs + addN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [addN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, addN, addN, addN_append, Rat.add_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem addN_cons_append : addN (x :: xs) = x + addN xs := by
  cases xs <;> simp only [addN, Rat.add_zero]

def mulN : List Rat → Rat
  | []      => 1
  | [x]     => x
  | x :: xs => x * mulN xs

@[simp] theorem mulN_append : mulN (xs ++ ys) = mulN xs * mulN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [mulN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, mulN, mulN, mulN_append, Rat.mul_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem mulN_cons_append : mulN (x :: xs) = x * mulN xs := by
  cases xs <;> simp only [mulN, Rat.mul_one]

end Rat

namespace Smt.Reconstruct.Rat.PolyNorm

structure Var where
  type : Bool
  val  : Nat
deriving DecidableEq, Repr

instance : LE Var where
  le v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val)

instance : LT Var where
  lt v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val)

instance (v₁ v₂ : Var) : Decidable (v₁ ≤ v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val) then isTrue h else isFalse h

instance (v₁ v₂ : Var) : Decidable (v₁ < v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val) then isTrue h else isFalse h

def Context := Var → Rat

def IntContext := Nat → Int
def RatContext := Nat → Rat

structure Monomial where
  coeff : Rat
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

def neg (m : Monomial) : Monomial :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial) (_ : m₁.vars = m₂.vars) : Monomial :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial) : Monomial :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert (x : Var) : List Var → List Var
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def divConst (m : Monomial) (c : Rat) : Monomial :=
  { m with coeff := m.coeff / c }

def eval (ctx : Context) (m : Monomial) : Rat :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem eval_neg {m : Monomial} : m.neg.eval ctx = -m.eval ctx := by
  simp only [neg, eval, Rat.neg_mul]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (z1 z2 : α):
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (z1 z2 : α):
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons, ih, assoc]

end
-- Can be generalized.
theorem foldl_mul_insert {ctx : Context} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [mul.insert]
  | cons x ys ih =>
    by_cases h : y ≤ x
    · simp [mul.insert, h, foldl_assoc Rat.mul_assoc (ctx y) (ctx x), Rat.mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, Rat.mul_comm,
                 foldl_assoc Rat.mul_assoc, ih]
      rw [← Rat.mul_assoc, Rat.mul_comm (ctx x) (ctx y), Rat.mul_assoc]

theorem eval_add {m n : Monomial} (h : m.vars = n.vars) :
  (m.add n h).eval ctx = m.eval ctx + n.eval ctx := by
  simp only [add, eval, Rat.add_mul, h]

theorem eval_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).eval ctx = m₁.eval ctx * m₂.eval ctx := by
  simp only [eval, mul, Rat.mul_assoc]; congr 1
  rw [← Rat.mul_assoc, Rat.mul_comm _ m₂.coeff, Rat.mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp [Rat.mul_assoc]
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc Rat.mul_assoc, ih]

theorem eval_divConst {m : Monomial} : (m.divConst c).eval ctx = m.eval ctx / c := by
  simp only [eval, divConst, Rat.mul_div_right_comm]

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

def neg (p : Polynomial) : Polynomial :=
  p.map Monomial.neg

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial) : Polynomial :=
  p.foldr insert q
where
  insert (m : Monomial) : Polynomial → Polynomial
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial) : Polynomial :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial) (p : Polynomial) : Polynomial :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial) : Polynomial :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def divConst (p : Polynomial) (c : Rat) : Polynomial :=
  p.map (·.divConst c)

def eval (ctx : Context) (p : Polynomial) : Rat :=
  p.foldl (fun acc m => acc + m.eval ctx) 0

theorem foldl_add_insert (ctx : Context) :
  List.foldl (fun z a => z + (Monomial.eval ctx a)) 0 (add.insert m p) =
  (Monomial.eval ctx m) + List.foldl (fun z a => z + (Monomial.eval ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←Rat.add_assoc, Rat.add_comm, ←Monomial.eval_add heq]
          simp [Monomial.eval, hneq]
        · simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Monomial.eval_add, heq, Rat.add_assoc]
      · simp only [List.foldl_cons, Rat.add_comm 0, ih, Monomial.foldl_assoc Rat.add_assoc]
        rw [←Rat.add_assoc, Rat.add_comm (Monomial.eval ctx n), Rat.add_assoc]

theorem eval_neg {p : Polynomial} : p.neg.eval ctx = -p.eval ctx := by
  simp only [eval, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.neg_add, ←ih, List.map, Monomial.eval_neg]

theorem eval_add {p q : Polynomial} : (p.add q).eval ctx = p.eval ctx + q.eval ctx := by
  simp only [eval, add]
  induction p with
  | nil => simp [add.insert]
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.add_assoc]
    rw [← ih, foldl_add_insert]

theorem eval_sub {p q : Polynomial} : (p.sub q).eval ctx = p.eval ctx - q.eval ctx := by
  simp only [sub, eval_neg, eval_add, Rat.sub_eq_add_neg]

theorem eval_mulMonomial {p : Polynomial} : (p.mulMonomial m).eval ctx = m.eval ctx * p.eval ctx := by
  simp only [eval, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.mul_add, ←ih]
    simp [foldl_add_insert, Monomial.eval_mul]

theorem eval_cons {p : List Monomial} {ctx : Context} : eval ctx (m :: p) = m.eval ctx + eval ctx p := by
  simp only [eval, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]

theorem eval_nil_add : eval ctx (p.add []) = eval ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [eval_add, List.foldr_cons, eval_cons, ih, show eval ctx [] = 0 by rfl]

theorem eval_add_insert {g : Monomial → Polynomial} :
  eval ctx (List.foldl (fun acc m => (g m).add acc) n p) = eval ctx n + eval ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [eval]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons, List.foldr, @ih n]
    rw [ih, @ih ((g k).add []), ← Rat.add_assoc, eval_nil_add, eval_add, Rat.add_comm _ (eval ctx n)]

theorem eval_foldl {g : Monomial → Polynomial} :
  eval ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).eval ctx + acc) 0 p := by
  induction p with
  | nil => simp [eval]
  | cons n p ih =>
    simp only [List.foldl_cons, Rat.add_comm, List.foldr] at *
    rw [Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, ←ih, eval_add_insert, eval_nil_add]

theorem eval_mul {p q : Polynomial} : (p.mul q).eval ctx = p.eval ctx * q.eval ctx :=by
  simp only [mul]
  induction p with
  | nil => simp [eval]
  | cons n p ih =>
    simp only [List.foldl_cons, eval_cons, Rat.add_mul, ← ih]
    rw [eval_foldl, eval_add_insert, ←eval_mulMonomial, eval_nil_add, eval_foldl]

theorem eval_divConst {p : Polynomial} : (p.divConst c).eval ctx = p.eval ctx / c := by
  simp only [eval, divConst]
  induction p with
  | nil => simp [Rat.zero_div]
  | cons x ys ih =>
    simp only [List.map_cons, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]
    rw [Monomial.eval_divConst, ih, Rat.add_div]

end Polynomial

inductive IntExpr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : IntExpr)
  | add (a b : IntExpr)
  | sub (a b : IntExpr)
  | mul (a b : IntExpr)
deriving Inhabited, Repr

namespace IntExpr

def toPoly : IntExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨false, v⟩] }]
  | .neg a => a.toPoly.neg
  | .add a b => Polynomial.add a.toPoly b.toPoly
  | .sub a b => Polynomial.sub a.toPoly b.toPoly
  | .mul a b => Polynomial.mul a.toPoly b.toPoly

def eval (ctx : IntContext) : IntExpr → Int
  | .val v => v
  | .var v => ctx v
  | .neg a => -a.eval ctx
  | .add a b => a.eval ctx + b.eval ctx
  | .sub a b => a.eval ctx - b.eval ctx
  | .mul a b => a.eval ctx * b.eval ctx

theorem eval_toPoly {rctx : RatContext} {e : IntExpr} : e.eval ictx = e.toPoly.eval (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [eval, toPoly]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · simp [Polynomial.eval, Monomial.eval]
  | var v =>
    simp [eval, toPoly, Polynomial.eval, Monomial.eval]
  | neg a ih =>
    simp only [eval, toPoly, Polynomial.eval_neg, Rat.intCast_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_add, Rat.intCast_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_sub, Rat.intCast_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_mul, Rat.intCast_mul, ih₁, ih₂]

end IntExpr

inductive RatExpr where
  | val (v : Rat)
  | var (v : Nat)
  | neg (a : RatExpr)
  | add (a b : RatExpr)
  | sub (a b : RatExpr)
  | mul (a b : RatExpr)
  | divConst (a : RatExpr) (c : Rat)
  | cast (a : IntExpr)
deriving Inhabited, Repr

namespace RatExpr

def toPoly : RatExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨true, v⟩] }]
  | .neg a => a.toPoly.neg
  | .add a b => Polynomial.add a.toPoly b.toPoly
  | .sub a b => Polynomial.sub a.toPoly b.toPoly
  | .mul a b => Polynomial.mul a.toPoly b.toPoly
  | .divConst a c => Polynomial.divConst a.toPoly c
  | .cast a => a.toPoly

def eval (ictx : IntContext) (rctx : RatContext)  : RatExpr → Rat
  | .val v => v
  | .var v => rctx v
  | .neg a => -a.eval ictx rctx
  | .add a b => a.eval ictx rctx + b.eval ictx rctx
  | .sub a b => a.eval ictx rctx - b.eval ictx rctx
  | .mul a b => a.eval ictx rctx * b.eval ictx rctx
  | .divConst a c => a.eval ictx rctx / c
  | .cast a => a.eval ictx

theorem eval_toPoly {e : RatExpr} : e.eval ictx rctx = e.toPoly.eval (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [eval, toPoly]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · simp [Polynomial.eval, Monomial.eval]
  | var v =>
    simp [eval, toPoly, Polynomial.eval, Monomial.eval]
  | neg a ih =>
    simp only [eval, toPoly, Polynomial.eval_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_mul, ih₁, ih₂]
  | divConst a c ih =>
    simp only [eval, toPoly, Polynomial.eval_divConst, ih]
  | cast a =>
    simpa only [eval] using IntExpr.eval_toPoly

theorem eval_eq_from_toPoly_eq {e₁ e₂ : RatExpr} (h : e₁.toPoly = e₂.toPoly) : e₁.eval ictx rctx = e₂.eval ictx rctx := by
  rw [eval_toPoly, eval_toPoly, h]

end Smt.Reconstruct.Rat.PolyNorm.RatExpr

namespace Rat

section le_lt_defs

variable {x y : Rat}

theorem le_of_not_le {a b : Rat} : ¬ a ≤ b → b ≤ a := (Rat.le_total a b).resolve_left

theorem lt_iff_le_not_le (a b : Rat) : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [← Rat.not_le]
  refine Iff.symm ((and_iff_right_of_imp (a := a ≤ b) (b := ¬ b ≤ a)) ?_)
  intro h
  cases le_total a b with
  | inl hl => exact hl
  | inr hr => exact False.elim (h hr)

theorem neg_self_add (c : Rat) : -c + c = 0 := by
  simp only [add_def, neg_num, Int.neg_mul, neg_den, Int.add_left_neg, normalize_zero]

theorem le_antisymm {a b : Rat} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  rw [Rat.le_iff_sub_nonneg] at hab hba
  rw [Rat.sub_eq_add_neg] at hba
  rw [← Rat.neg_sub, Rat.sub_eq_add_neg] at hab
  have := Rat.nonneg_antisymm _ hba hab
  have := congrArg (fun x => x + b) this
  simp at this
  rw [Rat.add_assoc, Rat.neg_self_add] at this
  rw [Rat.add_zero] at this
  exact this

theorem le_antisymm_iff (a b : Rat) : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨fun h ↦ ⟨by rw [h]; exact Rat.le_refl _, by rw [h]; exact Rat.le_refl _⟩, fun ⟨ab, ba⟩ ↦ Rat.le_antisymm ab ba⟩

theorem le_iff_eq_or_lt (a b : Rat) : a ≤ b ↔ a = b ∨ a < b := by
  rw [Rat.le_antisymm_iff, Rat.lt_iff_le_not_le, ← and_or_left]; simp [Classical.em]

theorem lt_iff_sub_pos (a b : Rat) : a < b ↔ 0 < b - a := by
  constructor
  · intro h
    have ⟨le, nle⟩ := (Rat.lt_iff_le_not_le a b).mp h
    have h' := (Rat.le_iff_sub_nonneg a b).mp le
    cases (Rat.le_iff_eq_or_lt 0 (b - a)).mp h' with
    | inl eq =>
        have eq' := Eq.symm eq
        rw [Rat.sub_eq_add_neg] at eq'
        have h'' := Rat.eq_neg_of_add_eq_zero_left _ _ eq'
        rw [Rat.neg_neg] at h''
        rw [h''] at h
        have abs := Rat.ne_of_lt _ _ h
        exact (False.elim (abs rfl))
    | inr lt => exact lt
  · intro h
    have ⟨le, nle⟩ := (Rat.lt_iff_le_not_le 0 (b - a)).mp h
    have h' := (Rat.le_iff_sub_nonneg a b).mpr le
    cases (Rat.le_iff_eq_or_lt a b).mp h' with
    | inl eq => rw [eq] at h; simp at h; apply False.elim; exact (Bool.eq_not_self (Rat.blt 0 0)).mp h
    | inr lt => exact lt

protected theorem divInt_lt_divInt
  {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d)
: a /. b < c /. d ↔ a * d < c * b := by
  rw [Rat.lt_iff_sub_pos, ← Int.sub_pos]
  simp only [Rat.sub_eq_add_neg, Rat.neg_divInt, Int.ne_of_gt b0, Int.ne_of_gt d0, Int.mul_pos d0 b0]
  rw [Rat.divInt_add_divInt]
  simp only [Int.neg_mul, Rat.divInt_pos_iff_of_pos_right (Int.mul_pos d0 b0), Int.sub_pos]
  rw [← Int.sub_pos (a := c * b)]
  rw [← Int.sub_eq_add_neg]
  · exact Ne.symm (Int.ne_of_lt d0)
  · exact Ne.symm (Int.ne_of_lt b0)

variable {x y : Rat}

theorem add_sub_add_left_eq_sub (a b c : Rat) : c + a - (c + b) = a - b := by
  rw [ Rat.sub_eq_add_neg,
       Rat.add_assoc c a (-(c + b)),
       Rat.add_comm a (-(c + b)),
       <- Rat.add_assoc c (-(c + b)) a,
       Rat.neg_add,
       Rat.sub_eq_add_neg,
       <- Rat.add_assoc c (-c) (-b),
       Rat.add_neg_self,
       Rat.zero_add,
       Rat.add_comm,
    ]

theorem add_le_add_left {a b c : Rat} : c + a ≤ c + b ↔ a ≤ b := by
  rw [Rat.le_iff_sub_nonneg, Rat.add_sub_add_left_eq_sub, ← Rat.le_iff_sub_nonneg]

theorem add_lt_add_left {a b c : Rat} : c + a < c + b ↔ a < b := by
  rw [Rat.lt_iff_sub_pos, Rat.add_sub_add_left_eq_sub, ← Rat.lt_iff_sub_pos]

protected theorem le_def : x ≤ y ↔ x.num * y.den ≤ y.num * x.den := by
  rw [← num_divInt_den y, ← num_divInt_den x]
  conv => rhs ; simp only [num_divInt_den]
  exact Rat.divInt_le_divInt (mod_cast x.den_pos) (mod_cast y.den_pos)

protected theorem lt_iff_le_and_ne : x < y ↔ x ≤ y ∧ x ≠ y := ⟨
  fun h => ⟨Rat.le_of_lt _ _ h, Rat.ne_of_lt _ _ h⟩,
  fun h => by
    let ⟨h_le, h_ne⟩ := h
    rw [Rat.lt_iff_le_not_le]
    apply And.intro h_le
    intro h_le'
    let _ := Rat.le_antisymm h_le h_le'
    contradiction
⟩

protected theorem lt_def : x < y ↔ x.num * y.den < y.num * x.den := by
  rw [Rat.lt_iff_le_and_ne, Rat.le_def]
  suffices x ≠ y ↔ x.num * y.den ≠ y.num * x.den by
    constructor <;> intro h
    · exact Int.lt_iff_le_and_ne.mpr ⟨h.left, this.mp h.right⟩
    · have tmp := Int.lt_iff_le_and_ne.mp h
      exact ⟨tmp.left, this.mpr tmp.right⟩
  exact Decidable.not_iff_not.mpr Rat.eq_iff_mul_eq_mul

end le_lt_defs

theorem floor_le_self (r : Rat) : r.floor ≤ r := Rat.le_floor.mp (Int.le_refl r.floor)

theorem self_le_floor_add_one (r : Rat) : r < ↑(r.floor + 1) := by
  simp only [intCast_eq_divInt, floor_def']
  conv =>
    lhs
    rw [← Rat.num_divInt_den r]
  rw [Rat.divInt_lt_divInt (by simp [Rat.den_pos]) (by simp), Int.add_mul, Int.one_mul, Int.mul_one]
  rw [← Int.add_lt_add_iff_right (r.num % r.den), Int.add_right_comm, Int.ediv_add_emod']
  rw [Int.add_lt_add_iff_left]
  apply Int.emod_lt _ (Int.ne_of_lt (by simp [Rat.den_pos])).symm

end Rat

private theorem Rat.mul_le_mul_left {c x y : Rat} (hc : c > 0) : (c * x ≤ c * y) = (x ≤ y) := by
  apply propext
  exact
    numDenCasesOn' x fun n₁ d₁ h₁ =>
    numDenCasesOn' y fun n₂ d₂ h₂ => by
      cases c_def : c with
      | mk' nc dc dc_nz _ =>
        rw [<- c_def, <- divInt_self c]
        have foo : (c.den : Int) ≠ (0 : Int) := by rw [c_def]; exact Int.ofNat_ne_zero.mpr dc_nz
        have bar : (d₂ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₂
        have baz : (d₁ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₁
        rw [Rat.divInt_mul_divInt _ _ foo bar, Rat.divInt_mul_divInt _ _ foo baz]
        have c_den_pos : (0 : Int) < c.den := Int.cast_pos' fun a => foo (congrArg Nat.cast a)
        have d1_pos : (0 : Int) < d₁ := Int.cast_pos' h₁
        have d2_pos : (0 : Int) < d₂ := Int.cast_pos' h₂
        have den_pos1 : (0 : Int) < c.den * d₁ := Int.mul_pos c_den_pos d1_pos
        have den_pos2 : (0 : Int) < c.den * d₂ := Int.mul_pos c_den_pos d2_pos
        rw [Rat.divInt_le_divInt den_pos1 den_pos2]
        rw [Rat.divInt_le_divInt d1_pos d2_pos]
        rw [Int.mul_assoc, Int.mul_assoc]
        constructor
        · intro h
          have c_num_pos : 0 < c.num := (Rat.num_pos c).mpr hc
          have h' := Int.le_of_mul_le_mul_left h c_num_pos
          rw [<- Int.mul_assoc,
              <- Int.mul_assoc,
              Int.mul_comm n₁ c.den,
              Int.mul_comm n₂ c.den,
              Int.mul_assoc,
              Int.mul_assoc] at h'
          exact Int.le_of_mul_le_mul_left h' c_den_pos
        · intro h
          have : 0 ≤ c.num := (Rat.num_nonneg c).mpr (Rat.le_of_lt 0 c hc)
          refine Int.mul_le_mul_of_nonneg_left ?_ this
          rw [<- Int.mul_assoc,
              <- Int.mul_assoc,
              Int.mul_comm n₁ c.den,
              Int.mul_comm n₂ c.den,
              Int.mul_assoc,
              Int.mul_assoc]
          exact Int.mul_le_mul_of_nonneg_left h (Int.ofNat_zero_le c.den)

private theorem Rat.mul_le_mul_left' {c x y : Rat} (hc : c ≥ 0) : x ≤ y → (c * x ≤ c * y) := by
  intro h
  have : 0 = c ∨ 0 < c := (le_iff_eq_or_lt 0 c).mp hc
  cases this
  next heq =>
    rw [<- heq]
    simp
  next hlt =>
    exact (Rat.mul_le_mul_left hlt).mpr h

private theorem Rat.mul_lt_mul_left {c x y : Rat} : 0 < c → ((c * x < c * y) ↔ (x < y)) :=
  numDenCasesOn' x fun n₁ d₁ h₁ =>
    numDenCasesOn' y fun n₂ d₂ h₂ => by
      cases c_def : c with
      | mk' nc dc dc_nz _ =>
        rw [<- c_def, <- divInt_self c]
        have foo : (c.den : Int) ≠ (0 : Int) := by rw [c_def]; exact Int.ofNat_ne_zero.mpr dc_nz
        have bar : (d₂ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₂
        have baz : (d₁ : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr h₁
        rw [Rat.divInt_mul_divInt _ _ foo bar, Rat.divInt_mul_divInt _ _ foo baz]
        have c_den_pos : (0 : Int) < c.den := Int.cast_pos' fun a => foo (congrArg Nat.cast a)
        have d1_pos : (0 : Int) < d₁ := Int.cast_pos' h₁
        have d2_pos : (0 : Int) < d₂ := Int.cast_pos' h₂
        have den_pos1 : (0 : Int) < c.den * d₁ := Int.mul_pos c_den_pos d1_pos
        have den_pos2 : (0 : Int) < c.den * d₂ := Int.mul_pos c_den_pos d2_pos
        rw [Rat.divInt_lt_divInt den_pos1 den_pos2]
        rw [Rat.divInt_lt_divInt d1_pos d2_pos]
        intro h
        have c_pos : 0 < c.num := (divInt_pos_iff_of_pos_right c_den_pos).mp h
        constructor
        · intro h2
          rw [Int.mul_assoc] at h2
          rw [Int.mul_assoc] at h2
          have h2' := Int.lt_of_mul_lt_mul_left (a := c.num) h2 (Int.le_of_lt c_pos)
          rw [<- Int.mul_assoc, <- Int.mul_assoc, Int.mul_comm n₁ c.den, Int.mul_comm n₂ c.den] at h2'
          rw [Int.mul_assoc, Int.mul_assoc] at h2'
          exact Int.lt_of_mul_lt_mul_left (a := c.den) h2' (Int.ofNat_zero_le c.den)
        · intro h2
          have h2' := Int.mul_lt_mul_of_pos_left h2 c_pos
          have h2'' := Int.mul_lt_mul_of_pos_left h2' c_den_pos
          rw [<- Int.mul_assoc] at h2''
          rw [<- Int.mul_assoc] at h2''
          rw [<- Int.mul_assoc] at h2''
          rw [<- Int.mul_assoc] at h2''
          rw [Int.mul_comm c.den c.num] at h2''
          rw [Int.mul_assoc c.num c.den n₁] at h2''
          rw [Int.mul_comm c.den n₁] at h2''
          rw [<- Int.mul_assoc] at h2''
          rw [Int.mul_assoc] at h2''
          rw [Int.mul_assoc c.num c.den n₂] at h2''
          rw [Int.mul_comm c.den n₂] at h2''
          rw [<- Int.mul_assoc c.num n₂ c.den] at h2''
          rw [Int.mul_assoc (c.num * n₂) c.den d₁] at h2''
          exact h2''

private theorem Rat.mul_eq_zero_left {x y : Rat} : x ≠ 0 → x * y = 0 → y = 0 :=
  numDenCasesOn' x fun nx dx nz_dx =>
    numDenCasesOn' y fun ny dy nz_dy => by
       intros h1 h2
       apply (Rat.mkRat_eq_zero nz_dy).mpr
       have nxn0 := (Rat.mkRat_ne_zero nz_dx).mp h1
       suffices nx * ny = 0
         by have nxy0 := Int.mul_eq_zero.mp this
            cases nxy0 with
            | inl nx0 => exact False.elim (nxn0 nx0)
            | inr ny0 => exact ny0
       have nz_dy' : (dy : Int) ≠ 0 := Int.ofNat_ne_zero.mpr nz_dy
       have nz_dx' : (dx : Int) ≠ 0 := Int.ofNat_ne_zero.mpr nz_dx
       rw [Rat.divInt_mul_divInt nx ny nz_dx' nz_dy'] at h2
       have nz_dxdy : (dx * dy) ≠ 0 := Nat.mul_ne_zero nz_dx nz_dy
       exact (Rat.mkRat_eq_zero nz_dxdy).mp h2

namespace Smt.Reconstruct.Rat

variable {a b c d x₁ x₂ y₁ y₂ : Rat}

theorem add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b :=
  Rat.numDenCasesOn' a fun n₁ d₁ h₁ ↦ Rat.numDenCasesOn' b fun n₂ d₂ h₂ ↦ by
    have d₁0 : 0 < (d₁ : Int) := mod_cast Nat.pos_of_ne_zero h₁
    have d₂0 : 0 < (d₂ : Int) := mod_cast Nat.pos_of_ne_zero h₂
    intro n₁0 n₂0
    rw [Rat.divInt_add_divInt _ _ (Int.ofNat_ne_zero.mpr h₁) (Int.ofNat_ne_zero.mpr h₂)]
    have : (0 : Int) < d₁ * d₂ := by exact Int.mul_pos d₁0 d₂0
    apply (Rat.divInt_nonneg_iff_of_pos_right this).mpr
    apply Int.add_nonneg
    · apply Int.mul_nonneg
      · exact (Rat.divInt_nonneg_iff_of_pos_right d₁0).mp n₁0
      · exact Int.ofNat_zero_le d₂
    · apply Int.mul_nonneg
      · exact (Rat.divInt_nonneg_iff_of_pos_right d₂0).mp n₂0
      · exact Int.ofNat_zero_le d₁

theorem le_trans (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  rw [Rat.le_iff_sub_nonneg] at hab hbc
  have := Rat.add_nonneg hab hbc
  rw [Rat.add_comm] at this
  rw [Rat.sub_eq_add_neg] at this
  rw [Rat.add_assoc] at this
  rw [Rat.sub_eq_add_neg] at this
  rw [<- Rat.add_assoc (-b) b (-a)] at this
  rw [Rat.neg_self_add] at this
  rw [Rat.zero_add] at this
  rw [<- Rat.sub_eq_add_neg] at this
  exact (Rat.le_iff_sub_nonneg a c).mpr this

theorem lt_of_le_not_le (hab : a ≤ b) (hba : ¬ b ≤ a) : a < b := (Rat.lt_iff_le_not_le _ _).mpr ⟨hab, hba⟩

theorem le_of_lt (hab : a < b) : a ≤ b := ((Rat.lt_iff_le_not_le _ _).1 hab).1

theorem not_le_of_lt (hab : a < b) : ¬ b ≤ a := ((Rat.lt_iff_le_not_le _ _).1 hab).2

theorem lt_of_lt_of_le (hab : a < b) (hbc : b ≤ c) : a < c :=
  lt_of_le_not_le (le_trans (le_of_lt hab) hbc) fun hca ↦ not_le_of_lt hab (le_trans hbc hca)

theorem lt_trans (hab : a < b) (hbc : b < c) : a < c := lt_of_lt_of_le hab (le_of_lt hbc)

theorem lt_of_le_of_lt (hab : a ≤ b) (hbc : b < c) : a < c :=
  lt_of_le_not_le (le_trans hab (le_of_lt hbc)) fun hca ↦ not_le_of_lt hbc (le_trans hca hab)

theorem sum_ub₁ (h₁ : a < b) (h₂ : c < d) : a + c < b + d := by
  have h' : c + a < c + b := Rat.add_lt_add_left.mpr h₁
  have h'' : b + c < b + d := Rat.add_lt_add_left.mpr h₂
  rewrite [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_trans h' h''

theorem sum_ub₂ (h₁ : a < b) (h₂ : c ≤ d) : a + c < b + d := by
  have h' : c + a < c + b := Rat.add_lt_add_left.mpr h₁
  have h'' : b + c ≤ b + d := Rat.add_le_add_left.mpr h₂
  rewrite [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_of_lt_of_le h' h''

theorem sum_ub₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by
  rewrite [h₂]
  have : d + a < d + b := Rat.add_lt_add_left.mpr h₁
  rewrite [Rat.add_comm, Rat.add_comm d b] at this
  exact this

theorem sum_ub₄ (h₁ : a ≤ b) (h₂ : c < d) : a + c < b + d := by
  have h' : c + a ≤ c + b := Rat.add_le_add_left.mpr h₁
  have h'' : b + c < b + d := Rat.add_lt_add_left.mpr h₂
  rewrite [Rat.add_comm, Rat.add_comm c b] at h'
  exact lt_of_le_of_lt h' h''

theorem sum_ub₅ (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  have h' : c + a ≤ c + b := Rat.add_le_add_left.mpr h₁
  have h'' : b + c ≤ b + d := Rat.add_le_add_left.mpr h₂
  rewrite [Rat.add_comm, Rat.add_comm c b] at h'
  exact le_trans h' h''

theorem sum_ub₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by
  rewrite [h₂, Rat.add_comm, Rat.add_comm b d]
  exact Rat.add_le_add_left.mpr h₁

theorem sum_ub₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by
  rewrite [h₁, Rat.add_comm b c, Rat.add_comm b d]
  exact sum_ub₃ h₂ rfl

theorem sum_ub₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by
  rewrite [h₁]
  exact Rat.add_le_add_left.mpr h₂

theorem sum_ub₉ (h₁ : a = b) (h₂ : c = d) : a + c = b + d := by
  rw [h₁, h₂]

theorem trichotomy₁ (h₁ : a ≤ b) (h₂ : a ≠ b) : a < b := by
  refine Rat.not_le.mp ?_
  intro abs
  have h := Rat.le_antisymm h₁ abs
  exact h₂ h

theorem trichotomy₂ (h₁ : a ≤ b) (h₂ : a ≥ b) : a = b :=
  Rat.le_antisymm h₁ h₂

theorem trichotomy₃ (h₁ : a ≠ b) (h₂ : a ≤ b) : a < b := by
  exact trichotomy₁ h₂ h₁

theorem trichotomy₄ (h₁ : a ≠ b) (h₂ : a ≥ b) : a > b := by
  exact trichotomy₃ (Ne.symm h₁) h₂

theorem trichotomy₅ (h₁ : a ≥ b) (h₂ : a ≤ b) : a = b := by
  exact Rat.le_antisymm h₂ h₁

theorem trichotomy₆ (h₁ : a ≥ b) (h₂ : a ≠ b) : a > b := by
  exact trichotomy₃ (Ne.symm h₂) h₁

theorem abs_elim {x : Rat} : x.abs = if x < 0 then -x else x :=
  rfl

theorem abs_eq {a b : Rat} (hb : 0 ≤ b) : a.abs = b ↔ a = b ∨ a = -b := by
  unfold Rat.abs
  cases Classical.em (a < 0)
  next hl =>
    simp [hl]
    constructor
    · intro h
      right
      have := congrArg (fun x => -x) h
      simp at this
      exact this
    · intro h
      cases h
      next h1 =>
        rw [h1] at hl
        apply False.elim
        have := lt_of_le_of_lt hb hl
        exact (Bool.eq_not_self (Rat.blt 0 0)).mp this
      next h2 =>
        have := congrArg (fun x => -x) h2
        simp at this
        exact this
  next hr =>
    simp [hr]
    intro h
    have := Rat.not_lt.mp hr
    rw [h] at this
    have : 0 = b := Eq.symm (Rat.nonneg_antisymm b hb this)
    rw [<- this] at h
    simp at h
    exact trans h this

theorem neg_of_pos {a : Rat} : 0 < a → -a < 0 := by
  intro h
  rw [<- Rat.neg_self_add a]
  have : -a = -a + 0 := by simp
  conv =>
    lhs
    rw [this]
    skip
  exact sum_ub₇ rfl h

theorem pos_of_neg {a : Rat} : a < 0 → 0 < -a := by
  intro h
  rw [<- Rat.neg_self_add a]
  have : -a = -a + 0 := by simp
  conv =>
    rhs
    rw [this]
    skip
  exact sum_ub₇ rfl h

theorem abs_nonneg (x : Rat) : 0 ≤ x.abs := by
  unfold Rat.abs
  split
  next hx =>
    have := pos_of_neg hx
    exact le_of_lt this
  next hx =>
    exact Rat.not_lt.mp hx

theorem abs_of_nonpos (h : a ≤ 0) : a.abs = -a := by
  unfold Rat.abs
  split
  next => rfl
  next hx =>
    have := Rat.not_lt.mp hx
    have : a = 0 := trichotomy₅ this h
    rw [this]
    simp

theorem abs_of_nonneg {a : Rat} (h : 0 ≤ a) : a.abs = a := by
  unfold Rat.abs
  split
  next hx =>
    have : a ≤ 0 := le_of_lt hx
    have : a = 0 := trichotomy₅ h this
    rw [this]
    simp
  next => rfl

theorem abs_mul (a b : Rat) : (a * b).abs = a.abs * b.abs := by
  rw [Rat.abs_eq (Rat.mul_nonneg (Rat.abs_nonneg a) (Rat.abs_nonneg b))]
  rcases Rat.le_total a 0 with ha | ha <;> rcases Rat.le_total b 0 with hb | hb <;>
    simp only [Rat.abs_of_nonpos, Rat.abs_of_nonneg, true_or, or_true, eq_self_iff_true, Rat.neg_mul,
      Rat.mul_neg, Rat.neg_neg, *]

theorem mul_abs₁ (h₁ : x₁.abs = y₁.abs) (h₂ : x₂.abs = y₂.abs) : (x₁ * x₂).abs = (y₁ * y₂).abs := by
  rw [Rat.abs_mul x₁ x₂, Rat.abs_mul y₁ y₂, h₁, h₂]

theorem mul_abs₂ (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs = y₂.abs ∧ x₂.abs ≠ 0) : (x₁ * x₂).abs > (y₁ * y₂).abs := by
  obtain ⟨hxy, hx⟩ := h₂
  rw [Rat.abs_mul, Rat.abs_mul]
  rw [<- hxy]
  rw [Rat.mul_comm, Rat.mul_comm (y₁.abs)]
  refine (Rat.mul_lt_mul_left ?_).mpr h₁
  · have : 0 ≤ x₂.abs := abs_nonneg x₂
    exact trichotomy₃ (Ne.symm hx) this

theorem mul_abs₃ (h₁ : x₁.abs > y₁.abs) (h₂ : x₂.abs > y₂.abs) : (x₁ * x₂).abs > (y₁ * y₂).abs := by
  rw [Rat.abs_mul, Rat.abs_mul]
  show y₁.abs * y₂.abs < x₁.abs * x₂.abs
  have : 0 < x₁.abs := lt_of_le_of_lt (abs_nonneg y₁) h₁
  have lt : x₁.abs * y₂.abs < x₁.abs * x₂.abs := (Rat.mul_lt_mul_left this).mpr h₂
  have le : y₁.abs * y₂.abs ≤ x₁.abs * y₂.abs := by
    rw [Rat.mul_comm, Rat.mul_comm x₁.abs]
    have : 0 ≤ y₂.abs := abs_nonneg y₂
    apply Rat.mul_le_mul_left' this
    exact le_of_lt h₁
  exact lt_of_le_of_lt le lt

theorem neg_lt_neg  : a < b → -a > -b :=
  Rat.numDenCasesOn' a fun na da da_nz =>
    Rat.numDenCasesOn' b fun nb db db_nz => by
      intro h
      simp only [Rat.neg_divInt]
      refine (Rat.lt_iff_sub_pos (Rat.divInt (-nb) ↑db) (Rat.divInt (-na) ↑da)).mpr ?_
      have h' := (Rat.lt_iff_sub_pos (Rat.divInt na da) (Rat.divInt nb db)).mp h
      have foo : (db : Int) ≠ 0 := Int.ofNat_ne_zero.mpr db_nz
      have bar : (da : Int) ≠ 0 := Int.ofNat_ne_zero.mpr da_nz
      rw [Rat.divInt_sub_divInt _ _ foo bar] at h'
      rw [Rat.divInt_sub_divInt _ _ bar foo]
      have foo' : (0 : Int) < da := Int.cast_pos' da_nz
      have bar' : (0 : Int) < db := Int.cast_pos' db_nz
      have : ((0 : Int) < da * db) := Int.mul_pos foo' bar'
      rw [Rat.divInt_pos_iff_of_pos_right this]
      have : ((0 : Int) < db * da) := Int.mul_pos bar' foo'
      rw [Rat.divInt_pos_iff_of_pos_right this] at h'
      simp only [Int.neg_mul, Int.sub_neg, gt_iff_lt]
      rw [Int.add_comm, <- Int.sub_eq_add_neg]
      exact h'

theorem neg_le_neg : a ≤ b → -a ≥ -b :=
  Rat.numDenCasesOn' a fun na da da_nz =>
    Rat.numDenCasesOn' b fun nb db db_nz => by
      intro h
      simp only [Rat.neg_divInt]
      refine (Rat.le_iff_sub_nonneg (Rat.divInt (-nb) ↑db) (Rat.divInt (-na) ↑da)).mpr ?_
      have h' := (Rat.le_iff_sub_nonneg (Rat.divInt na da) (Rat.divInt nb db)).mp h
      have foo : (db : Int) ≠ 0 := Int.ofNat_ne_zero.mpr db_nz
      have bar : (da : Int) ≠ 0 := Int.ofNat_ne_zero.mpr da_nz
      rw [Rat.divInt_sub_divInt _ _ foo bar] at h'
      rw [Rat.divInt_sub_divInt _ _ bar foo]
      have foo' : (0 : Int) < da := Int.cast_pos' da_nz
      have bar' : (0 : Int) < db := Int.cast_pos' db_nz
      have : ((0 : Int) < da * db) := Int.mul_pos foo' bar'
      rw [Rat.divInt_nonneg_iff_of_pos_right this]
      have : ((0 : Int) < db * da) := Int.mul_pos bar' foo'
      rw [Rat.divInt_nonneg_iff_of_pos_right this] at h'
      simp only [Int.neg_mul, Int.sub_neg, ge_iff_le]
      rw [Int.add_comm, <- Int.sub_eq_add_neg]
      exact h'

theorem int_tight_lb {i : Int} (h : i > c) : i ≥ c.floor + 1 := by
  cases Int.lt_trichotomy i (c.floor + 1) with
  | inl iltc =>
    have ilec := (Int.lt_iff_add_one_le).mp iltc
    have h2 : i ≤ c.floor := by exact (Int.add_le_add_iff_right 1).mp iltc
    have c_le_floor := Rat.floor_le_self c
    have : i ≤ c := Rat.le_trans (Rat.cast_le.mp h2) c_le_floor
    have abs := Rat.lt_of_le_of_lt this h
    apply False.elim
    exact Rat.lt_irrefl _ abs
  | inr h' =>
    cases h' with
    | inl ieqc => exact Int.le_of_eq (id (Eq.symm ieqc))
    | inr igtc => exact Int.le_of_lt igtc

theorem floor_neg : Rat.floor (-a) = -Rat.ceil' a := by
  simp [Rat.ceil']

theorem int_tight_ub {i : Int} (h : i < c) : i ≤ c.ceil' - 1 := by
  have h' := Rat.neg_lt_neg h
  have i_le_floor_neg_c := int_tight_lb h'
  rw [floor_neg] at i_le_floor_neg_c
  have pf := Int.neg_le_neg i_le_floor_neg_c
  simp [Int.add_comm, Int.neg_add] at pf
  rw [Int.add_comm] at pf
  rw [Int.sub_eq_add_neg]
  exact pf

theorem lt_eq_sub_lt_zero : (a < b) = (a - b < 0) := by
  apply propext
  rw [Rat.lt_iff_sub_pos]
  constructor
  · intro h
    have h' := Rat.neg_lt_neg h
    rw [Rat.neg_sub] at h'
    exact h'
  · intro h
    have h' := Rat.neg_lt_neg h
    simp at h'
    rw [Rat.neg_sub] at h'
    exact h'

theorem le_eq_sub_le_zero : (a ≤ b) = (a - b ≤ 0) := by
  apply propext
  constructor
  · intro h
    have h' := (Rat.add_le_add_left (c := -b)).mpr h
    rw [Rat.add_comm, Rat.add_comm (-b) b] at h'
    simp [Rat.add_neg_self, <- Rat.sub_eq_add_neg] at h'
    exact h'
  · intro h
    have h' := (Rat.add_le_add_left (c := b)).mpr h
    rw [Rat.sub_eq_add_neg, Rat.add_comm, Rat.add_assoc, Rat.neg_self_add] at h'
    simp [Rat.add_zero] at h'
    exact h'

theorem eq_eq_sub_eq_zero : (a = b) = (a - b = 0) := by
  apply propext
  constructor
  · intro h; rw [h]; simp
  · intro h
    have h' := congrArg (fun z => z + b) h
    simp [Rat.zero_add, Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_self_add, Rat.add_zero] at h'
    exact h'

theorem ge_eq_sub_ge_zero : (a ≥ b) = (a - b ≥ 0) := by
  apply propext
  exact Rat.le_iff_sub_nonneg b a

theorem gt_eq_sub_gt_zero : (a > b) = (a - b > 0) := by
  apply propext
  exact Rat.lt_iff_sub_pos b a

theorem lt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_lt_mul_left hc]
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem mul_sign₁ : a < 0 → b < 0 → a * b > 0 :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz ha =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz hb => by
      have : 0 < a_den := Nat.zero_lt_of_ne_zero a_den_nz
      have a_den_pos : (0 : Int) < a_den := Int.ofNat_pos.mpr this
      have a_num_neg : a_num < 0 := (Rat.divInt_neg_iff_of_neg_right a_den_pos).mp ha
      have : 0 < b_den := Nat.zero_lt_of_ne_zero b_den_nz
      have b_den_pos : (0 : Int) < b_den := Int.ofNat_pos.mpr this
      have b_num_neg : b_num < 0 := (Rat.divInt_neg_iff_of_neg_right b_den_pos).mp hb
      have bar : (a_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr a_den_nz
      have bar' : (b_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr b_den_nz
      rw [Rat.divInt_mul_divInt _ _ bar bar']
      have : 0 < (a_den : Int) * b_den := Int.mul_pos a_den_pos b_den_pos
      apply (Rat.divInt_pos_iff_of_pos_right this).mpr
      exact Int.mul_pos_of_neg_of_neg a_num_neg b_num_neg

theorem mul_sign₃ : a < 0 → b > 0 → a * b < 0 :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz ha =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz hb => by
      have : 0 < a_den := Nat.zero_lt_of_ne_zero a_den_nz
      have a_den_pos : (0 : Int) < a_den := Int.ofNat_pos.mpr this
      have a_num_neg : a_num < 0 := (Rat.divInt_neg_iff_of_neg_right a_den_pos).mp ha
      have : 0 < b_den := Nat.zero_lt_of_ne_zero b_den_nz
      have b_den_pos : (0 : Int) < b_den := Int.ofNat_pos.mpr this
      have b_num_neg : 0 < b_num := (Rat.divInt_pos_iff_of_pos_right b_den_pos).mp hb
      have bar : (a_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr a_den_nz
      have bar' : (b_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr b_den_nz
      rw [Rat.divInt_mul_divInt _ _ bar bar']
      have : 0 < (a_den : Int) * b_den := Int.mul_pos a_den_pos b_den_pos
      apply (Rat.divInt_neg_iff_of_neg_right this).mpr
      exact Int.mul_neg_of_neg_of_pos a_num_neg b_num_neg

theorem mul_sign₄ (ha : a > 0) (hb : b < 0) : a * b < 0 := by
  rw [Rat.mul_comm]
  exact mul_sign₃ hb ha

theorem le_mul_of_lt_of_le (a b : Rat) : a < 0 → b ≤ 0 → 0 ≤ a * b := by
  intros h1 h2
  cases (Rat.le_iff_eq_or_lt b 0).mp h2 with
  | inl heq => rw [heq, Rat.mul_zero]; exact rfl
  | inr hlt => have := mul_sign₁ h1 hlt; exact le_of_lt this

theorem nonpos_of_mul_nonneg (a b : Rat) : a < 0 → 0 ≤ a * b → b ≤ 0 := by
  intros h1 h2
  apply Classical.byContradiction
  intro h3
  have : 0 < b := (Rat.not_nonpos _).mp h3
  have : a * b < 0 := mul_sign₃ h1 this
  have := Rat.lt_of_lt_of_le this h2
  exact Rat.lt_irrefl _ this

theorem neg_of_mul_pos (a b : Rat) : a < 0 → 0 < a * b → b < 0 := by
  intros h1 h2
  apply Classical.byContradiction
  intro h3
  have : 0 ≤ b := Rat.not_lt.mp h3
  cases (Rat.le_iff_eq_or_lt 0 b).mp this with
  | inl heq => rw [<-heq, Rat.mul_zero] at h2; exact Rat.lt_irrefl _ h2
  | inr hlt => have := mul_sign₃ h1 hlt; have := Rat.lt_trans h2 this; exact Rat.lt_irrefl _ this

theorem le_iff_sub_nonneg' (x y : Rat) : y ≤ x ↔ y - x ≤ 0 := by
  rw [Rat.le_iff_sub_nonneg]
  rw [Rat.nonneg_iff_sub_nonpos]
  rw [Rat.neg_sub]

theorem lt_iff_sub_pos' (x y : Rat) : y < x ↔ y - x < 0 := by
  rw [Rat.lt_iff_sub_pos]
  rw [Rat.pos_iff_neg_nonpos]
  rw [Rat.neg_sub]

theorem lt_of_sub_eq_neg' {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) → (b₁ < b₂) := by
  intro h2
  have := (Rat.lt_iff_sub_pos' a₂ a₁).mp h2
  have : 0 < c₁ * (a₁ - a₂) := mul_sign₁ hc₁ this
  rw [h] at this
  have := neg_of_mul_pos c₂ (b₁ - b₂) hc₂ this
  exact (lt_iff_sub_pos' b₂ b₁).mpr this

theorem lt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  apply propext
  constructor
  · exact lt_of_sub_eq_neg' hc₁ hc₂ h
  · intro h2
    exact lt_of_sub_eq_neg' (c₁ := c₂) (c₂ := c₁) (a₁ := b₁) (a₂ := b₂) (b₁ := a₁) (b₂ := a₂) hc₂ hc₁ (Eq.symm h) h2

theorem le_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, Rat.mul_le_mul_left hc]
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero b₁, ← this hc₁, ← this hc₂, h]

theorem le_of_sub_eq_neg' {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) → (b₁ ≤ b₂) := by
  intro h2
  have := (Rat.le_iff_sub_nonneg' a₂ a₁).mp h2
  have : 0 ≤ c₁ * (a₁ - a₂) := le_mul_of_lt_of_le c₁ (a₁ - a₂) hc₁ this
  rw [h] at this
  have := nonpos_of_mul_nonneg c₂ (b₁ - b₂) hc₂ this
  exact (Rat.le_iff_sub_nonneg' b₂ b₁).mpr this

theorem le_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  apply propext
  constructor
  · exact le_of_sub_eq_neg' hc₁ hc₂ h
  · intro h2
    exact le_of_sub_eq_neg' (c₁ := c₂) (c₂ := c₁) (a₁ := b₁) (a₂ := b₂) (b₁ := a₁) (b₂ := a₂) hc₂ hc₁ (Eq.symm h) h2

theorem eq_of_sub_eq {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  apply propext
  apply Iff.intro
  · intro ha
    rw [ha] at h
    simp at h
    have := Rat.mul_eq_zero_left hc₂ (Eq.symm h)
    rw [eq_eq_sub_eq_zero]
    exact this
  · intro hb
    rw [hb] at h
    simp at h
    have := Rat.mul_eq_zero_left hc₁ h
    rw [eq_eq_sub_eq_zero]
    exact this

theorem ge_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, ge_iff_le, Rat.mul_le_mul_left hc]
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero b₁, ← this hc₁, ← this hc₂, h]

theorem mul_neg (a b : Rat) : a * (-b) = - (a * b) :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz => by
      rw [Rat.divInt_mul_divInt _ _ (Int.ofNat_ne_zero.mpr a_den_nz) (Int.ofNat_ne_zero.mpr b_den_nz)]
      rw [Rat.neg_divInt]
      rw [Rat.divInt_mul_divInt _ _ (Int.ofNat_ne_zero.mpr a_den_nz) (Int.ofNat_ne_zero.mpr b_den_nz)]
      rw [Int.mul_neg, Rat.neg_divInt]

theorem neg_eq {a b : Rat} : -a = -b → a = b := by
  intro h
  have h' := congrArg (fun z => -z) h
  simp only [Rat.neg_neg] at h'
  exact h'

theorem ge_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  show (a₂ ≤ a₁) = (b₂ ≤ b₁)
  rw [<- Rat.neg_sub, <- Rat.neg_sub (x := b₂) (y := b₁), mul_neg, mul_neg] at h
  have h' := neg_eq h
  exact le_of_sub_eq_neg hc₁ hc₂ h'

theorem gt_of_sub_eq_pos {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have {c x y : Rat} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) := by
    rw (config := { occs := .pos [1] }) [← Rat.mul_zero c, gt_iff_lt, Rat.mul_lt_mul_left hc]
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero b₁, ← this hc₁, ← this hc₂, h]

theorem gt_of_sub_eq_neg {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  show (a₂ < a₁) = (b₂ < b₁)
  rw [<- Rat.neg_sub, <- Rat.neg_sub (x := b₂) (y := b₁), mul_neg, mul_neg] at h
  have h' := neg_eq h
  exact lt_of_sub_eq_neg hc₁ hc₂ h'

theorem lt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_lt]
  exact lt_of_sub_eq_pos hc₁ hc₂ h

theorem lt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_lt]
  exact lt_of_sub_eq_neg hc₁ hc₂ h

theorem le_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_le]
  exact le_of_sub_eq_pos hc₁ hc₂ h

theorem le_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_le]
  exact le_of_sub_eq_neg hc₁ hc₂ h

theorem eq_of_sub_eq_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_eq]
  exact eq_of_sub_eq hc₁ hc₂ h

theorem ge_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_ge]
  exact ge_of_sub_eq_pos hc₁ hc₂ h

theorem ge_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_ge]
  exact ge_of_sub_eq_neg hc₁ hc₂ h

theorem gt_of_sub_eq_pos_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_gt]
  exact gt_of_sub_eq_pos hc₁ hc₂ h

theorem gt_of_sub_eq_neg_int_left {a₁ a₂ : Int} {b₁ b₂ c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * ↑(a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_gt]
  exact gt_of_sub_eq_neg hc₁ hc₂ h

theorem lt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_lt]
  exact lt_of_sub_eq_pos hc₁ hc₂ h

theorem lt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_lt]
  exact lt_of_sub_eq_neg hc₁ hc₂ h

theorem le_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_le]
  exact le_of_sub_eq_pos hc₁ hc₂ h

theorem le_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_le]
  exact le_of_sub_eq_neg hc₁ hc₂ h

theorem eq_of_sub_eq_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ ≠ 0) (hc₂ : c₂ ≠ 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_eq]
  exact eq_of_sub_eq hc₁ hc₂ h

theorem ge_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_ge]
  exact ge_of_sub_eq_pos hc₁ hc₂ h

theorem ge_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_ge]
  exact ge_of_sub_eq_neg hc₁ hc₂ h

theorem gt_of_sub_eq_pos_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_gt]
  exact gt_of_sub_eq_pos hc₁ hc₂ h

theorem gt_of_sub_eq_neg_int_right {a₁ a₂ : Rat} {b₁ b₂ : Int} {c₁ c₂ : Rat} (hc₁ : c₁ < 0) (hc₂ : c₂ < 0) (h : c₁ * (a₁ - a₂) = c₂ * ↑(b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  rw [Rat.intCast_sub] at h
  rw [Rat.cast_gt]
  exact gt_of_sub_eq_neg hc₁ hc₂ h

theorem mul_sign₆ : a > 0 → b > 0 → a * b > 0 :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz ha =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz hb => by
      have : 0 < a_den := Nat.zero_lt_of_ne_zero a_den_nz
      have a_den_pos : (0 : Int) < a_den := Int.ofNat_pos.mpr this
      have a_num_pos : 0 < a_num := (Rat.divInt_pos_iff_of_pos_right a_den_pos).mp ha
      have : 0 < b_den := Nat.zero_lt_of_ne_zero b_den_nz
      have b_den_pos : (0 : Int) < b_den := Int.ofNat_pos.mpr this
      have b_num_pos : 0 < b_num := (Rat.divInt_pos_iff_of_pos_right b_den_pos).mp hb
      have bar : (a_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr a_den_nz
      have bar' : (b_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr b_den_nz
      rw [Rat.divInt_mul_divInt _ _ bar bar']
      have : 0 < (a_den : Int) * b_den := Int.mul_pos a_den_pos b_den_pos
      apply (Rat.divInt_pos_iff_of_pos_right this).mpr
      exact Int.mul_pos a_num_pos b_num_pos

theorem Int.square_pos {i : Int} : i ≠ 0 → 0 < i * i := by
  intro h
  cases Int.lt_or_lt_of_ne h with
  | inl h' => exact Int.mul_pos_of_neg_of_neg h' h'
  | inr h' => exact Int.mul_pos h' h'

theorem mul_sign₀ : a ≠ 0 → a * a > 0 :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz ha => by
    have : a_num ≠ 0 := (Rat.mkRat_ne_zero a_den_nz).mp ha
    have : 0 < a_num * a_num := Int.square_pos this
    have bar : (a_den : Int) ≠ (0 : Int) := Int.ofNat_ne_zero.mpr a_den_nz
    have foo : (0 : Int) < a_den * a_den := Int.square_pos bar
    rw [Rat.divInt_mul_divInt _ _ bar bar]
    exact (Rat.divInt_pos_iff_of_pos_right foo).mpr this

theorem mul_sign₂ (ha : a < 0) (hb : b ≠ 0) : a * b * b < 0 := by
  have := mul_sign₀ hb
  rw [Rat.mul_assoc]
  exact mul_sign₃ ha this

theorem mul_sign₅ (ha : a > 0) (hb : b ≠ 0) : a * b * b > 0 := by
  have := mul_sign₀ hb
  rw [Rat.mul_assoc]
  exact mul_sign₆ ha this

theorem mul_pos_lt (h : c > 0 ∧ a < b) : c * a < c * b := by
  have ⟨h1, h2⟩ := h
  exact (Rat.mul_lt_mul_left h1).mpr h2

theorem mul_pos_le (h : c > 0 ∧ a ≤ b) : c * a ≤ c * b := by
  have ⟨h1, h2⟩ := h
  exact (Rat.mul_le_mul_left h1).mpr h2

theorem mul_pos_gt (h : c > 0 ∧ a > b) : c * a > c * b := mul_pos_lt h

theorem mul_pos_ge (h : c > 0 ∧ a ≥ b) : c * a ≥ c * b := mul_pos_le h

theorem mul_pos_eq (h : c > 0 ∧ a = b) : c * a = c * b := by rw [h.2]

theorem mul_neg_lt : (c < 0 ∧ a < b) → c * a > c * b :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz =>
      Rat.numDenCasesOn' c fun c_num c_den c_den_nz => by
        rintro ⟨h1, h2⟩
        rw [Rat.divInt_mul_divInt _ _ (Int.ofNat_ne_zero.mpr c_den_nz) (Int.ofNat_ne_zero.mpr a_den_nz)]
        rw [Rat.divInt_mul_divInt _ _ (Int.ofNat_ne_zero.mpr c_den_nz) (Int.ofNat_ne_zero.mpr b_den_nz)]
        have c_den_pos : (0 : Int) < c_den := Int.cast_pos' c_den_nz
        have a_den_pos : (0 : Int) < a_den := Int.cast_pos' a_den_nz
        have b_den_pos : (0 : Int) < b_den := Int.cast_pos' b_den_nz
        have : c_num < 0 := (Rat.divInt_neg_iff_of_neg_right c_den_pos).mp h1
        have h3 := (Rat.divInt_lt_divInt a_den_pos b_den_pos).mp h2
        have ca_pos : (0 : Int) < c_den * a_den := Int.mul_pos c_den_pos a_den_pos
        have cb_pos : (0 : Int) < c_den * b_den := Int.mul_pos c_den_pos b_den_pos
        show (Rat.divInt (c_num * b_num) (↑c_den * ↑b_den) < Rat.divInt (c_num * a_num) (↑c_den * ↑a_den))
        rw [(Rat.divInt_lt_divInt cb_pos ca_pos)]
        have c_num_neg : c_num < 0 := (Rat.divInt_neg_iff_of_neg_right c_den_pos).mp h1
        rw [Int.mul_assoc, Int.mul_assoc]
        apply Int.mul_lt_mul_of_neg_left _ c_num_neg
        rw [Int.mul_comm, Int.mul_comm b_num (c_den * a_den)]
        rw [Int.mul_assoc, Int.mul_assoc]
        apply Int.mul_lt_mul_of_pos_left _ c_den_pos
        rw [Int.mul_comm, Int.mul_comm a_den b_num]
        exact h3

theorem mul_neg_gt (h : c < 0 ∧ a > b) : c * a < c * b := mul_neg_lt h

theorem mul_neg_eq (h : c < 0 ∧ a = b) : c * a = c * b := by rw [h.2]

theorem Int.mul_le_mul_of_neg_left {a b c : Int} (h : b ≤ a) (hc : c < 0) : c * a ≤ c * b :=
  match Int.le_iff_eq_or_lt.mp h with
  | Or.inl heq => by rw [heq]; exact Int.le_refl (c * a)
  | Or.inr hlt => by have := Int.mul_lt_mul_of_neg_left hlt hc; exact Int.le_of_lt this

theorem Int.mul_le_mul_of_pos_left {a b c : Int} (h : a ≤ b) (hc : 0 < c) : c * a ≤ c * b :=
  match Int.le_iff_eq_or_lt.mp h with
  | Or.inl heq => by rw [heq]; exact Int.le_refl (c * b)
  | Or.inr hlt => by have := Int.mul_lt_mul_of_pos_left hlt hc; exact Int.le_of_lt this

theorem Rat.neg_mul (a b : Rat) : -a * b = - (a * b) := by
  rw [Rat.mul_comm]
  rw [Rat.mul_neg]
  rw [Rat.mul_comm]

theorem Int.ge_of_mul_le_mul_left_neg {a b c : Int} (w : a * b ≤ a * c) (h : a < 0) : c ≤ b := by
  have w := Int.sub_nonneg_of_le w
  rw [← Int.mul_sub] at w
  have w := Int.ediv_nonpos_of_nonneg_of_nonpos w (Int.le_of_lt h)
  rw [Int.mul_ediv_cancel_left _ (Int.ne_of_lt h)] at w
  exact Int.le_of_sub_nonpos w

theorem Int.mul_le_mul_neg {a b c : Int} (h : a < 0) : a * b ≤ a * c <-> c ≤ b :=
  ⟨fun x => ge_of_mul_le_mul_left_neg x h , fun x => mul_le_mul_of_neg_left x h⟩

theorem Rat.mul_le_mul_of_neg_left (a b c : Rat) : c < 0 -> (a ≤ b <-> c * a ≥ c * b) :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz =>
      Rat.numDenCasesOn' c fun c_num c_den c_den_nz => by
        intro h1
        have : (0 : Int) < c_den := Int.cast_pos' c_den_nz
        have c_num_neg : c_num < 0 := (Rat.divInt_neg_iff_of_neg_right this).mp h1
        clear h1
        have a_den_pos : (0 : Int) < a_den := Int.cast_pos' a_den_nz
        have b_den_pos : (0 : Int) < b_den := Int.cast_pos' b_den_nz
        have c_den_pos : (0 : Int) < c_den := Int.cast_pos' c_den_nz
        have a_den_nz' : (a_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr a_den_nz
        have b_den_nz' : (b_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr b_den_nz
        have c_den_nz' : (c_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr c_den_nz
        have ca_den_pos : (0 : Int) < c_den * a_den := Int.mul_pos this a_den_pos
        have cb_den_pos : (0 : Int) < c_den * b_den := Int.mul_pos this b_den_pos
        rw [Rat.divInt_le_divInt a_den_pos b_den_pos]
        rw [Rat.divInt_mul_divInt _ _ c_den_nz' a_den_nz']
        rw [Rat.divInt_mul_divInt _ _ c_den_nz' b_den_nz']
        show a_num * ↑b_den ≤ b_num * ↑a_den ↔ Rat.divInt _ _ ≤ Rat.divInt _ _
        rw [Rat.divInt_le_divInt cb_den_pos ca_den_pos]
        rw [Int.mul_assoc, Int.mul_assoc]
        rw [Int.mul_le_mul_neg c_num_neg]
        rw [Int.mul_comm a_num (c_den * b_den)]
        rw [Int.mul_comm b_num (c_den * a_den)]
        rw [Int.mul_assoc, Int.mul_assoc]
        constructor
        · intro h2; rw [Int.mul_comm b_den a_num, Int.mul_comm a_den b_num]; exact Int.mul_le_mul_of_pos_left h2 this
        · intro h2; rw [Int.mul_comm a_num b_den, Int.mul_comm b_num a_den]; exact Int.le_of_mul_le_mul_left h2 this

theorem mul_neg_le (h : c < 0 ∧ a ≤ b) : c * a ≥ c * b := (Rat.mul_le_mul_of_neg_left a b c h.1).mp h.2

theorem mul_neg_ge (h : c < 0 ∧ a ≥ b) : c * a ≤ c * b :=
  mul_neg_le h

theorem mul_tangent_mp_lower (h : x * y ≤ b * x + a * y - a * b)
  : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b := by
  apply Classical.or_iff_not_imp_right.mpr
  have h := Rat.add_le_add_left (c := (- b * x)).mpr h
  rw [Rat.sub_eq_add_neg] at h
  rw [Rat.add_assoc (b * x)] at h
  rw [<- Rat.add_assoc (-b * x) (b * x) (a * y + -(a * b))] at h
  rw [Rat.neg_mul] at h
  rw [Rat.neg_self_add] at h
  rw [Rat.zero_add] at h
  rw [<- Rat.neg_mul, Rat.mul_comm] at h
  rw [<- Rat.mul_add x (-b) y] at h
  rw [<- Rat.mul_neg] at h
  rw [<- Rat.mul_add] at h
  rw [Rat.add_comm] at h
  rw [<- Rat.sub_eq_add_neg] at h
  intro h2
  have h2 := Classical.not_and_iff_not_or_not.mp h2
  rw [Rat.not_le, Rat.not_le] at h2
  cases h2 with
  | inl h2 =>
    constructor
    · exact le_of_lt h2
    · apply Classical.byContradiction
      intro h3
      rw [Rat.not_le] at h3
      have h3 := (Rat.lt_iff_sub_pos' _ _).mp h3
      rw [Rat.mul_comm, Rat.mul_comm a _] at h
      have := (Rat.mul_le_mul_of_neg_left _ _ _ h3).mpr h
      have := Rat.lt_of_lt_of_le h2 this
      exact Rat.lt_irrefl _ this
  | inr h2 =>
    rw [and_comm]
    constructor
    · exact le_of_lt h2
    · apply Classical.byContradiction
      intro h3
      rw [Rat.not_le] at h3
      rw [Rat.mul_comm, Rat.mul_comm a _] at h
      have : 0 < y - b := (Rat.lt_iff_sub_pos b y).mp h2
      rw [Rat.mul_le_mul_left this] at h
      exact Rat.lt_irrefl _ (Rat.lt_of_le_of_lt h h3)

theorem mul_tangent_mpr_lower (h : x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b)
  : x * y ≤ b * x + a * y - a * b := by
  rw [<- Rat.add_le_add_left (c := -b * x)]
  rw [Rat.sub_eq_add_neg]
  rw [Rat.add_assoc (b * x)]
  rw [<- Rat.add_assoc (-b * x) (b * x) (a * y + -(a * b))]
  rw [Rat.neg_mul]
  rw [Rat.neg_self_add]
  rw [Rat.zero_add]
  rw [<- Rat.neg_mul, Rat.mul_comm]
  rw [<- Rat.mul_add x (-b) y]
  rw [<- Rat.mul_neg]
  rw [<- Rat.mul_add]
  rw [Rat.add_comm]
  rw [<- Rat.sub_eq_add_neg]
  rw [Rat.mul_comm, Rat.mul_comm a _]
  cases h with
  | inl h =>
    have ⟨h1, h2⟩ := h
    have : 0 ≤ y - b := (Rat.le_iff_sub_nonneg b y).mp h2
    cases (Rat.le_iff_eq_or_lt _ _).mp this with
    | inl eq => rw [<- eq]; simp only [Rat.zero_mul, ge_iff_le]; rfl
    | inr lt => rw [Rat.mul_le_mul_left lt]; exact h1
  | inr h =>
    have ⟨h1, h2⟩ := h
    have : y - b ≤ 0 := (le_iff_sub_nonneg' b y).mp h2
    cases (Rat.le_iff_eq_or_lt _ _).mp this with
    | inl eq => rw [eq]; simp only [Rat.zero_mul, ge_iff_le]; rfl
    | inr lt => show (y - b) * a ≥ (y - b) * x; rw [<- Rat.mul_le_mul_of_neg_left a x _ lt]; exact h1

theorem mul_tangent_lower :
  x * y ≤ b * x + a * y - a * b ↔ x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b :=
  ⟨mul_tangent_mp_lower, mul_tangent_mpr_lower⟩

theorem mul_tangent_lower_eq
  : (x * y ≤ b * x + a * y - a * b) = (x ≤ a ∧ y ≥ b ∨ x ≥ a ∧ y ≤ b) :=
  propext (mul_tangent_lower)

theorem mul_tangent_mp_upper (h : x * y ≥ b * x + a * y - a * b)
  : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b := by
  apply Classical.or_iff_not_imp_right.mpr
  have h := Rat.add_le_add_left (c := (- b * x)).mpr h
  rw [Rat.sub_eq_add_neg (b * x + a * y) _] at h
  rw [Rat.add_assoc (b * x)] at h
  rw [<- Rat.add_assoc (-b * x) (b * x) (a * y + -(a * b))] at h
  rw [Rat.neg_mul] at h
  rw [Rat.neg_self_add] at h
  rw [Rat.zero_add] at h
  rw [<- Rat.neg_mul b, Rat.mul_comm (-b) x] at h
  rw [<- Rat.mul_add x (-b) y] at h
  rw [<- Rat.mul_neg] at h
  rw [<- Rat.mul_add] at h
  rw [Rat.add_comm (-b) y] at h
  rw [<- Rat.sub_eq_add_neg] at h
  rw [Rat.mul_comm, Rat.mul_comm x _] at h
  intro h2
  have h2 := Classical.not_and_iff_not_or_not.mp h2
  rw [Rat.not_le, Rat.not_le] at h2
  cases h2 with
  | inl h2 =>
    constructor
    · exact le_of_lt h2
    · apply Classical.byContradiction
      intro h3
      rw [Rat.not_le] at h3
      have : 0 < y - b := (Rat.lt_iff_sub_pos b y).mp h3
      rw [Rat.mul_le_mul_left this] at h
      exact Rat.lt_irrefl _ (Rat.lt_of_lt_of_le h2 h)
  | inr h2 =>
    constructor
    · have : y - b < 0 := by exact (lt_iff_sub_pos' b y).mp h2
      exact (Rat.mul_le_mul_of_neg_left _ _ _ this).mpr h
    · exact le_of_lt h2

theorem mul_tangent_mpr_upper (h : x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b)
  : x * y ≥ b * x + a * y - a * b := by
  show _ ≤ _
  rw [<- Rat.add_le_add_left (c := -b * x)]
  show _ ≥ _
  rw [Rat.sub_eq_add_neg (b * x + a * y) _]
  rw [Rat.add_assoc (b * x)]
  rw [<- Rat.add_assoc (-b * x) (b * x) (a * y + -(a * b))]
  rw [Rat.neg_mul]
  rw [Rat.neg_self_add]
  rw [Rat.zero_add]
  rw [<- Rat.neg_mul, Rat.mul_comm]
  rw [<- Rat.mul_add x (-b) y]
  rw [<- Rat.mul_neg]
  rw [<- Rat.mul_add]
  rw [Rat.add_comm]
  rw [<- Rat.sub_eq_add_neg]
  rw [Rat.mul_comm, Rat.mul_comm a _]
  cases h with
  | inl h =>
    have ⟨h1, h2⟩ := h
    cases (Rat.le_iff_eq_or_lt y b).mp h2 with
    | inl eq => rw [eq]; simp only [Rat.sub_self, Rat.zero_mul, ge_iff_le]; rfl
    | inr lt =>
      have : y - b < 0 := (lt_iff_sub_pos' b y).mp lt
      exact (Rat.mul_le_mul_of_neg_left x a (y - b) this).mp h1
  | inr h =>
    have ⟨h1, h2⟩ := h
    cases (Rat.le_iff_eq_or_lt b y).mp h2 with
    | inl eq => rw [eq]; simp only [Rat.sub_self, Rat.zero_mul, ge_iff_le]; rfl
    | inr lt =>
      have : 0 < y - b := (Rat.lt_iff_sub_pos b y).mp lt
      show _ ≤ _
      rw [Rat.mul_le_mul_left this]
      exact h1

theorem mul_tangent_upper
  : x * y ≥ b * x + a * y - a * b ↔ x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b :=
  ⟨mul_tangent_mp_upper, mul_tangent_mpr_upper⟩

theorem mul_tangent_upper_eq
  : (x * y ≥ b * x + a * y - a * b) = (x ≤ a ∧ y ≤ b ∨ x ≥ a ∧ y ≥ b) :=
  propext (mul_tangent_upper)

end Smt.Reconstruct.Rat

namespace Smt.Reconstruct.Rat.Rewrite

open Function

-- https://github.com/cvc5/cvc5/blob/main/src/theory/arith/rewrites

variable {t s x : Rat}

theorem div_total_zero : t / 0 = 0 :=
  Rat.div_def t 0 ▸ Rat.inv_zero.symm ▸ Rat.mul_zero t

-- Eliminations

theorem elim_gt : (t > s) = ¬(s ≥ t) :=
  propext Rat.not_le.symm
theorem elim_lt : (t < s) = ¬(t ≥ s) :=
  propext Rat.not_le.symm
theorem elim_leq : (t ≤ s) = (s ≥ t) :=
  propext ge_iff_le

theorem geq_norm1 : (t ≥ s) = (t - s ≥ 0) := by
  rw [←elim_leq, ←elim_leq, Rat.le_iff_sub_nonneg _ _]

theorem eq_elim : (t = s) = (t ≥ s ∧ t ≤ s) := by
  apply propext
  rw [←elim_leq, And.comm]
  exact Rat.le_antisymm_iff _ _

theorem eq_conflict {t : Int} {c : Rat} (hcc : (↑c.floor = c) = False) : (t = c) = False := by
  simp only [eq_iff_iff, iff_false]
  intro htc
  have hcc : c.floor < c := ((Rat.le_iff_eq_or_lt c.floor c).mp (Rat.floor_le_self c)).resolve_left hcc.mp
  cases Int.lt_trichotomy t c.floor <;> rename_i htcf
  · have hntc : ↑t ≠ c := (Rat.lt_iff_le_and_ne.mp (Rat.lt_trans (Rat.cast_lt2 htcf) hcc)).right
    contradiction
  · cases htcf <;> rename_i htcf
    · simp_all
    · have h : c < t := by
        apply @Rat.lt_of_lt_of_le _ _ _
        · exact Rat.self_le_floor_add_one c
        · exact Rat.cast_le2 htcf
      simp_all [Rat.lt_irrefl]

theorem geq_tighten {t : Int} {c : Rat} {cc : Int} (hc : (↑c.floor = c) = False) (hcc : cc = Int.addN [c.floor, 1]) : (t ≥ c) = (t ≥ cc) := by
  have Int.floor_lt {z : Int} {a : Rat} : a.floor < z ↔ a < ↑z := by
    have ha := Rat.floor_le_self a
    apply Iff.intro
    · intro hz
      have ha' := Rat.self_le_floor_add_one a
      apply Rat.lt_of_lt_of_le ha'
      exact Rat.cast_le2 hz
    · intro hz
      have hlt := Rat.lt_of_le_of_lt ha hz
      exact Rat.cast_lt1 hlt
  simp only [hcc, Int.addN, ge_iff_le, eq_iff_iff, Rat.le_iff_eq_or_lt, ← Int.floor_lt]
  have h : ↑t ≠ c := by simpa [Eq.symm] using eq_conflict hc
  apply Iff.intro <;> intro hct
  · have h := hct.resolve_left h.symm
    omega
  · omega

-- Absolute value comparisons

theorem abs_eq : (x.abs = y.abs) = (x = y ∨ x = -y) := by
  cases hx : decide (x < 0) <;> cases hy : decide (y < 0) <;> simp_all [Rat.abs]
  <;> try simp [Rat.not_lt] at hx hy <;> try intro H <;> try rw [H] at hx
  · have hx':= Rat.neg_le_neg hx
    simp at hx'
    have : y = 0 := by
      apply Rat.le_antisymm hx' hy
    simp [this]
  · exfalso; exact (Rat.lt_irrefl y) (Rat.lt_of_lt_of_le hy hx)
  · constructor <;> (intro H; try rw [H] at hx)
    · apply Or.inr
      rw [← Rat.neg_neg y] at H
      exact Rat.neg_eq H
    · cases H with
      | inl H => rw [H] at hx; exfalso
                 exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt hy hx)
      | inr H => rw [← Rat.neg_neg x] at H
                 exact Rat.neg_eq H
  · constructor
    · intro H; apply Or.inl; exact Rat.neg_eq H
    · intro H; cases H with
      | inl H => exact congrArg Neg.neg H
      | inr H => rw [H] at hx; exfalso
                 have hy' := Rat.pos_of_neg hy
                 exact (Rat.lt_irrefl 0) (Rat.lt_trans hy' hx)

theorem abs_gt : (x.abs > y.abs) = ite (x ≥ 0) (ite (y ≥ 0) (x > y) (x > -y)) (ite (y ≥ 0) (-x > y) (-x > -y)) := by
  (simp only [Rat.abs, gt_iff_lt, ge_iff_le, eq_iff_iff]; split) <;> split <;> split <;> split <;> try simp [Rat.not_lt, Rat.not_le] at *
  case isTrue.isTrue.isTrue.isTrue h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt h4 h1)
  case isTrue.isTrue.isTrue.isFalse h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl x) (Rat.lt_of_lt_of_le h2 h3)
  case isTrue.isTrue.isFalse.isTrue h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl y) (Rat.lt_of_lt_of_le h1 h3)
  case isTrue.isFalse.isTrue.isTrue h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt h3 h1)
  case isTrue.isFalse.isFalse.isTrue h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt h3 h4)
  case isTrue.isFalse.isFalse.isFalse h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl x) (Rat.lt_of_lt_of_le h3 h2)
  case isFalse.isTrue.isTrue.isTrue h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl x) (Rat.lt_of_lt_of_le h1 h2)
  case isFalse.isTrue.isTrue.isFalse h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt h2 h1)
  case isFalse.isTrue.isFalse.isFalse h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt h2 h4)
  case isFalse.isFalse.isTrue.isFalse h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt h2 h4)
  case isFalse.isFalse.isFalse.isTrue h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt h3 h4)
  case isFalse.isFalse.isFalse.isFalse h1 h2 h3 h4 =>
    exfalso; exact (Rat.lt_irrefl 0) (Rat.lt_of_le_of_lt h2 h3)

-- ITE lifting

theorem geq_ite_lift [h : Decidable c] {t s r : Rat} : (ite c t s ≥ r) = ite c (t ≥ r) (s ≥ r) := by
  cases h <;> simp_all

theorem leq_ite_lift [h : Decidable c] {t s r : Rat} : (ite c t s ≤ r) = ite c (t ≤ r) (s ≤ r) := by
  cases h <;> simp_all

-- min/max rules

theorem min_lt1 : (ite (t < s) t s ≤ t) = True := by
  cases h : decide (t < s) <;> simp_all [Rat.not_lt.mp]

theorem min_lt2 : (ite (t < s) t s ≤ s) = True := by
  cases h : decide (t < s) <;> simp_all [Rat.le_of_lt]

theorem max_geq1 : (ite (t ≥ s) t s ≥ t) = True := by
  cases h : decide (t ≥ s) <;> simp_all [Rat.le_of_not_le]

theorem max_geq2 : (ite (t ≥ s) t s ≥ s) = True := by
  cases h : decide (t ≥ s) <;> simp_all

end Smt.Reconstruct.Rat.Rewrite

namespace Smt.Reconstruct.UF

-- https://github.com/cvc5/cvc5/blob/main/src/theory/uf/rewrites

variable {c : Prop} [h : Decidable c] {t s r : α}

-- Equality

theorem eq_refl : (t = t) = True := eq_self t
theorem eq_symm : (t = s) = (s = t) := propext ⟨(· ▸ rfl), (· ▸ rfl)⟩

theorem eq_cond_deq (h : (s = r) = False) : ((t = s) = (t = r)) = (¬t = s ∧ ¬t = r) :=
  propext <| Iff.intro
    (fun hsr => And.intro (fun hts => absurd (hts ▸ hsr ▸ hts) (of_eq_false h))
                          (fun htr => absurd (htr ▸ Eq.symm (hsr ▸ htr)) (of_eq_false h)))
    (fun hnsr => propext ⟨(absurd · hnsr.left), (absurd · hnsr.right)⟩)

theorem eq_ite_lift : (ite c t s = r) = (ite c (t = r) (s = r)) := h.byCases
  (fun hc => if_pos hc ▸ if_pos hc ▸ rfl)
  (fun hnc => if_neg hnc ▸ if_neg hnc ▸ rfl)

theorem distinct_binary_elim : (t ≠ s) = ¬(t = s) := rfl

end Smt.Reconstruct.UF
