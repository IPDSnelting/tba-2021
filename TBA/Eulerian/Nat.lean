open Nat

namespace Nat

theorem zeroSub (a : Nat) : 0 - a = 0 := by
  match a with
  | 0     => rfl
  | a + 1 => simp[Nat.sub_succ, pred, zeroSub a]

theorem subAdd_assoc {a b c : Nat} : a - b - c = a - (b + c) := by
  induction c with
  | zero      => simp
  | succ c ih => rw [add_succ, sub_succ a, ←ih, sub_succ]

@[simp] theorem addSub {a b : Nat} : a + b - b = a := by
  revert a
  induction b with
  | zero => intros; simp
  | succ b h =>
    intros a
    rw [←@Nat.subAdd_assoc (a + succ b) b 1, Nat.add_succ, ←Nat.succ_add]
    rw [h, Nat.sub_succ, Nat.sub_zero]
    rfl

@[simp] theorem succSubOne {a : Nat} : succ a - 1 = a := @addSub a 1

theorem leSuccSubOne {a : Nat} : a ≤ succ (a - 1) :=
 match a with
 | zero => rfl
 | succ a => by simp [Nat.leRefl]

theorem le_subAdd {a b : Nat} (h : b ≤ a) : a = a - b + b := by
  rw [←(le.dest h).2, Nat.add_comm]; simp;

theorem lt_add_right_cancel {m n k : Nat} : m + k > n + k → m > n :=
  match k with
  | zero => fun h => h
  | succ k => fun h => by
    simp only [Nat.add_succ] at h
    exact lt_add_right_cancel (Nat.lt_of_succ_lt_succ h)

theorem lt_add_left_cancel {m n k : Nat} : k + m > k + n → m > n := by
  rw [Nat.add_comm, Nat.add_comm (m := n) (n := k)]; exact lt_add_right_cancel

theorem ltImpLt_of_leImpLe {a b c d : Nat} (h : a ≤ b → c ≤ d) (h' : d < c) : b < a :=
  gtOfNotLe $ fun h'' => Nat.notLeOfGt h' (h h'')


theorem lt_sub_right_cancel {m n k : Nat} : m - k > n - k → m > n := by
  refine ltImpLt_of_leImpLe ?_
  induction k with
  | zero => intro h; rw [Nat.sub_zero, Nat.sub_zero]; exact h
  | succ k ih => intro h; rw [Nat.sub_succ, Nat.sub_succ]; apply predLePred; exact ih h

theorem zeroLtIffSub {a b : Nat} : b < a ↔ a - b > 0 := by
  apply Iff.intro
  case mp =>
    intro h
    apply lt_add_right_cancel (k := b)
    rw [←le_subAdd (Nat.leOfLt h)]
    simp [h]
  case mpr =>
    intro h
    apply lt_sub_right_cancel (k := b)
    rw [Nat.sub_self]
    exact h

theorem neSuccSelf (a : Nat) : a ≠ succ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    intro heq
    apply ih
    apply Nat.add_right_cancel (m := 1)
    exact heq

end Nat
