namespace TBA

-- Let's work with some inductive types other than `Nat`!

-- Here is our very own definition of `List`:
inductive List (α : Type) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α

notation  (priority := high) "[" "]" => List.nil   -- `[]`
infixr:67 (priority := high) " :: "  => List.cons  -- `a :: as`

-- as a warmup exercise, let's define concatenation of two lists
def append (as bs : List α) : List α := _

infixl:65 (priority := high) " ++ " => append

example : 1::2::[] ++ 3::4::[] = 1::2::3::4::[] := rfl

-- as with associativity on `Nat`, think twice about what induction variable to use!
theorem append_assoc {as bs cs : List α} : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by

open Decidable

/-
One important special case of `Decidable` is decidability of equalities:
```
abbrev DecidableEq (α : Type) :=
  (a b : α) → Decidable (a = b)

def decEq [s : DecidableEq α] (a b : α) : Decidable (a = b) :=
  s a b
```
Note: `DecidableEq` is defined using `abbrev` instead of `def` because typeclass resolution only
unfolds the former for performance reasons.

Let's try to prove that `List` equality is decidable!
-/
-- hint: Something is still missing. Do we need to assume anything about `α`?
-- hint: Apply `match` case distinctions until the the appropriate `Decidable` constructor is clear,
--   then fill in its proof argument with `by`.
--   We could also do everything in a `by` block, but it's nicer to reserve tactics for proofs so we have
--   more control about the code of programs, i.e. the part that is actually executed
def ldecEq  (as bs : List α) : Decidable (as = bs) := _

-- Let's declare the instance:
instance  : DecidableEq (List α) := _

-- This should now work:
#eval decEq (1::2::[]) (1::3::[])

/-
`DecidabePred` is another convenient abbreviation of `Decidable`
```
abbrev DecidablePred (r : α → Prop) :=
  (a : α) → Decidable (r a)
```
If we have `[DecidablePred p]`, we can e.g. use `if p a then ...` for some `a : α`.

`filter p as` is a simple list function that should remove all elements `a` for which `p a` does not hold.
-/
def filter (p : α → Prop) [DecidablePred p] (as : List α) : List α := _

example : filter (fun x => x % 2 = 0) (1::2::3::4::[]) = 2::4::[] := rfl

variable {p : α → Prop} [DecidablePred p] {as bs : List α}

-- These helper theorems can be useful, also for manual rewriting
@[simp] theorem filter_cons_true (h : p a) : filter p (a :: as) = a :: filter p as :=
  by simp [filter, h]
@[simp] theorem filter_cons_false (h : ¬ p a) : filter p (a :: as) = filter p as :=
  by simp [filter, h]
-- It's worthwhile thinking about what's actually happening here:
-- * first, `filter p (a :: as)` is unfolded to `if p a then a :: filter p as else filter p as`
--   (note that the second `filter` cannot be unfolded)
-- * then `if p a then ...` is rewritten to `if True then ...` using `h`
-- * finally, `if True then a :: filter p as else ...` is rewritten to `a :: filter p as` using
--   the built-in simp theorem `Lean.Simp.ite_True`

-- useful tactic: `byCases h : q` for a decidable proposition `q`
theorem filter_idem : filter p (filter p as) = filter p as := by

theorem filter_append : filter p (as ++ bs) = filter p as ++ filter p bs := by

-- list membership as an inductive predicate:
inductive Mem (a : α) : List α → Prop where
  -- either it's the first element...
  | head {as} : Mem a (a::as)
  -- or it's in the remainder list
  | tail {as} : Mem a as → Mem a (a'::as)

infix:50 " ∈ " => Mem

-- recall that `a ≠ b` is the same as `a = b → False`
theorem mem_of_nonempty_filter (h : ∀ a, p a → a = x) : filter p as ≠ [] → x ∈ as := by

-- This proof is pretty long! Some hints:
-- * If you have an assumption `h : a ∈ []`, you can solve the current goal by `cases h`:
--   since there is no constructor that could possibly match `[]`, there is nothing left to prove!
--   This exclusion of cases, and case analysis on inductive predicates in general,
--   is also called *rule inversion* since we (try to) apply the introduction rules (constructors)
--   "in reverse".
-- * On the other hand, if you try to do case analysis on a proof of e.g. `a ∈ filter p as`,
--   Lean will complain with "dependent elimination failed" since it *doesn't* know yet if
--   the argument `filter p as` is of the form `_ :: _` as demanded by the `Mem` constructors.
--   You need to get the assumption into the shape `_ ∈ []` or `_ ∈ _ :: _` before applying
--   `(no)match/cases` to it.
theorem mem_filter : a ∈ filter p as ↔ a ∈ as ∧ p a := _

-- Here is an alternative definition of list membership via `append`
inductive Mem' (a : α) : List α → Prop where
  | intro (as bs) : Mem' a (as ++ (a :: bs))

infix:50 " ∈' " => Mem'

-- Let's prove that they are equivalent!
theorem mem_mem' : a ∈ as ↔ a ∈' as := _

end TBA
