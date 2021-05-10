/- TACTICS -/

namespace TBA

-- definitions from last week
-- NOTE: We renamed it from `Nat'` for consistency. The new namespace makes sure we don't use the
-- standard library `Nat`.
inductive Nat : Type
  | zero : Nat
  | succ (n : Nat) : Nat

open Nat

def add (m n : Nat) : Nat :=
  match n with
  | zero   => m
  | succ n => succ (add m n)

-- With this command we add a notation for `add`. From now on we will be able to write `m + n` for
-- `add m n`. The 65 denotes how strongly the operator should bind to what's adjacent to it.
-- The `priority` means that Lean will prefer it over the built-in `+`.
infix:65 (priority := high) " + " => add

def mul (m n : Nat) : Nat :=
  match n with
  | zero   => zero
  | succ n => (mul m n) + m

-- We also want a notation for `mul`, with a higher binding strength than addition so that
-- `a + b * c` means `a + (b * c`)`.
infix:70 (priority := high) " * " => mul

inductive LE : Nat → Nat → Prop where
  | refl (n : Nat) : LE n n
  | succ : LE m n → LE m (succ n)

-- lower binding strength than either addition or multiplication
infix:50 (priority := high) " ≤ " => LE

-- Let's start by reproving some theorems from last week, but this time with tactics!
-- useful tactics:
-- * `induction ... with ...`
-- * `simp only [f]` to unfold applications of a function `f`
-- * `rw [h]` to rewrite every `a` to `b` if `h : a = b`
-- * `apply/exact`
-- * `simp/simp_all`... are powerful and basically always useful, though make sure that you could also
--   do the proof without them
theorem zero_add : zero + n = n := by
  induction n with
  | zero      =>
    rfl
    -- same as
    --exact rfl
  | succ n ih =>
    simp only [add]
    rw [ih]
    -- or
    --simp [add, ih]
  -- or simply
  --induction n <;> simp_all [add]
  

theorem le_add : m ≤ m + n := by
  induction n with
  | zero =>
    apply LE.refl
    -- same as
    --exact LE.refl _
  | succ n ih =>
    simp only [add]  -- optional, but helpful
    apply LE.succ
    apply ih
    -- same as
    --exact LE.succ ih
    -- alternatively, simply use
    --simp [add, LE.succ, ih]
    -- ...but using a conditional simp theorem like `LE.succ` is usually not obvious
    -- when first writing a proof
  -- or simply
  --induction n <;> simp_all [LE.refl, LE.succ, add]
  

-- Alright, let's start automating more!
attribute [simp] add mul
-- These definitions will now automatically be unfolded when you use `simp/simp_all`


theorem add_succ : (succ n) + m = succ (n + m) := by
  induction m <;> simp_all [zero_add]

-- This one is a bit more tricky, you might need to prove a helper lemma!
theorem add_comm : n + m = m + n := by
  induction n with
  | zero      => simp [zero_add]
  | succ n ih => simp [add_succ, ih]
  

-- Associativity can be proven in a similar way.
theorem add_assoc : (m + n) + k = m + (n + k) := by
  induction k with
  | zero      => rfl
  | succ k ih => simp [add_succ, ih]
  

def one := succ zero

theorem mul_one : m * one = m := by
  simp [zero_add]

-- To prove associativity of multiplication, you might have to come up with
-- some more lemmas about multiplication first. Some are similar to the above laws of
-- addition, some use both addition and multiplication ("distributivity" is the keyword).

theorem left_distrib : m * (n + k) = (m * n) + (m * k) := by
  induction k with
  | zero      => simp
  | succ k ih =>
    simp only [mul]
    rw [ih, ←add_assoc]
    -- NOTE: We *could* also use `add_assoc` as a simp theorem here.
    -- ```
    --  | succ n ih => simp [add_succ, ih, add_assoc]
    -- ```
    -- This even works with `add_comm` since `simp` is clever enough to avoid
    -- permutating applicable terms endlessly! However, such general simp theorems
    -- are best avoided for performance reasons and unintended interactions with
    -- other simp theorems.


theorem mul_assoc : (m * n) * k = m * (n * k) := by 
  induction k with
  | zero      => rfl
  | succ k ih => simp [ih, left_distrib]
  

-- Remember the structures for semigroups and monoids which we defined last week?
structure Semigroup (α : Type) where
  mul   : α → α → α
  assoc : mul (mul a b) c = mul a (mul b c)

structure Monoid (α : Type) extends Semigroup α where
  e     : α
  e_mul : mul e a = a
  mul_e : mul a e = a


theorem one_mul : one * m = m := by
  induction m with
  | zero      => rfl
  | succ m ih => simp [ih]

-- You should now be able to instantiate two of them,  including proofs!
def Nat_add_Monoid : Monoid Nat := 
  { mul := add,
    assoc := add_assoc,
    e := zero,
    e_mul := by intros; simp [zero_add]
    mul_e := by intros; rfl }
  

def Nat_mul_Monoid : Monoid Nat := 
  { mul := mul,
    assoc := mul_assoc,
    e := one,
    e_mul := one_mul,
    mul_e := mul_one }
  
