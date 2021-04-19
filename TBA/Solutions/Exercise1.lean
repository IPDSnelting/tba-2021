-- Let's first prove some simple example lemmas with the logical connectives we learned in the lecture.
section
-- Variables in sections determine the type of certain variables for the remainder of the section, saving us a bit of space.
variable (p q r : Prop)

example : p → p := 
  fun h => h

example : p → (q → p) := 
  fun hp => fun hq => hp -- similarly to the note below, we can elide parentheses around the inner `fun`

-- Note: `→` associates to the right, so the above proposition is equivalent to
-- `p → q → p`

example : (p → False) → (p → q) := 
  fun hnp hp => nomatch hnp hp  -- we can also combine nested `fun`s

example : (p ∨ p) → p := 
  fun hpp => match hpp with
    | Or.inl hp => hp
    | Or.inr hp => hp

example : (p → q → r) → (p ∧ q → r) := 
  fun h hpq => match hpq with
    | And.intro hp hq => h hp hq

example : (p ∧ q → r) → (p → q → r) := 
  fun h hp hq => h (And.intro hp hq)

example : p → (p → q) → p ∧ q := 
  -- For inductive types with a single constructor `I.c`, we can also use the
  -- *anonymous constructor* notation `⟨e, ...⟩` instead of `I.c e...`.
  -- Input `⟨` and `⟩` as `\<` and `\>`.
  fun hp h => ⟨hp, h hp⟩

theorem imp_and : (p → q ∧ r) → (p → q) ∧ (p → r) := 
  fun h => ⟨fun hp => match h hp with | And.intro hq hr => hq,
            fun hp => match h hp with | And.intro hq hr => hr⟩

-- Matching on `And.intro` can quickly become tedious, so you can use the following helper functions from now on.
#check And.left
#check And.right

/- BIIMPLICATION -/

-- Biimplication ("if and only if") is written \iff.
-- It is defined as a data type on the constructor
-- Iff.intro : (A → B) → (B → A) → (A ↔ B)
-- Can you recover the proof for A → B by a match expression?

example (hpq : p ↔ q) : (p → q) := 
  match hpq with
  | ⟨hmp, _⟩ => hmp
-- Note that we didn't have to give the second argument on the left side of `=>` since we do not use it.

-- Like for `And`, we have names for both directions of the biimplication:
#check Iff.mp
#check Iff.mpr

-- Prove the following biimplications using the threorem from above!
-- Note: `↔` is defined to bind less tightly than other connectives such as `∧` or `∨`.

theorem iff_and : (p → q ∧ r) ↔ (p → q) ∧ (p → r) := 
  -- If `h : p ∧ q`, we can also write `h.left` as a shorthand for `And.left h`.
  -- In general, if a term `e` has some type `A` and `A.f : A → ...` is a function,
  -- then `e.f` is a shorthand for `A.f e`.
  ⟨fun hpqr => ⟨fun hp => (hpqr hp).left, fun hp => (hpqr hp).right⟩,
   -- We can use "infallible" patterns such as anonymous constructors directly in place of a `fun` binder name
   -- This feature is a good way to make proofs shorter.
   fun ⟨hpq, hpr⟩ hp => ⟨hpq hp, hpr hp⟩⟩

theorem or_and : (p ∨ q → r) ↔ (p → r) ∧ (q → r) := 
  ⟨fun hpqr => ⟨fun hp => hpqr (Or.inl hp), fun hq => hpqr (Or.inr hq)⟩,
   fun hprqr =>
     -- `fun | ...` is short for `fun x => match x with | ...`
     fun
     | Or.inl hp => hprqr.left hp
     | Or.inr hq => hprqr.right hq⟩

theorem iff_and_false : False ↔ p ∧ False := 
  ⟨fun fa => nomatch fa, fun h => h.right⟩

/- NEGATION -/

-- Negation is defined by ¬ A := (A → False).
-- How is that a good choice? Let us check some basic properties of negation:
theorem imp_not_not : p → ¬¬p := 
  fun hp hnp => hnp hp

example : ¬(p ∧ ¬p) := 
  fun h => h.right h.left

theorem not_or_not : (¬p ∨ ¬q) → ¬(p ∧ q) := 
  fun hor ⟨hp, hq⟩ =>
    match hor with
    | Or.inl hnp => hnp hp
    | Or.inr hnq => hnq hq

-- The following ones are a harder to prove. Don't hesitate to skip them or ask your
-- tutors if you get stuck

example : ¬(p ↔ ¬p) := 
  fun h =>
    -- We can use `have` for a sub-proof so we don't have to repeat ourselves.
    -- `have` is generally nicer to use than `let` in the case of propositions.
    -- We have updated the slides to reflect this.
    have hp : p := h.2 (fun hp => h.1 hp hp)
    h.1 hp hp
-- Did you see that we used `.1` and `.2` instead of `.mp` and `.mpr`?
-- For single-constructor inductive types we can also use numbers to refer to their "fields", i.e. to
-- the arguments of the constructor.

example : ¬¬(¬¬p → p) := 
  fun nnnpp => nnnpp fun nnp => False.elim (nnp (fun hp => nnnpp fun _ => hp))
-- Using `False.elim` instead of `nomatch` makes for better output during the construction of the proof.
-- We have updated the slides to reflect this.

/- CLASSICAL AXIOMS -/

-- Some tautologies about negation cannot be proven by just assuming the logical
-- connectives as algebraic propositions. Instead, we need to assume these facts
-- as axioms. To have access to these, we need to open a namespace called "Classical".
-- We will learn more about constructive versus classical logic in week 5.
open Classical

-- The following statement is called the _law of excluded middle_.
-- It is assumed as an axiom, which means that it doesn't have to be proved.

#check em p

-- Now use the law of excluded middle to show that the theorem not_or_not is reversible:

theorem not_and : ¬(p ∧ q) → (¬ p ∨ ¬ q) := 
  fun hn =>
  match em p with
  | Or.inl hp  =>
    match em q with
    | Or.inl hq  => False.elim (hn ⟨hp, hq⟩)
    | Or.inr hnq => Or.inr hnq
  | Or.inr hnp => Or.inl hnp
-- You can see in the structure of this proof that what we are doing is just making
-- iterated case distinctions on the truth value of propositions.
-- As such, the above proof is the equivalent of a proof "by truth" table, where we are listing all the possible
-- combinations.

-- Also, we can now deal better with double negations:

example : ¬¬p ↔ p := 
  ⟨fun hnnp =>
   match em p with
   | Or.inl hp => hp
   | Or.inr hnp => False.elim (hnnp hnp),
   imp_not_not p⟩
-- The proof of the first direction is what you know as "proof by contradiction":
-- To prove a proposition `p`, we match on `em p`. Then, the first case is always trivial,
-- and in the second case we will have to use `False.elim` to show that now we have contradicting
-- premises.
-- You will need this principle in the second exercise sheet as well.

end
