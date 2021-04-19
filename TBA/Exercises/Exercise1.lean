-- Let's first prove some simple example lemmas with the logical connectives we learned in the lecture.
section
-- Variables in sections determine the type of certain variables for the remainder of the section, saving us a bit of space.
variable (p q r : Prop)

example : p → p := _

example : p → (q → p) := _

-- Note: `→` associates to the right, so the above proposition is equivalent to
-- `p → q → p`

example : (p → False) → (p → q) := _

example : (p ∨ p) → p := _

example : (p → q → r) → (p ∧ q → r) := _

example : (p ∧ q → r) → (p → q → r) := _

example : p → (p → q) → p ∧ q := _

theorem imp_and : (p → q ∧ r) → (p → q) ∧ (p → r) := _

-- Matching on `And.intro` can quickly become tedious, so you can use the following helper functions from now on:
#check And.left
#check And.right

/- BIIMPLICATION -/

-- Biimplication ("if and only if") is written \iff.
-- It is defined as a data type on the constructor
-- Iff.intro : (A → B) → (B → A) → (A ↔ B)
-- Can you recover the proof for A → B by a match expression?

example (hpq : p ↔ q) : (p → q) := _

-- Like for `And`, we have names for both directions of the biimplication:
#check Iff.mp
#check Iff.mpr

-- Prove the following biimplications using the threorem from above!
-- Note: `↔` is defined to bind less tightly than other connectives such as `∧` or `∨`.

theorem iff_and : (p → q ∧ r) ↔ (p → q) ∧ (p → r) := _

theorem or_and : (p ∨ q → r) ↔ (p → r) ∧ (q → r) := _

theorem iff_and_false : False ↔ p ∧ False := _

/- NEGATION -/

-- Negation is defined by ¬ A := (A → False).
-- How is that a good choice? Let us check some basic properties of negation:
theorem imp_not_not : p → ¬¬p := _

example : ¬(p ∧ ¬p) := _

theorem not_or_not : (¬p ∨ ¬q) → ¬(p ∧ q) := _

-- The following ones are a harder to prove. Don't hesitate to skip them or ask your
-- tutors if you get stuck

example : ¬(p ↔ ¬p) := _

example : ¬¬(¬¬p → p) := _


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

theorem not_and : ¬(p ∧ q) → (¬ p ∨ ¬ q) := _

-- Also, we can now deal better with double negations:

example : ¬¬p ↔ p := _

end
