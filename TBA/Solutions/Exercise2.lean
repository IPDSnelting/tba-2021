section
variable (α : Type) (p q : α → Prop) (r : α → α → Prop)

/- UNIVERSAL QUANTIFICATION -/

-- We can leave off `: α` if Lean can infer it (here via `p`/`q`)
example : (∀ x, p x) → (∀ x, p x → q x) → (∀ x, q x) := 
  fun hp hpq x => hpq x (hp x)

-- The reverse direction of the slides example
example : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := 
  -- for the `⟨...⟩` and `.left/right` notations, see Solutions/Exercise1.lean
  fun hpq => ⟨fun x => And.left (hpq x),
              fun x => (hpq x).right⟩

-- TODO: Prove the corresponding forward/reverse lemma(s) for `∨` (that hold)!
-- hint: input `∀` as `\all`
example : (∀ x, p x) ∨ (∀ x, q x) → (∀ x, p x ∨ q x) :=
  -- We can match multiple terms separated by commas in parallel
  -- Here `fun | ...` is short for `fun h x => match h, x with | ...`
  fun | Or.inl hp, x => Or.inl (hp x)
      | Or.inr hq, x => Or.inr (hq x)

-- We can bind multiple variables in a single `∀`
example : (∀ x y, r x y) → (∀ y x, r x y) := 
  fun h y x => h x y

/- EXISTENTIAL QUANTIFICATION -/

/-
Interestingly, in contrast to the universal quantifier, the existential quantifier is not primitive
but can be specified as an inductive type:
```
inductive Exists (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
```
That is, `Exists.intro` takes/offers a "witness" and a proof that the predicate holds for the witness.
Instead of `Exists (fun x => p x)`, we can also write `∃ x, p x` (input `∃` as `\ex`).
-/

example : (∃ x, p x ∧ q x) → (∃ x, p x) ∧ (∃ x, q x) := 
  fun | Exists.intro x hpq => ⟨Exists.intro x hpq.left, Exists.intro x hpq.right⟩

example : ¬(∃ x, p x) → (∀ x, ¬ p x) := 
  fun h x hp => h ⟨x, hp⟩

example : (∀ x, ¬ p x) → ¬(∃ x, p x) := 
  fun hnotp ⟨x, hpx⟩ => hnotp x hpx

example : (∃ x, ¬ p x) → ¬ (∀ x, p x) := 
  fun ⟨x, hnotpx⟩ hp => hnotpx (hp x)

section
open Classical
-- The following example can only be solved using the classical axioms
-- This one is pretty tricky again, don't feel bad about skipping it
-- hint: use the following helper theorem that can be derived from `em`:
#check byContradiction
-- hint: you may even need to use it more than once
example : ¬(∀ x, p x) → (∃ x, ¬ p x) := 
  fun hnotp => byContradiction (fun h => hnotp (fun x => byContradiction (fun hpx => h ⟨x, hpx⟩)))
end

-- TODO: Decide for yourself what variables you need to model and prove the following
-- important real-world observation, which is sometimes called "drinker paradox":
--   "If there is at least one person in the pub, then there is someone in the pub such that,
--    if (s)he is drinking, then everyone in the pub is drinking."
-- hint: you can define "is in pub" either as a predicate variable on a "Person" type (`(Person : Type)`),
--   or, more simply, directly as a type "Occupant" since we are not interested in persons outside the pub
-- hint: you might need classical logic again
section Drinker

open Classical
-- NOTE: instead of `(∃ p : Occupant, True)`, the equivalent simple `Occupant` could also be used
example (Occupant : Type) (drinking : Occupant → Prop) : (∃ p : Occupant, True) →
    ∃ p, drinking p → ∀ p', drinking p' :=
  fun ⟨p, _⟩ => match em (∃ p', ¬ drinking p') with
    | Or.inl ⟨p', hp'nodrink⟩ => ⟨p', fun hp'drink => False.elim (hp'nodrink hp'drink)⟩
    | Or.inr h => ⟨p, fun hpdrink p' => byContradiction (fun hp'nodrink => h ⟨p', hp'nodrink⟩)⟩

end Drinker

/- EQUALITY -/

example : ∀ a b c : α, a = b → b = c → a = c := 
  fun a b c hab hbc => hab ▸ hbc

example : ∀ a : α, ∃ b : α, b = a := 
  fun a => ⟨a, rfl⟩

-- "`Eq` is the least reflexive relation"
example : (∀ a, r a a) → (∀ a b, a = b → r a b) := 
  fun hrrefl a b hab =>
    hab ▸ hrrefl a

end
