section
variable (α : Type) (p q : α → Prop) (r : α → α → Prop)

/- UNIVERSAL QUANTIFICATION -/

-- We can leave off `: α` if Lean can infer it (here via `p`/`q`)
example : (∀ x, p x) → (∀ x, p x → q x) → (∀ x, q x) := 
  fun hp hpq x => hpq x (hp x)

-- The reverse direction of the slides example
example : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := 
  fun hpq => ⟨fun x => (hpq x).left, fun x => (hpq x).right⟩ 

-- TODO: Prove the corresponding forward/reverse lemma(s) for `∨` (that hold)!
-- hint: input `∀` as `\all`

example : (∀ x, p x) ∨ (∀ x, q x) → (∀ x, p x ∨ q x) := 
  fun
  | Or.inl hp => fun x => Or.inl (hp x)
  | Or.inr hq => fun x => Or.inr (hq x)

-- Die andere Richtung (∀ x, p x ∨ q x) → (∀ x, p x) ∨ (∀ x, q x) funktioniert im Allgemeinen nicht:
-- Mit q = ¬p gilt die Aussage bspw. links zwar immer (unter dem Law of excluded middle), aber die rechte Aussage muss nicht zwingend gelten.
-- Sehr gut!

-- We can bind multiple variables in a single `∀`
example : (∀ x y, r x y) → (∀ y x, r x y) := 
  fun hr hy hx => hr hx hy

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
  fun | Exists.intro hx hpq => ⟨Exists.intro hx hpq.left, Exists.intro hx hpq.right⟩ 

example: ¬(∃ x, p x) → (∀ x, ¬ p x) := 
  fun hnp x px => hnp (Exists.intro x px)

example : (∀ x, ¬ p x) → ¬(∃ x, p x) := 
  fun all => fun | Exists.intro x px => (all x) px

example : (∃ x, ¬ p x) → ¬ (∀ x, p x) := 
  fun | Exists.intro x px => fun all => px (all x)

section
open Classical
-- The following example can only be solved using the classical axioms
-- This one is pretty tricky again, don't feel bad about skipping it
-- hint: use the following helper theorem that can be derived from `em`:
#check byContradiction
-- hint: you may even need to use it more than once

theorem allex : ¬(∀ x, p x) → (∃ x, ¬ p x) := 
  fun all =>
    let h1 : ¬(∃ x, ¬ p x) → (∀ x, p x) := fun hnnp hx => 
      byContradiction fun npx => hnnp (Exists.intro hx npx)
    let h2 : ¬(∃ x, ¬ p x) → False := fun hxnp => all (h1 hxnp)
    byContradiction h2    
-- Um dieses Theorem wiederzuverwenden, habe ich ihm einen Namen gegeben

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

-- So hat dein Pub genau zwei Gäste. Gemeint hatten wir eigentlich eher `variable (Occupant : Type)`, dann ist es
-- ein beliebiger Typ von Gästen des Pubs.
inductive Occupant : Type where
  | drinker : Occupant
  | nodrinker : Occupant

-- Auch hier wäre entsprechend ein beliebiges Prädikat `variable (drinks : Occupant → Prop)` allgemeiner gewesen.
def drinks : Occupant → Prop := fun w =>
  match w with
  | Occupant.drinker => true
  | Occupant.nodrinker => false
  
-- Diese Variablen brauchst du nicht, weil das Theorem ja keine Freien Variablen hat, d.h. alle Variablennamen werden dort in Quantoren oder
-- Funktionen eingeführt.
--variable (x y z : Occupant) 

theorem DrinkerParadox : (x : Occupant) → (∃ y, drinks y → (∀ z, drinks z)) :=
  fun hx => let hp := (∀ y, drinks y) match em hp with
    | Or.inl h1 => Exists.intro hx (fun hy => h1)
    | Or.inr h0 => match allex Occupant drinks h0 with
      | Exists.intro hy ndy => Exists.intro hy (fun dhy => False.elim (ndy dhy))

end Drinker

/- EQUALITY -/

example : ∀ a b c : α, a = b → b = c → a = c := 
  fun ha hb hc hab => fun | rfl => hab

example : ∀ a : α, ∃ b : α, b = a := 
  fun ha => Exists.intro ha rfl

-- "`Eq` is the least reflexive relation"
example : (∀ a, r a a) → (∀ a b, a = b → r a b) := 
  fun raa ha hb => fun | rfl => raa ha

end
