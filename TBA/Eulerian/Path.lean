/- Eulerian circuits -/

/- 
We provide you with a formalization of some facts about lists being equal up to permutation and
lists being sublists of their permutation
-/
import TBA.Eulerian.List
import TBA.Util.Find 

-- If a simp has to be turned to a simp only. :D
-- set_option trace.Meta.Tactic.simp true 

open List

namespace Eulerian

-- We model graphs as lists of pairs on a type with decidable equality.
variable {α : Type} (E : List (α × α)) [DecidableEq α]

def isNonEmpty : Prop := E.length > 0

instance : Decidable (isNonEmpty E) := inferInstanceAs (Decidable (E.length > 0))

-- Now it's your turn to fill out the following definitions and prove the characterization!

inductive path : List (α × α) → α → α → Prop := 
  | refl : path [] a a 
  | trans (e : (α × α)) (C : List (α × α)) : path C e.2 x → path (e::C) e.1 x 

def first (h : path E a b) : α := a 

def last (h : path E a b) : α := b

def circuit : List (α × α) → α → α → Prop := by 
  intro E a b 
  exact (path E a b) ∧ (a = b)

def reachable (E : List (α × α)) (a b : α) : Prop := 
  ∃ p : List (α × α), ∃ h : isNonEmpty p, p ⊆ E ∧ path p a b 

def isStronglyConnected (E : List (α × α)) : Prop := ∀ a b : α, reachable E a b  

def inDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ fun e => e.2 = a).length

def outDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ fun e => e.1 = a).length

-- returns list of head ends of edges.
def heads (E : List (α × α)) : List α := map (fun e => e.2) E 

-- returns list of tail ends of edges.
def tails (E : List (α × α)) : List α := map (fun e => e.1) E 

def hasEqualInOutDegrees (E : List (α × α)) : Prop := ∀ a : α, inDegree E a = outDegree E a

def isEulerian (E : List (α × α)) : Prop := ∃ E' : List (α × α), ∃ a : α, E' ≃ E ∧ circuit E' a a 

theorem pathNil {p : List (α × α)} {a b : α} (hp : path p a b) : p = [] → a = b := by 
  intro heq 
  rw [heq] at hp
  match hp with 
  | path.refl => rfl 

theorem pathAppend {p q : List (α × α)} {a b c : α} 
  (hp : path p a b) (hq : path q b c) : path (p++q) a c := by 
  induction p generalizing a b with 
  | nil => 
    have heq : a = b := pathNil hp (by rfl) 
    rw [nil_append] 
    rw [← heq] at hq 
    exact hq 
  | cons e p' ih => 
    cases hp with 
    | trans e p' hp' => 
      have h := ih hp' hq
      rw [cons_append]
      exact path.trans e (p'++q) h

-- Inverse to pathAppend.
theorem pathBreak {p q : List (α × α)} {a b c : α}  
  (hpq : path (p++q) a c) : ∃ b : α, path p a b ∧ path q b c := by 
  induction p generalizing a c with 
  | nil => 
    rw [nil_append] at hpq 
    exact ⟨a, path.refl, hpq⟩ 
  | cons e p' ih => 
    rw [cons_append] at hpq 
    cases hpq with 
    | trans _ _ hpq' => 
      have ⟨b, hp', hq⟩ := ih hpq' 
      exact ⟨b, path.trans e p' hp', hq⟩ 

theorem pathLastEdge {p : List (α × α)} {e : (α × α)} {a b : α} 
  (hp : path (e::p) a b) : ∃ x : α × α, x ∈ e::p ∧ x.2 = b := by 
  induction p generalizing e a b with 
  | nil => 
    cases hp with 
    | trans _ _ hp' => 
      have heq := pathNil hp' $ rfl 
      exact ⟨e, Mem.head e [], heq⟩ 
  | cons e' p' ih => 
    cases hp with 
    | trans _ _ hp' => 
      have ⟨x, hin, heq⟩ := ih hp'
      exact ⟨x, Mem.tail x e (e'::p') hin, heq⟩ 

end Eulerian