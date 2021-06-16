/- Eulerian circuits -/

/- 
We provide you with a formalization of some facts about lists being equal up to permutation and
lists being sublists of their permutation
-/
import TBA.Eulerian.List

-- If a simp has to be turned to a simp only. :D
--set_option trace.Meta.Tactic.simp true 

open List

namespace Eulerian

-- We model graphs as lists of pairs on a type with decidable equality.
variable {α : Type} (E : List (α × α)) [DecidableEq α]

def isNonEmpty : Prop := E.length > 0 -- This is a Test

instance : Decidable (isNonEmpty E) := inferInstanceAs (Decidable (E.length > 0))

-- Now it's your turn to fill out the following definitions and prove the characterization!

def path (E : List (α × α)) : Prop := match E with
  | [] => True
  | cons (a,b) [] => True 
  | cons (a,b) (cons (c,d) E) => if b = c then path (cons (c,d) E) else False

def first (E : List (α × α)) : (h : isNonEmpty E) → α := by
  intro h 
  cases E with 
    | nil => simp [isNonEmpty] at h
    | cons e E => exact e.1

theorem lastIndexValid (E : List (α × α)) (h : isNonEmpty E) : length E - 1 < length E := by
  cases E with 
    | nil => cases h
    | cons _ E' => 
      simp only [List.length_cons, Nat.succSubOne]
      show length E' + 1 ≤ Nat.succ (length E') 
      rw [Nat.add_succ, Nat.add_zero]
      apply Nat.leRefl

def last (E : List (α × α)) : (h : isNonEmpty E) → α := by 
  intro h
  let h' := lastIndexValid E h 
  exact (E.get (E.length - 1) h').2 

def circuit (E : List (α × α)) : Prop := 
  if h : isNonEmpty E
  then path E ∧ first E h = last E h 
  else True -- Debatable if it should return True. For our purposes probably better.

-- inverted edge
def inverse (e : α × α) : α × α := (e.2, e.1)

-- returns graph with undirected edges, i.e. for (a,b) (b,a) is inserted.
def undirected (E : List (α × α)) : List (α × α) := match E with 
  | [] => []
  | e::E => e::(inverse e)::(undirected E)

def reachable (E : List (α × α)) (a b : α) : Prop := 
  if a = b 
  then True 
  else ∃ p : List (α × α), ∃ h : isNonEmpty p, p ⊆ E ∧ path p ∧ first p h = a ∧ last p h = b 

def bridge (E : List (α × α)) (a : (α × α)) : Prop := ¬ reachable (E.erase a) a.1 a.2

def isWeaklyConnected (E : List (α × α)) : Prop := ∀ a b : α, reachable (undirected E) a b

def isStronglyConnected (E : List (α × α)) : Prop := ∀ a b : α, reachable E a b  

def inDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ fun e => e.2 = a).length

def outDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ fun e => e.1 = a).length

def hasEqualInOutDegrees (E : List (α × α)) : Prop := ∀ a : α, inDegree E a = outDegree E a

-- Def. for "C is maximal in E under property p".
def maximal (E C : List (α × α)) (p : List (α × α) → Prop): Prop := C ⊆ E ∧ p C ∧ ∀ C' : List (α × α), C' ⊆ E → C ⊆ C' → C ≠ C' → ¬(p C')

def weakComponent (E C : List (α × α)) : Prop := maximal E C (isWeaklyConnected)

def strongComponent (E C : List (α × α)) : Prop := maximal E C (isStronglyConnected)

def isEulerian (E : List (α × α)) : Prop := ∃ E' : List (α × α), E' ≃ E ∧ circuit E'

def preList (E E' : List (α × α)) : Prop := ∃ E'' : List (α × α), E = E' ++ E'' 

theorem prePath (E E' : List (α × α)) : preList E E' → path E → path E' := by 
  induction E with 
  | nil => 
    intro h h' 
    have h'' : E' = [] := _    
  | cons e E' ih => 
    intro h h' 
    _ 
    
def insert (E : List (α × α)) (e : α × α) (n : Nat) : List (α × α) := 
  if n = 0
  then e :: E
  else match E with 
    | [] => [e]
    | cons e' E' => e' :: insert E' e (n-1)

#eval insert [(1,2),(2,3)] (5,4) 1

-- Returns longest prefix of elements that satisfy p.
def takeWhile (p : α → Bool) : List α → List α 
| [] => []
| a::l => match p a with 
  | true => a::(takeWhile p l)
  | false => []

-- sanity check
#eval takeWhile (fun a => a < 3) [1,2,3,5,8]  

-- Given path from a to b, returns path without edge (b,a). 
def pathNonRedundant (P : List (α × α)) (hp : path P) (hpne : isNonEmpty P) (hne : first P hpne ≠ last P hpne) : List (α × α) :=   
  let e := (last P hpne, first P hpne)
  takeWhile (fun e' => e ≠ e') P 

-- somewhat sanity check
#eval takeWhile (fun e' => (1,2) ≠ e') [(2,3), (3,4), (4,1), (1,2), (2,1)]

theorem contraposition : (p → q) → (¬q → ¬p) := fun hpq hnq hp => hnq $ hpq hp  


theorem pathNRNonEmpty (P : List (α × α)) (hp : path P) (hpne : isNonEmpty P) (hne : first P hpne ≠ last P hpne) : 
isNonEmpty $ pathNonRedundant P hp hpne hne := by 
  match P with 
  | nil => cases hpne 
  | cons e' P' => 
    have h : first (e' :: P') hpne = e'.1 := by simp [first] 
    have h' : e' = (e'.1, e'.2) := by simp [Prod] 


    /-have h' : (last (e' :: P') hpne, first (e' :: P') hpne) ≠ e' := by 
      suffices last (e' :: P') hpne ≠ e'.1 by 
        intro h 
    -/
    


/-
theorem pathNRNonEmpty (P : List (α × α)) (hp : path P) (hpne : isNonEmpty P) (hne : first P hpne ≠ last P hpne) : 
  isNonEmpty $ pathNonRedundant P hp hpne hne := by 
  let Q := pathNonRedundant P hp hpne hne
  show isNonEmpty Q
  byCases h : isNonEmpty Q 
  case inl => exact h
  case inr => 
    byCases h' : Q.length = 0 
    case inr => 
      let h' : isNonEmpty Q := by 
        simp [h']
         have h'' : Q = [] := length_zero_iff_nil.mpr h' 
    case inl => 
-/    

  --match P with 
  --| [] => 
/-
theorem pathWithoutCycle (P : List (α × α)) (hp : path P) (hpne : isNonEmpty P) : 
first P hpne ≠ last P hpne → ∃ Q : List (α × α), ∃ hqne : isNonEmpty Q, path Q ∧ first P hpne = first Q hqne ∧ last P hpne = last Q hqne := by 
  intro hne 
-/


-- theorem insert_index (E : List (α × α)) (e : α × α) (n : Nat) (h : n < E.length) : (insert E e n).get n h = e := by 

/-
theorem insert_length (E : List (α × α)) (e : α × α) (n : Nat) : (insert E e n).length = E.length + 1 := by
  induction E with 
    | nil => 
      show length (insert [] e n) = 1
      byCases h : n = 0 
      simp [h, insert]
      
      case inl => 
        rw [h]
        have h' : insert nil e 0 = [e] := by
          apply insert 
-/

def insertEdgeAtStart (E : List (α × α)) (a b : α) : List (α × α) :=
  (a, b) :: E

def connectEnds (E : List (α × α)) (h : isNonEmpty E) : List (α × α) :=
  insertEdgeAtStart E (last E h) (first E h)

def removeFirst (E: List (α × α)) (h : isNonEmpty E) : List (α × α) :=
  E.erase (E.get 0 h)

def removeLast (E: List (α × α)) (h : isNonEmpty E) : List (α × α) :=
  E.erase (E.get (E.length - 1) (lastIndexValid E h))

theorem removeLength (E: List (α × α)) (h : isNonEmpty E) : (removeLast E h).length = E.length - 1 := by 
  induction E with 
  | nil => cases h 
  | cons e E ih => 
    _

  -- hier ist wahrscheinlich length_erase_mem hilfreich...

theorem removeLastLengthTwoNonEmpty (E : List (α × α)) (h : E.length ≥ 2) : isNonEmpty (removeLast E (lengthTwoNonEmpty E h)) := by
  _
  
theorem lengthTwoNonEmpty (E : List (α × α)) (h : E.length ≥ 2) : isNonEmpty E := by
  let h' := Nat.succPos 1
  exact Nat.ltOfLtOfLe h' h  
    
def SkipFirst (E : List (α × α)) (h : E.length ≥ 2) : List (α × α) := 
  let a := last E h
  let b := first E h
  insertEdgeAtStart (removeFirst (removeLast E (lengthTwoNonEmpty E h)) (removeLastLengthTwoNonEmpty E h)) a b 

theorem circuitEqualInOut (E : List (α × α)) (h : circuit E) : hasEqualInOutDegrees E := by
  simp [circuit] at h
  simp only [hasEqualInOutDegrees]
  intro a
  byCases h' : isNonEmpty E
  case inl => 
    have hp : path E := by 
      apply h h'
    have hfeql : first E = last E := by 
      apply h h'
    -- hier brauchen wir wahrscheinlich noch ein paar Lemmata, ich komme direkt sonst auf nichts..
  case inr => 
    have hin: inDegree E a = 0 := by
      _
    have hout: outDegree E a = 0 := by
      _

-- List of head ends of edges.
def heads (E : List (α × α)) : List α := map (fun e => e.2) E 

-- List of tail ends of edges.
def tails (E : List (α × α)) : List α := map (fun e => e.1) E 

def breakAt (E : List (α × α)) (h : circuit E) (a : α) (h' : a ∈ heads E) : α := _
  
theorem circuitRotate (E as bs : List (α × α)) (h : circuit E) : E = as++bs → circuit (bs++as) := _

theorem circHeadIffTail (E : List (α × α)) (h : circuit E) (e : α) : e ∈ heads E ↔ e ∈ tails E := by 
constructor 
  focus 
  induction E with 
  | nil => 
    simp [map, heads, tails] 
    intro h' 
    exact h' 
  | cons e' E' ih =>  
    simp [cons] 

theorem circuitRotate (E : List (α × α)) (h : circuit E) (e : α) : 
e ∈ (map (fun (x,y) => x) E) → ∃ E' : List (α × α), ∃ h' : isNonEmpty E', E' ≃ E ∧ e = first E' h'
:= _

theorem Nat.strongRecOn (n : Nat) {C : Nat → Sort u}
  {c : ∀ n, (∀ m, m < n → C m) → C n} : C n := by 
  suffices ∀ l, (∀ m, m < l → C m) by
    have h : n < Nat.succ n := by 
      show Nat.succ n ≤ Nat.succ n 
      apply Nat.leRefl 
    exact this (Nat.succ n) n h 
  intro l
  induction l with 
  | zero => 
    intros m hle 
    let h := (Nat.zeroLtIffSub.mp) hle
    rw [Nat.zeroSub] at h 
    cases h
  | succ l ih => 
    intros m h 
    let h := Nat.leOfLtSucc h 
    match decEq m l with 
    | isTrue h' => 
      rw [h'] 
      exact c l ih 
    | isFalse h' => 
      let h' : m ≠ l := by simp [h'] 
      let h := Nat.ltOfLeAndNe h h' 
      exact ih m h

theorem eulerian_degrees
  (hne : isNonEmpty E)
  (sc : isStronglyConnected E)
  (ed : hasEqualInOutDegrees E)
  : isEulerian E := by 
  induction E.length using Nat.strongRecOn with 
  | _ => _ 
  
  -- show ∀ n : Nat, ∀ E : List (α × α), E.length = n → isEulerian E
  /-
  induction E.length with 
  | zero => _
  | succ n ih => _
  -/
  
  /-
  induction ∀ m : Nat, m ≤ E.length with 
  | zero => _
  | succ n => _
  -/
  

end Eulerian