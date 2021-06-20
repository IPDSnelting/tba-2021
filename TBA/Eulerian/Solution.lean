/- Eulerian circuits -/

/- 
We provide you with a formalization of some facts about lists being equal up to permutation and
lists being sublists of their permutation
-/
import TBA.Eulerian.List

-- If a simp has to be turned to a simp only. :D
-- set_option trace.Meta.Tactic.simp true 

open List

namespace Eulerian

-- We model graphs as lists of pairs on a type with decidable equality.
variable {α : Type} (E : List (α × α)) [DecidableEq α]

def isNonEmpty : Prop := E.length > 0

instance : Decidable (isNonEmpty E) := inferInstanceAs (Decidable (E.length > 0))

-- Now it's your turn to fill out the following definitions and prove the characterization!

def path (E : List (α × α)) : Prop := match E with
  | [] => True
  | cons (a,b) [] => True 
  | cons (a,b) (cons (c,d) E) => if b = c then path (cons (c,d) E) else False

theorem subPath (E : List (α × α)) (h : path E) : ∀ as bs : List (α × α), E = as ++ bs → path as ∧ path bs := by 
  induction E with 
  | nil => 
    intros as bs heq
    match as bs with 
    | nil nil =>  
  | cons e' E' ih => _

-- returns the first vertex of the first edge in a list of edges
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

-- returns the second vertex of the last edge in a list of edges
def last (E : List (α × α)) : (h : isNonEmpty E) → α := by 
  intro h
  let h' := lastIndexValid E h 
  exact (E.get (E.length - 1) h').2 

theorem eENonEmpty (e : (α × α)) (E' : List (α × α)) : isNonEmpty (e :: E') := by
  have h'': ¬(length (e :: E') = 0) := by
        simp [length_cons_ne_zero]
      simp only [isNonEmpty]
      have h''' : length (e :: E') = 0 ∨ length (e :: E') > 0 := by
        apply Nat.eqZeroOrPos (length (e :: E'))
  simp_all [isNonEmpty]

def circuit (E : List (α × α)) : Prop := match E with
  | nil => True
  | cons e E' => e.1 = last (e :: E') (eENonEmpty e E') ∧ path (e :: E')

def reachable (E : List (α × α)) (a b : α) : Prop := 
  if a = b 
  then True 
  else ∃ p : List (α × α), ∃ h : isNonEmpty p, p ⊆ E ∧ path p ∧ first p h = a ∧ last p h = b 

def isStronglyConnected (E : List (α × α)) : Prop := ∀ a b : α, reachable E a b  

def inDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ fun e => e.2 = a).length

def outDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ fun e => e.1 = a).length

-- returns list of head ends of edges.
def heads (E : List (α × α)) : List α := map (fun e => e.2) E 

-- returns list of tail ends of edges.
def tails (E : List (α × α)) : List α := map (fun e => e.1) E 

def hasEqualInOutDegrees (E : List (α × α)) : Prop := ∀ a : α, inDegree E a = outDegree E a

def isEulerian (E : List (α × α)) : Prop := ∃ E' : List (α × α), E' ≃ E ∧ circuit E'

def preList (E E' : List (α × α)) : Prop := ∃ E'' : List (α × α), E = E' ++ E'' 

theorem prePath (E E' : List (α × α)) : preList E E' → path E → path E' := by 
  induction E with 
  intro h h' 
  | nil =>
    simp only [preList] at h
    
  | cons e E'' ih =>
    simp
    
    
-- inserts edge in list at index n (if n is grater than list.length, it inserts it at the end)
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

def connectEnds (E : List (α × α)) (h : isNonEmpty E) : List (α × α) :=
  insert E (last E h, first E h) 0

theorem inDegreeSingle (e : α × α) (a : α) : if a = e.2 then inDegree [e] a = 1 else inDegree [e] a = 0 := _

theorem outDegreeSingle (e : α × α) (a : α) : if a = e.1 then outDegree [e] a = 1 else outDegree [e] a = 0 := _

theorem midPathEqualInOut (E: List (α × α)) (h : isNonEmpty E) (h': path E) : 
  ∀ a : α , ¬(a = first E h) → ¬(a = last E h) → ((inDegree E a) = (outDegree E a)) := by
  intro a nfirst nlast
  induction E with
  | nil => 
    simp_all [inDegree, outDegree]
  | cons e E' ih =>
    byCases loop: e.1 = e.2
    case cons.inl =>
      match E' with
      | nil => 
        have outdeg: outDegree [e] a = 0 := by
          have f: e.1 = first [e] h := by
            simp [first]
          rw [←f] at nfirst
          have outDegreeSingle': if a = e.1 then outDegree [e] a = 1 else outDegree [e] a = 0 := by
            exact outDegreeSingle e a
          simp_all
        have indeg : inDegree [e] a = 0 := by
          have f: e.2 = last [e] h := by
            simp only [last]
            have length: length [e] = 1 := by
              simp
            rfl
          rw [←f] at nlast
          have inDegreeSingle': if a = e.2 then inDegree [e] a = 1 else inDegree [e] a = 0 := by
            exact inDegreeSingle e a
          simp_all
        simp_all [indeg, outdeg]
      | cons e' E'' => 
        have h'': e.2 = e'.1 := by
          -- hier muss vielleicht die Definition von Path doch etwas angepasst werden. Ich schaffe es nicht, 
          -- aus "path (e :: e' :: E'')" zu folgern, dass e.2 = e'.1 gilt, was ja in der Definition steckt..
          

-- to prove theorems from Exersise sheet 1
open Classical

theorem imp_not_not : p → ¬¬p := 
  fun hp hnp => hnp hp

theorem notNot : ¬¬p → p := 
  fun hnnp =>
   match em p with
   | Or.inl hp => hp
   | Or.inr hnp => False.elim (hnnp hnp)

theorem not_and : ¬(p ∧ q) → (¬ p ∨ ¬ q) := 
  fun hn =>
  match em p with
  | Or.inl hp  =>
    match em q with
    | Or.inl hq  => False.elim (hn ⟨hp, hq⟩)
    | Or.inr hnq => Or.inr hnq
  | Or.inr hnp => Or.inl hnp

theorem not_or_not : (¬p ∨ ¬q) → ¬(p ∧ q) := 
  fun hor ⟨hp, hq⟩ =>
    match hor with
    | Or.inl hnp => hnp hp
    | Or.inr hnq => hnq hq

theorem deMorgan' (a b : Prop) : ¬(¬ a ∧ ¬ b) → a ∨ b := by
  intro h
  have h': (¬ ¬ a ∨ ¬ ¬ b) := by
    exact not_and h
  match h' with
  | Or.inl hna => 
    simp_all [notNot]
  | Or.inr hnb =>
    simp_all [notNot]

theorem circuitEqualInOut1 (E : List (α × α)) (h : circuit E) : hasEqualInOutDegrees E := by
  simp only [hasEqualInOutDegrees]
  intro a
  simp only [circuit] at h
  match E with
  | nil =>
    simp_all [inDegree, outDegree]
  | cons e E' =>
    have h': e.1 = last (e :: E') (eENonEmpty e E') ∧ path (e :: E') := by
      simp_all [h]
    byCases mid: ¬(a = first (e :: E') (eENonEmpty e E')) ∧ ¬(a = last (e :: E') (eENonEmpty e E'))
    case inl =>
      apply (midPathEqualInOut (e :: E') (eENonEmpty e E') h'.2 a mid.1 mid.2)
    case inr =>
      have firstlast: a = e.1 ∧ a = last (e :: E') (eENonEmpty e E') := by
        have firstOrlast: a = e.1 ∨ a = last (e :: E') (eENonEmpty e E') := by
          exact deMorgan' (a = e.1) (a = last (e :: E') (eENonEmpty e E')) mid
        simp_all
      _
      
      
-- strong recursion, not sure if we still need it.
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

-- Theorem that a subgraph always has at most as many edges as E.
theorem permSubLtLength {C E : List (α × α)} (hsub : C ⊆ E) : length C ≤ length E := by 
  have h := permEqvToEraseAppend hsub 
  have h' := permEqvLength h 
  rw [length_append] at h'
  rw [h']
  exact Nat.leAddLeft (length C) (length (E -l C))

-- If a graph is not Eulerian, all of its circuit have a smaller length.
theorem notEulerianNoEqCircuit (hne : ¬isEulerian E) 
  : ∀ C : List (α × α), C ⊆ E ∧ circuit C → C.length < E.length := by 
  intro C hall
  byCases h : C ≃ E 
  case inl => 
    have heulerian : isEulerian E := Exists.intro C (And.intro h hall.right) 
    cases hne heulerian 
  case inr => 
    have h'' := permSubLtLength hall.left 
    exact Nat.ltOfLeAndNe h'' (contraposition (permEqvOfPermSub hall.left) h)

theorem existenceCircuitWithStartEdge (E : List (α × α)) (e : (α × α)) (h : e ∈ E) (ed : hasEqualInOutDegrees E)  
  : ∃ C : List (α × α), (e::C) ⊆ E ∧ circuit (e::C) := _ 

theorem existenceCircuit (E : List (α × α)) (hne : isNonEmpty E) (ed : hasEqualInOutDegrees E) 
  : ∃ C : List (α × α), C ⊆ E ∧ circuit C ∧ isNonEmpty C := by 
  match E with 
  | nil => 
    simp only [isNonEmpty] at hne 
    simp_all 
  | cons e E' => 
    let ⟨C, hsub, hcirc⟩ := existenceCircuitWithStartEdge (e::E') e (Mem.head e E') ed 
    exact ⟨e::C, hsub, hcirc, eENonEmpty e C⟩  

-- Definition for when an edge is adjacent to a graph. 
def adjacentEdge (E : List (α × α)) (e : (α × α)) := e.1 ∈ heads E  

-- the actual theorem
theorem eulerian_degrees
  (hne : isNonEmpty E)
  (sc : isStronglyConnected E)
  (ed : hasEqualInOutDegrees E)
  : isEulerian E := by 
    suffices ∀ C : List (α × α), C ⊆ E ∧ circuit C ∧ C.length < E.length 
    → ∃ C' : List (α × α), C' ⊆ E ∧ circuit C' ∧ C.length < C'.length by
      have h : ∀ n : Nat, n < E.length → (∃ C : List (α × α), C ⊆ E ∧ circuit C ∧ n < C.length) := by 
        intro n 
        induction n with 
        | zero => 
          intro _
          exact existenceCircuit E hne ed
        | succ n ih => 
          intro hlt 
          have ⟨C, hsub, hcirc, hltc⟩ := ih $ Nat.ltOfSuccLe $ Nat.leOfLt hlt 
          have hle := permSubLtLength hsub 
          byCases heq : C.length = E.length 
          case inl => 
            rw [← heq] at hlt
            exact ⟨C, hsub, hcirc, hlt⟩ 
          case inr => 
            have ⟨C', hsub', hcirc', hltc'⟩ := this C ⟨hsub, hcirc, Nat.ltOfLeAndNe hle heq⟩ 
            let hltc' := Nat.ltOfLeOfLt (Nat.succLeOfLt hltc) hltc' 
            exact ⟨C', hsub', hcirc', hltc'⟩ 
      have ⟨C, hsub, hcirc, hltc⟩ := h (E.length - 1) $ lastIndexValid E hne 
      have heq := Nat.leAntisymm (permSubLtLength hsub) (Nat.leTrans Nat.leSuccSubOne (Nat.succLeOfLt hltc))
      exact ⟨C, permEqvOfPermSub hsub heq, hcirc⟩ 
    intro C ⟨hsub, hcirc, hlt⟩
    have heqv := permEqvToEraseAppend hsub 
    cases hrest : (E -l C) with 
    | nil => 
      rw [hrest, nil_append] at heqv  
      have heq := permEqvLength heqv 
      rw [heq] at hlt
      cases Nat.ltIrrefl C.length hlt   
    | cons e' E' => 
      have hnempty := eENonEmpty e' E'
      have hAdj : ∃ e e' : (α × α), e ∈ C ∧ e' ∈ (E -l C) ∧ e.2 = e'.1 := by
        byCases houter : ∃ a : α, filter (fun e => e.2 = a) C = [] 
        case inr => 
          have hall := fun a hempty => houter ⟨a, hempty⟩ 
          have hfilter := hall e'.1 
          cases hcfilter : filter (fun e => e.2 = e'.1) C with 
          | nil => cases hfilter hcfilter
          | cons e C' =>
            have hin := Mem.head e C'
            rw [← hcfilter] at hin 
            have hprop := filterProp_of_mem hin
            exact ⟨e, e', mem_of_mem_filter hin, (by rw [hrest]; exact Mem.head e' E'), ofDecideEqTrue hprop⟩ 
        case inl => 
          have ⟨a, hfempty⟩ := houter 

        --byCases houter : ∃ a : α, ∀ e : (α × α), e ∈ C → e.2 ≠ a
        --case inr =>  
        --have hall : ∀ a : α,  := fun 
        --have hall : ∀ a : α, ∃ e : (α × α), e ∈ C ∧ e.2 = a := by 
        --  intro a 
          --¬(∃ x, p x) → (∀ x, ¬ p x) := 
          --fun h x hp => h ⟨x, hp⟩
        --case inl => _
        /-
        byCases hall : ∀ a : α, ∃ e : (α × α), e ∈ C ∧ e.2 = a 
        case inl => 
          have ⟨e, hmem, hadj⟩ := hall e'.1 
          exact ⟨e, e', hmem, (by rw [hrest]; exact Mem.head e' E'), hadj⟩ 
        case inr => 
          have hall : ∃ a : α, ∀ e : (α × α), ¬(e ∈ C ∧ e.2 = a) := by 
        -/
            

    /-
    match (E -l C) with 
    | nil => 
      rw [nil_append] at heqv  
      let heq := permEqvLength heqv 
      rw [heq] at hlt
      cases Nat.ltIrrefl C.length hlt   
    | cons e' E' => 
      let hnezero : ¬0 = (E -l C).length := fun heq => contraposition length_zero_iff_nil.mp hempty heq.symm
      let hnempty : isNonEmpty $ E -l C := Nat.ltOfLeOfNe (Nat.zeroLe (length $ E -l C)) hnezero
    -/
    /-
    byCases hempty : E -l C = [] 
    case inl =>  
      let heqv := permEqvToEraseAppend hsub 
      rw [hempty] at heqv 
      rw [nil_append] at heqv  
      let heq := permEqvLength heqv 
      rw [heq] at hlt
      cases Nat.ltIrrefl C.length hlt   
    case inr => 
      let hnezero : ¬0 = (E -l C).length := fun heq => contraposition length_zero_iff_nil.mp hempty heq.symm
      let hnempty : isNonEmpty $ E -l C := Nat.ltOfLeOfNe (Nat.zeroLe (length $ E -l C)) hnezero
      have hAdj : ∃ e e' : (α × α), e ∈ C ∧ e' ∈ (E -l C) ∧ e.2 = e'.1 := 
        match E -l C with 
        | [] => simp at hempty 
        | cons e' E' => 
         by 
          byCases hall : ∀ a : α, ∃e : (α × α), e ∈ C ∧ e.2 = a 
          case inl => 
            let ⟨e, hmem, hadj⟩ := hall e'
            
            
          --let ⟨e, hmem, hadj⟩ := hall (first (E -l C) hnempty)
    -/
    



/- 
Dinge, deren Nützlichkeit ich noch nicht direkt sehe, aber sicher nicht schlecht sind:

-- Def. for "C is maximal in E under property p".
def maximal (E C : List (α × α)) (p : List (α × α) → Prop): Prop := C ⊆ E ∧ p C ∧ ∀ C' : List (α × α), C' ⊆ E → C ⊆ C' → C ≠ C' → ¬(p C')

def weakComponent (E C : List (α × α)) : Prop := maximal E C (isWeaklyConnected)

def strongComponent (E C : List (α × α)) : Prop := maximal E C (isStronglyConnected)

def bridge (E : List (α × α)) (a : (α × α)) : Prop := ¬ reachable (E.erase a) a.1 a.2

def isWeaklyConnected (E : List (α × α)) : Prop := ∀ a b : α, reachable (undirected E) a b

-- inverted edge
def inverse (e : α × α) : α × α := (e.2, e.1)

-- returns graph with undirected edges, i.e. for (a,b) (b,a) is inserted.
def undirected (E : List (α × α)) : List (α × α) := match E with 
  | [] => []
  | e::E => e::(inverse e)::(undirected E)

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

/-
theorem pathWithoutCycle (P : List (α × α)) (hp : path P) (hpne : isNonEmpty P) : 
first P hpne ≠ last P hpne → ∃ Q : List (α × α), ∃ hqne : isNonEmpty Q, path Q ∧ first P hpne = first Q hqne ∧ last P hpne = last Q hqne := by 
  intro hne 
-/

theorem insert_index (E : List (α × α)) (e : α × α) (n : Nat) (h : n < E.length) : (insert E e n).get n h = e := by 

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
          
def breakAt (E : List (α × α)) (h : circuit E) (a : α) (h' : a ∈ heads E) : α := _
  
theorem circuitRotate (E as bs : List (α × α)) (h : circuit E) : E = as++bs → circuit (bs++as) := _

theorem circuitRotate (E : List (α × α)) (h : circuit E) (e : α) : 
e ∈ (map (fun (x,y) => x) E) → ∃ E' : List (α × α), ∃ h' : isNonEmpty E', E' ≃ E ∧ e = first E' h'
:= _

-- hier glaube ich dass die Aussage bald schnell aus der gefolgert werden kann, dass für einen Kreis der
-- Eingangs- und Ausgangsgrad gleich sind.
theorem circHeadIffTail (E : List (α × α)) (h : circuit E) (e : α) : e ∈ heads E ↔ e ∈ tails E := by
constructor 
  focus 
  induction E with 
  | nil => 
    simp [map, heads, tails] 
    intro h' 
    exact h' 
  | cons e' E' ih =>
    simp [circuit] at h
    _

def removeFirst (E: List (α × α)) (h : isNonEmpty E) : List (α × α) :=
  E.erase (E.get 0 h)

def removeLast (E: List (α × α)) (h : isNonEmpty E) : List (α × α) :=
  E.erase (E.get (E.length - 1) (lastIndexValid E h))
-/

end Eulerian