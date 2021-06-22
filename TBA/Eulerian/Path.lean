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

instance decidableMem [DecidableEq α] (x : α) : (xs : List α) → Decidable (x ∈ xs)
  | [] => isFalse (by intro h; cases h)
  | y :: ys => 
    match decEq x y with
    | isTrue heq => by 
      rw [heq] 
      exact isTrue (Mem.head y ys) 
    | isFalse heq => 
      match decidableMem x ys  with 
      | isTrue hin => isTrue (Mem.tail x y ys hin)
      | isFalse hnin => isFalse (by 
        rw [cons_eq_append] 
        intro hin 
        cases hin with 
        | head x ys => exact heq rfl
        | tail x y ys hin' => cases hnin hin'
      )

-- Now it's your turn to fill out the following definitions and prove the characterization!

inductive path : List (α × α) → α → α → Prop := 
  | refl : path [] a a 
  | trans (e : (α × α)) (C : List (α × α)) : path C e.2 x → path (e::C) e.1 x 

def first (h : path E a b) : α := a 

def last (h : path E a b) : α := b

def circuit : List (α × α) → α → Prop := by 
  intro E a 
  exact path E a a

def reachable (E : List (α × α)) (a b : α) : Prop := 
  ∃ p : List (α × α), p ⊆ E ∧ path p a b 

def isStronglyConnected (E : List (α × α)) : Prop := ∀ a b : α, reachable E a b  

def inDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ fun e => e.2 = a).length

def outDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ fun e => e.1 = a).length

-- returns list of head ends of edges.
def heads (E : List (α × α)) : List α := map (fun e => e.2) E 

-- returns list of tail ends of edges.
def tails (E : List (α × α)) : List α := map (fun e => e.1) E 

def hasEqualInOutDegrees (E : List (α × α)) : Prop := ∀ a : α, inDegree E a = outDegree E a

def isEulerian (E : List (α × α)) : Prop := ∃ E' : List (α × α), ∃ a : α, E' ≃ E ∧ circuit E' a

theorem pathNil {p : List (α × α)} {a b : α} (hp : path p a b) : p = [] → a = b := by 
  intro heq 
  rw [heq] at hp
  match hp with 
  | path.refl => rfl 

-- Generalisation of transitivity: Paths can be concatenated into a bigger path.
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
theorem pathBreak (p q : List (α × α)) {a c : α}  
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

theorem pathCons {p : List (α × α)} {e : (α × α)} {a b : α}  :
  path (e::p) a b → e.1 = a := by 
  intro h 
  cases h with 
  | trans _ _ h' => rfl

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

theorem listSplitUntil (p : (α × α) → Bool) (E : List (α × α)) (e : (α × α)) : 
  e ∈ E ∧ p e → ∃ x : (α × α), ∃ s t : List (α × α), p x ∧ filter p s = [] ∧ E = s++x::t := by 
  intro ⟨hin, hprop⟩ 
  induction E with 
  | nil => 
    cases hin
  | cons e' E ih => 
    byCases h : p e' 
    case inl => 
      exact ⟨e', [], E, h, filter_nil, rfl⟩ 
    case inr => 
      have hneq : ¬ e = e' := by 
        intro heq 
        rw [← heq] at h 
        exact h hprop 
      have hin' : e ∈ E := by 
        rw [cons_eq_append] at hin 
        match mem_append e hin with 
        | (Or.inl h') => 
          cases hneq $ mem_singleton h'
        | (Or.inr h') => 
          exact h'
      have ⟨x, s, t, hprop', hfempty, heq⟩ := ih hin' 
      have h' : filter p (e'::s) = [] := by 
        rw [filter_cons, hfempty] 
        simp [h]
      exact ⟨x, e'::s, t, hprop', h', (by simp [heq, cons_append])⟩ 

theorem permEqvAppend {as bs cs ds : List α} (h : as ≃ bs) (h' : cs ≃ ds) : as++cs ≃ bs++ds := by 
  simp only [isPermEqvTo] 
  intro a 
  simp only [count_append]
  have hcount := h a 
  have hcount' := h' a 
  rw [hcount, hcount']

/- If a circuit contains an adjacent edge to another circuit, we can concatenate them to a bigger circuit. -/
theorem concatCircuit {C C' : List (α × α)} {a b : α} (hcirc : circuit C a) (hcirc' : circuit C' b) : 
  (∃ e : (α × α), e ∈ C ∧ e.2 = b) → ∃ Ccon : List (α × α), circuit Ccon a ∧ Ccon ≃ C++C' := by 
  intro ⟨e, hin, heq⟩ 
  have ⟨s, t, hsplit⟩ := mem_split hin
  have hCpath : path C a a := hcirc
  rw [hsplit] at hCpath 
  have ⟨c, hspath, hetpath⟩ := pathBreak s (e::t) hCpath 
  cases hetpath with 
  | trans _ _ htpath => 
    rw [heq] at htpath 
    have hC'tpath := pathAppend hcirc' htpath 
    rw [← heq] at hC'tpath 
    have heC'tpath := path.trans e (C'++t) hC'tpath 
    have hconpath := pathAppend hspath heC'tpath 
    have heqv : (s ++ e :: (C' ++ t)) ≃ C++C' := by
      simp only [hsplit]
      have hrot := permEqvRotate C' t
      rw [append_assoc, cons_append]
      apply permEqvAppend permEqvRefl
      apply permEqvCons
      assumption
    exact ⟨s ++ e :: (C' ++ t), hconpath, heqv⟩ 

theorem lastIndexValid (E : List (α × α)) (h : isNonEmpty E) : length E - 1 < length E := by
  cases E with 
    | nil => cases h
    | cons _ E' => 
      simp only [List.length_cons, Nat.succSubOne]
      show length E' + 1 ≤ Nat.succ (length E') 
      rw [Nat.add_succ, Nat.add_zero]
      apply Nat.leRefl

theorem eENonEmpty (e : (α × α)) (E' : List (α × α)) : isNonEmpty (e :: E') := by
  have h'': ¬(length (e :: E') = 0) := by
        simp [length_cons_ne_zero]
      simp only [isNonEmpty]
      have h''' : length (e :: E') = 0 ∨ length (e :: E') > 0 := by
        apply Nat.eqZeroOrPos (length (e :: E'))
  simp_all [isNonEmpty]

-- Remove, if only needed in notEulerianNoEqCircuit
theorem contraposition : (p → q) → (¬q → ¬p) := fun hpq hnq hp => hnq $ hpq hp  

theorem circuitEqualInOut (E : List (α × α)) {a : α} (h : circuit E a) : hasEqualInOutDegrees E := by admit 

-- Removing a circuit from a graph with equal in- and out degrees preserves that property.
/- Could be generalized for any subgraph with equal in- and out degrees. -/
theorem removeCircuit (C E : List (α × α)) {a : α} (hsub : C ⊆ E) (ed : hasEqualInOutDegrees E) (hcirc : circuit C a) 
  : hasEqualInOutDegrees $ E -l C := by 
  simp only [hasEqualInOutDegrees, inDegree, outDegree]
  intro a 
  have heqv := permEqvToEraseAppend hsub 
  have hout := permEqvFilter (fun e => e.2 = a) heqv 
  have hin  := permEqvFilter (fun e => e.1 = a) heqv 
  rw [filter_append] at hout
  rw [filter_append] at hin 
  have hout := permEqvLength hout 
  have hin  := permEqvLength hin 
  simp only [length_append] at hout
  simp only [length_append] at hin 
  have heqE := ed a
  simp only [hasEqualInOutDegrees, inDegree, outDegree] at heqE
  rw [hin] at heqE 
  rw [hout] at heqE 
  have heqC := circuitEqualInOut C hcirc 
  simp only [hasEqualInOutDegrees, inDegree, outDegree] at heqC 
  rw [heqC] at heqE 
  exact Nat.add_right_cancel heqE

-- Theorem that a subgraph always has at most as many edges as E.
theorem permSubLtLength {C E : List (α × α)} (hsub : C ⊆ E) : length C ≤ length E := by 
  have h := permEqvToEraseAppend hsub 
  have h' := permEqvLength h 
  rw [length_append] at h'
  rw [h']
  exact Nat.leAddLeft (length C) (length (E -l C))

-- If a graph is not Eulerian, all of its circuit have a smaller length.
theorem notEulerianNoEqCircuit (hne : ¬isEulerian E) {a : α}
  : ∀ C : List (α × α), C ⊆ E ∧ circuit C a → C.length < E.length := by 
  intro C hall
  byCases h : C ≃ E 
  case inl => 
    have heulerian : isEulerian E := ⟨C, a, h, hall.right⟩ 
    cases hne heulerian 
  case inr => 
    have h'' := permSubLtLength hall.left 
    exact Nat.ltOfLeAndNe h'' $ contraposition (permEqvOfPermSub hall.left) h

-- If a graph has equal in- and out degrees and contains an edge e, then there is a circuit starting with e.
theorem existenceCircuitWithStartEdge {E : List (α × α)} {e : (α × α)} (h : e ∈ E) (ed : hasEqualInOutDegrees E)  
  : ∃ C : List (α × α), (e::C) ⊆ E ∧ circuit (e::C) e.1 := by admit 

-- Corollary: If a graph has equal in- and out degrees and is non-empty, that it contains a non-empty circuit.
theorem existenceCircuit (E : List (α × α)) (hne : isNonEmpty E) (ed : hasEqualInOutDegrees E) 
  : ∃ C : List (α × α), ∃ a : α, C ⊆ E ∧ circuit C a ∧ isNonEmpty C := by 
  match E with 
  | nil => 
    simp only [isNonEmpty] at hne 
    simp_all 
  | cons e E' => 
    let ⟨C, hsub, hcirc⟩ := existenceCircuitWithStartEdge (Mem.head e E') ed 
    exact ⟨e::C, e.1, hsub, hcirc, eENonEmpty e C⟩  

-- the actual theorem
theorem eulerian_degrees
  (hne : isNonEmpty E)
  (sc : isStronglyConnected E)
  (ed : hasEqualInOutDegrees E)
  : isEulerian E := by 
  -- It's sufficient to prove that every circuit that isn't already the whole graph can be enlarged.
  suffices ∀ C : List (α × α), ∀ a : α, C ⊆ E ∧ circuit C a ∧ C.length < E.length 
  → ∃ C' : List (α × α), ∃ a' : α, C' ⊆ E ∧ circuit C' a' ∧ C.length < C'.length by
    have h : ∀ n : Nat, n < E.length → (∃ C : List (α × α), ∃ a' : α, C ⊆ E ∧ circuit C a' ∧ n < C.length) := by 
      intro n 
      induction n with 
      | zero => 
        intro _
        exact existenceCircuit E hne ed
      | succ n ih => 
        intro hlt 
        have ⟨C, a, hsub, hcirc, hltc⟩ := ih $ Nat.ltOfSuccLe $ Nat.leOfLt hlt 
        have hle := permSubLtLength hsub 
        byCases heq : C.length = E.length 
        case inl => 
          rw [← heq] at hlt
          exact ⟨C, a, hsub, hcirc, hlt⟩ 
        case inr => 
          have ⟨C', a', hsub', hcirc', hltc'⟩ := this C a ⟨hsub, hcirc, Nat.ltOfLeAndNe hle heq⟩ 
          have hltc' := Nat.ltOfLeOfLt (Nat.succLeOfLt hltc) hltc' 
          exact ⟨C', a', hsub', hcirc', hltc'⟩ 
    have ⟨C, a, hsub, hcirc, hltc⟩ := h (E.length - 1) $ lastIndexValid E hne 
    have heq := Nat.leAntisymm (permSubLtLength hsub) (Nat.leTrans Nat.leSuccSubOne (Nat.succLeOfLt hltc))
    exact ⟨C, a, permEqvOfPermSub hsub heq, hcirc⟩ 
  -- Let C be such a circuit.
  intro C a ⟨hsub, hcirc, hlt⟩
  have heqv := permEqvToEraseAppend hsub 
  cases hrest : (E -l C) with 
  | nil => 
    -- If E -l C is empty, then C can't be a proper subgraph of E.
    rw [hrest, nil_append] at heqv  
    have heq := permEqvLength heqv 
    rw [heq] at hlt
    cases Nat.ltIrrefl C.length hlt   
  | cons e' E' => 
    -- So, w.l.o.g. is E -l C non-empty. 
    -- W.l.o.g. is C also non-empty and can be written as c'::C'.
    /-
      This is important: 
      We want to argue that by sc there is path between an edge in C and one in E -l C. 
      But for that, we must first look at the edge case that C is actually the empty circuit.
    -/
    cases hc : C with 
    | nil => 
      have ⟨C', hsub', hcirc', hltc'⟩ := existenceCircuit E hne ed
      exact ⟨C', hsub', hcirc', (by simp_all [hltc', isNonEmpty])⟩ 
    | cons c' C' => 
      -- There is an edge in E -l C adjacent to C.
      have ⟨x, y, hinC, hinRest, heq⟩ : ∃ e e' : (α × α), e ∈ C ∧ e' ∈ (E -l C) ∧ e.2 = e'.1 := by
        byCases houter : ∃ a : α, filter (fun e => e.2 = a) C = [] 
        case inr => 
        -- If every vertex is in C, then there trivially is such an edge.
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
        -- Case: There is a vertex in the outer of C.
          have ⟨a, hfempty⟩ := houter
          -- There is no edge in C with a as head.
          have hnexist : ¬ ∃ e : (α × α), e ∈ C ∧ e.2 = a := by 
            intro ⟨e, hin, hhead⟩ 
            let p : (α × α) → Bool := fun e => e.2 = a 
            have hprop' : p e = true := decideEqTrue hhead 
            have hfin : e ∈ filter p C := by exact mem_filter_of_prop hin hprop'
            rw [hfempty] at hfin
            simp [mem_nonzeroCount, count_empty] at hfin
          /-
            By strongly connectedness, there must still be a path p from the tail of c' to a.
          -/
          have hreachable := sc c'.2 a
          simp only [reachable] at hreachable 
          have ⟨p, hsub, hpath⟩ := hreachable 
          cases p with 
          | nil => 
            -- If p is empty, then c'.2 must be a, contradiction to hnexist. 
            cases hnexist ⟨c', by simp [Mem.head c' C', hc], pathNil hpath $ rfl⟩ 
          | cons x p' =>
            -- So, w.l.o.g. p is non-empty and can be written as x::p'.
            have ⟨y, hinpath, heq⟩ := pathLastEdge hpath 
            have hin : y ∈ E -l C := by 
              have hingraph : y ∈ (E -l C) ++ C := by
                have h := hsub y 
                have h' := mem_nonzeroCount.mp hinpath
                exact permEqvMemClosed heqv $ mem_nonzeroCount.mpr $ Nat.ltOfLtOfLe h' h 
              match mem_append y hingraph with 
              | (Or.inl h) => 
                exact h 
              | (Or.inr h) => 
                cases hnexist ⟨y, h, heq⟩  
            have hin' := decideEqTrue hin
            -- We look at the first edge z in p that is in E -l C.
            have ⟨z, s, t, hprop', hfempty', heq'⟩ := listSplitUntil (fun e => e ∈ (E -l C)) (x::p') y ⟨hinpath, hin'⟩
            have hprop' := ofDecideEqTrue hprop' 
            rw [heq'] at hpath
            -- The prefix s of p must have z.1 as the last vertex. 
            have ⟨b, hspath, hztpath⟩ := (pathBreak s (z::t) hpath)
            have heq'' : z.1 = b := pathCons hztpath 
            rw [← heq''] at hspath
            cases hs : s with 
            | nil => 
              -- If s is empty, then c' is adjacent to z.
              exact ⟨c', z, by simp [hc, Mem.head c' C'], hprop', pathNil hspath $ hs⟩    
            | cons f s' =>  
              /-
                If s is non-empty, there must be an edge e in s s.t. it has the last vertex as tail.
              -/
              rw [hs] at hspath 
              have ⟨e, hin'', heq'''⟩  := pathLastEdge hspath
              /-
                As a member of p, it must by definition be in E but not in E -l C.
              -/
              have hnin : ¬ e ∈ (E -l C) := by 
                rw [← hs] at hin''
                intro hin''' 
                have hinfilter : e ∈ filter (fun (e : α × α) => decide (e ∈ E -l C)) s 
                  := mem_filter_of_prop hin'' (decideEqTrue hin''')  
                rw [hfempty'] at hinfilter 
                cases hinfilter 
              have hsub' : f::s' ⊆ x::p' := by 
                simp only [isPermSubOf] 
                intro a 
                rw [heq', hs]
                simp only [count_append]
                rw [Nat.add_comm]
                exact Nat.leAddLeft (count (f :: s') a) (count (z :: t) a)
              have hin''' : e ∈ E := by 
                have h := mem_nonzeroCount.mp hin'' 
                have h' := Nat.ltOfLtOfLe h (hsub' e) 
                exact mem_nonzeroCount.mpr $  Nat.ltOfLtOfLe h' (hsub e)
              match mem_append e $ permEqvMemClosed heqv hin''' with 
              | (Or.inl h) => 
                cases hnin h
              | (Or.inr h) => 
                -- Hence, it must be in C.
                exact ⟨e, z, h, hprop', heq'''⟩  
      -- There is a circuit in E - C with starting edge y. 
      have ⟨Crest, hsubrest, hcircrest⟩  := existenceCircuitWithStartEdge hinRest (removeCircuit C E hsub ed hcirc)
      -- We can create a bigger circuit by concatinating them at x / y.
      have ⟨Ccon, hcirccon, heqvcon⟩   := concatCircuit hcirc hcircrest ⟨x, hinC, heq⟩  
      have hltcon : (c'::C').length < Ccon.length := by
        have h' := permEqvLength heqvcon 
        rw [length_append, length_cons] at h' 
        rw [h']
        rw [hc]
        have h'' := Nat.addLtAddLeft (Nat.succPos Crest.length) (c'::C').length
        rw [Nat.add_zero] at h'' 
        assumption 
      have hsubcon : Ccon ⊆ E := by 
        have h : C ++ y :: Crest ⊆ C ++ (E -l C) := by 
          simp only [isPermSubOf,count_append]
          intro a 
          apply Nat.addLeAddLeft 
          exact hsubrest a 
        have h' := permEqvSymm $ permEqvTrans heqv (permEqvRotate (E -l C) C)
        have h'' := permSubEqvClosed (permEqvSymm heqvcon) h
        simp only [isPermSubOf,count_append]
        intro a 
        rw [← (h' a)]
        exact h'' a 
      exact ⟨Ccon, a, hsubcon, hcirccon, hltcon⟩ 
end Eulerian