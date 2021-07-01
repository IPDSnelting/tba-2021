/- Eulerian circuits -/

/- 
We provide you with a formalization of some facts about lists being equal up to permutation and
lists being sublists of their permutation
-/
import TBA.Eulerian.List
import TBA.Util.Find 

open List

namespace Eulerian

-- If a simp has to be turned to a simp only. :D
-- set_option trace.Meta.Tactic.simp true 

-- We model graphs as lists of pairs on a type with decidable equality.
variable {α : Type} (E : List (α × α)) [DecidableEq α]

/-
  To use some lemmas concerning filtering lists, we first show that the membership predicate is decidable. 
-/
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

/-
  We now begin by giving some basic definitions we can work with later.
-/

def isNonEmpty : Prop := E.length > 0

instance : Decidable (isNonEmpty E) := inferInstanceAs (Decidable (E.length > 0))

inductive path : List (α × α) → α → α → Prop
  | refl : path [] a a 
  | trans (e : (α × α)) (C : List (α × α)) : path C e.2 x → path (e::C) e.1 x 

def circuit : List (α × α) → α → Prop := by 
  intro E a 
  exact path E a a

def reachable (E : List (α × α)) (a b : α) : Prop := 
  ∃ p : List (α × α), p ⊆ E ∧ path p a b 

def isStronglyConnected (E : List (α × α)) : Prop := ∀ a b : α, reachable E a b  

def inDegreeProp : α → (α × α) → Bool := fun a e => decide (e.2 = a)

def outDegreeProp : α → (α × α) → Bool := fun a e => decide (e.1 = a)   

def inDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ inDegreeProp a).length

def outDegree (E : List (α × α)) (a : α) : Nat := (E.filter $ outDegreeProp a).length

-- returns list of head ends of edges.
def heads (E : List (α × α)) : List α := map (fun e => e.2) E 

-- returns list of tail ends of edges.
def tails (E : List (α × α)) : List α := map (fun e => e.1) E 

def hasEqualInOutDegrees (E : List (α × α)) : Prop := ∀ a : α, inDegree E a = outDegree E a

def isEulerian (E : List (α × α)) : Prop := ∃ E' : List (α × α), ∃ a : α, E' ≃ E ∧ circuit E' a

/- 
  The next section consists of a few helpful lemmas we use later in the proof. 
  We separate them from the main proof, to make things more structured and easy to follow.
-/

-- The first set of lemmas is concerned with basic manipulations that will become handy later.

theorem contraposition : (p → q) → (¬q → ¬p) := fun hpq hnq hp => hnq $ hpq hp  

theorem notEqualComm {a b : α} : (¬a = b) → (¬b = a) := by 
  intro hne h 
  exact hne $ Eq.symm h

/-
  The next set of lemmas will partially extend properties of general lists.
  All of them could be stated with no graph theoretic interpretation in mind.
-/

theorem consNonEmpty (e : (α × α)) (E' : List (α × α)) : isNonEmpty (e :: E') := by
  simp [isNonEmpty, Nat.succPos]

theorem lengthIteComm {xs ys : List (α × α)} {p : Bool} : 
  length (if p then xs else ys) = if p then length xs else length ys := by
  match p with 
  | true => 
    simp [eqSelf, Lean.Simp.ite_True]  
  | false => 
    simp [eqSelf, Lean.Simp.ite_False]

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
  rw [h a, h' a]

/-
  This next set of lemmas will exactly deal with those more graph-theoretic properties.
  In particular, we prove a deciding property for non-Eulerian graphs. 
-/

/-
  These two lemmas can probably be condensed by defining explicitly the 
  p : α → Bool for inDegree and outDegree and then generalizing p.
  Then only one lemma would be needed to express both.
-/
theorem inDegreeAppend {C E : List (α × α)} (hsub : C ⊆ E) : 
  ∀ x : α, inDegree E x = inDegree (E -l C) x + inDegree C x := by 
  intro x
  have heqv := permEqvFilter (inDegreeProp x) $ permEqvToEraseAppend hsub
  rw [filter_append] at heqv 
  have hlen := permEqvLength heqv
  rw [length_append] at hlen 
  simp only [inDegree]
  assumption

theorem outDegreeAppend {C E : List (α × α)} (hsub : C ⊆ E) : 
  ∀ x : α, outDegree E x = outDegree (E -l C) x + outDegree C x := by 
  intro x
  have heqv := permEqvFilter (outDegreeProp x) $ permEqvToEraseAppend hsub
  rw [filter_append] at heqv 
  have hlen := permEqvLength heqv
  rw [length_append] at hlen 
  simp only [outDegree]
  assumption

-- Theorem that a subgraph always has at most as many edges as E.
theorem permSubLeLength {C E : List (α × α)} (hsub : C ⊆ E) : length C ≤ length E := by 
  have h := permEqvToEraseAppend hsub 
  have h' := permEqvLength h 
  rw [length_append] at h'
  rw [h']
  exact Nat.leAddLeft (length C) (length (E -l C))

-- If a graph is not Eulerian, all of its circuits have a smaller length.
theorem notEulerianNoEqCircuit (hne : ¬isEulerian E) {a : α} : 
  ∀ C : List (α × α), C ⊆ E ∧ circuit C a → C.length < E.length := by 
  intro C hall
  byCases h : C ≃ E 
  case inl => 
    have heulerian : isEulerian E := ⟨C, a, h, hall.right⟩ 
    cases hne heulerian 
  case inr => 
    have hle := permSubLeLength hall.left 
    exact Nat.ltOfLeAndNe hle $ contraposition (permEqvOfPermSub hall.left) h

/-
  The next set of lemmas will show basic properties of paths and deal with special cases.
-/

theorem pathNil {a b : α} (hp : path [] a b) : a = b := by 
  match hp with 
  | path.refl => rfl 

theorem pathEdge {e : α × α} {a b : α} (hp : path [e] a b) : e.1 = a ∧ e.2 = b := by 
  match hp with 
  | path.trans _ _ hpath => 
    exact ⟨rfl, pathNil hpath⟩ 

theorem pathCons {p : List (α × α)} {e : (α × α)} {a b : α} :
  path (e::p) a b → e.1 = a := by 
  intro h 
  cases h with 
  | trans _ _ h' => rfl

-- Generalisation of transitivity: Paths can be concatenated into a bigger path.
theorem pathAppend {p q : List (α × α)} {a b c : α} 
  (hp : path p a b) (hq : path q b c) : path (p++q) a c := by 
  induction p generalizing a b with 
  | nil => 
    have heq := pathNil hp
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

theorem pathLastEdge {p : List (α × α)} {e : (α × α)} {a b : α} 
  (hp : path (e::p) a b) : ∃ x : α × α, x ∈ e::p ∧ x.2 = b := by 
  induction p generalizing e a b with 
  | nil => 
    cases hp with 
    | trans _ _ hp' => 
      have heq := pathNil hp'
      exact ⟨e, Mem.head e [], heq⟩ 
  | cons e' p' ih => 
    cases hp with 
    | trans _ _ hp' => 
      have ⟨x, hin, heq⟩ := ih hp'
      exact ⟨x, Mem.tail x e (e'::p') hin, heq⟩ 

/-
  We can now give a constructive proof of the actual theorem in a few steps, using the above lemmas.
  This part is closest to the actual way we proved the theorem on paper.
-/

-- We begin by proving, that all circuits have the property that each vertex has equal in- and outdegree.
theorem circuitEqualInOut (E : List (α × α)) {a : α} (h : circuit E a) : hasEqualInOutDegrees E := by 
  suffices ∀ n : Nat, ∀ E : List (α × α), ∀ a : α, E.length = n → circuit E a → hasEqualInOutDegrees E by 
    exact this E.length E a rfl h  
  intro n 
  induction n with 
  | zero => 
    intro E a heq hcirc 
    have hnil := length_zero_iff_nil.mp heq 
    rw [hnil]
    simp only [hasEqualInOutDegrees, inDegree, outDegree]
    intro x 
    simp [filter_nil, length_nil]
  | succ n ih => 
    intro E a heq hcirc 
    cases E with
    | nil => 
      simp [length, lengthAux] at heq 
    | cons e E => 
      simp only [circuit] at hcirc 
      cases E with 
      | nil => 
        have h := pathEdge hcirc
        simp only [hasEqualInOutDegrees, inDegree, outDegree]
        intro x 
        match decEq x a with 
        | isTrue h' => 
          rw [h']
          simp only [filter_cons e [], inDegreeProp, outDegreeProp]
          rw [h.left]
          simp only [eqSelf, decideEqTrue]
          rw [h.right]
          simp [eqSelf, decideEqTrue, Lean.Simp.ite_True, length_cons, length_nil] 
        | isFalse h' => 
          simp only [filter_cons e [], inDegreeProp, outDegreeProp]
          rw [← h.left] at h'
          have h' := notEqualComm h' 
          simp only [eqSelf, decideEqFalse, h'] 
          rw [h.left, ← h.right] at h' 
          simp [eqSelf, decideEqFalse, h'] 
      | cons e' E' => 
        have heq' : e::e'::E' = [e]++[e'] ++ E' := by 
          simp [append_assoc] 
        rw [heq'] 
        rw [heq'] at hcirc 
        have ⟨b, hpath, hpath'⟩ := pathBreak [e, e'] E' hcirc 
        have hnpath := path.trans (a,b) E' hpath' 
        simp only [Prod.fst] at hnpath 
        have hlen : ((a, b) :: E').length = n := by 
          have h' := heq 
          simp only [length_cons, Nat.succ_Eq_add_one]
          simp only [length_cons, Nat.succ_Eq_add_one] at h'
          exact Nat.add_right_cancel h'
        have ed := ih ((a, b) :: E') a hlen (by simp [circuit, hnpath])  
        simp only [hasEqualInOutDegrees, inDegree, inDegreeProp, outDegree, outDegreeProp] 
        have heqe : e.1 = a := pathCons hpath 
        have ⟨heqee', heqe'⟩ : e'.1 = e.2 ∧ e'.2 = b := by 
          cases hpath with 
          | trans _ _ h' => 
            exact pathEdge h'
        intro x 
        /-
          The next sequence of operations might be a bit hard to follow.
          In essence, by expanding all the definitions, we remove the necessity of case distinctions for x.
          Keep in mind that what we're really doing here is reducing the equal degree property of E = e::e'::E' to (a,b)::E'.
        -/
        simp only [length_append, filter_append, filter_cons e' [], filter_cons e [], filter_nil] 
        have hed := ed x
        simp only [hasEqualInOutDegrees, inDegree, inDegreeProp, outDegree, outDegreeProp] at hed
        rw [cons_eq_append] at hed
        simp only [length_append, filter_append, filter_cons (a,b) [], filter_nil] at hed
        simp only [lengthIteComm, length_nil, length_cons, Nat.succ_Eq_add_one, Nat.add_zero, Nat.zero_add]
        simp only [lengthIteComm, length_nil, length_cons, Nat.succ_Eq_add_one, Nat.add_zero, Nat.zero_add] at hed
        simp only [Nat.add_assoc]
        rw [heqee', heqe', heqe]
        rw [hed, Nat.add_comm]
        rw [Nat.add_comm (if decide (e.snd = x) = true then 1 else 0) $ length (filter (fun (e : α × α) => decide (e.fst = x)) E'), Nat.add_assoc]

-- Corollary: If a path is not a circuit, all vertices except the start and end have the equal degree property.
theorem pathEqualInOut (E : List (α × α)) {a b : α} (hpath : path E a b) : 
  a ≠ b → inDegree E a + 1 = outDegree E a ∧ inDegree E b = outDegree E b + 1 ∧ 
  ∀ x : α, x ≠ a ∧ x ≠ b → inDegree E x = outDegree E x := by 
  induction E generalizing a b with 
  | nil => 
    intro h 
    cases h $ pathNil hpath
  | cons e E ih => 
    intro hab 
    cases hpath with 
    | trans _ _ hpath' => 
      match decEq e.snd b with 
      | isTrue heq =>   
        -- Case 1: E is a circuit.
        rw [heq] at hpath'
        have ed := circuitEqualInOut E hpath'
        constructor
        -- Case a 
        simp only [inDegree, inDegreeProp, outDegree, outDegreeProp, filter_cons]
        rw [heq] 
        simp [eqSelf, decideEqTrue, decideEqFalse, notEqualComm hab, length_cons, Lean.Simp.ite_True, Lean.Simp.ite_False, Nat.succPos] -- trace
        exact ed e.1 
        constructor
        -- Case b 
        simp only [inDegree, outDegree, inDegreeProp, outDegreeProp, filter_cons]
        simp [eqSelf, decideEqTrue, decideEqFalse, heq, hab] -- trace
        exact ed b
        -- Otherwise 
        intro x ⟨hnea, hneb⟩ 
        simp only [inDegree, inDegreeProp, outDegree, outDegreeProp, filter_cons]
        rw [heq]
        simp [decideEqFalse, notEqualComm hneb, notEqualComm hnea] -- trace
        exact ed x 
      | isFalse hneq => 
        -- Case 2: E is not a circuit.
        have almosted := ih hpath' hneq 
        constructor 
        -- Case a 
        match decEq e.1 e.2 with 
        | isTrue hloop => 
          simp only [inDegree, inDegreeProp, outDegree, outDegreeProp, filter_cons]
          rw [hloop]
          simp [eqSelf, decideEqTrue] -- trace
          exact almosted.left
        | isFalse hnloop => 
          simp only [inDegree, inDegreeProp, outDegree, outDegreeProp, filter_cons]
          simp [eqSelf, decideEqTrue, decideEqFalse, notEqualComm hnloop] -- trace
          exact almosted.right.right e.1 ⟨hnloop, hab⟩  
        constructor 
        -- Case b 
        simp only [inDegree, inDegreeProp, outDegree, outDegreeProp, filter_cons]
        simp [decideEqFalse, hab, hneq]
        exact almosted.right.left 
        -- Otherwise 
        intro x ⟨hnea, hneb⟩ 
        match decEq e.2 x with 
        | isTrue heqx => 
          simp only [inDegree, inDegreeProp, outDegree, outDegreeProp, filter_cons]
          simp [heqx, eqSelf, decideEqTrue, notEqualComm hnea, decideEqFalse] -- trace
          rw [Nat.succ_Eq_add_one, ← heqx]
          exact almosted.left 
        | isFalse hneqx => 
          simp only [inDegree, inDegreeProp, outDegree, outDegreeProp, filter_cons]
          simp [decideEqFalse, hneqx, notEqualComm hnea] -- trace
          exact almosted.right.right x ⟨notEqualComm hneqx, hneb⟩ 

/- 
  Using the theorems above, we can now show that the equal degree property is preserved under the removal of circuits.
  Note that this lemma could be extended to arbitrary subgraphs with equal degree property.
-/
theorem removeCircuit (C E : List (α × α)) {a : α} (hsub : C ⊆ E) (ed : hasEqualInOutDegrees E) (hcirc : circuit C a) 
  : hasEqualInOutDegrees $ E -l C := by 
  simp only [hasEqualInOutDegrees, inDegree, outDegree]
  intro a 
  have heqv := permEqvToEraseAppend hsub 
  have hout := permEqvFilter (inDegreeProp a) heqv 
  have hin  := permEqvFilter (outDegreeProp a) heqv 
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

/- 
  We now show, that we can always find a circuit with a given starting edge, if the underlying graph has the equal degree property.
-/
theorem existenceCircuitWithStartEdge {E : List (α × α)} {e : (α × α)} (h : e ∈ E) (ed : hasEqualInOutDegrees E)  
  : ∃ C : List (α × α), (e::C) ⊆ E ∧ circuit (e::C) e.1 := by 
  have hpathextend : ∀ p : List (α × α), ∀ a b : α, p ⊆ E ∧ path p a b ∧ a ≠ b → 
    ∃ e : (α × α), e ∈ (E -l p) ∧ path (p++[e]) a e.2 := by 
    intro p a b ⟨hsub, hpath, hanotb⟩
    have eqcount := ed b
    have neqcount := (pathEqualInOut p hpath hanotb).right.left 
    have hin := inDegreeAppend hsub b
    have hout := outDegreeAppend hsub b
    rw [eqcount, hout, neqcount, Nat.add_comm (outDegree p b) 1] at hin 
    rw [← Nat.add_assoc] at hin
    have hlt := Nat.add_right_cancel hin 
    have hnempty : outDegree (E -l p) b > 0 := by simp [Nat.succPos, hlt]
    have ⟨e, hmem, heq⟩ : ∃ e : (α × α), e ∈ (E -l p) ∧ e.1 = b := by 
      simp only [outDegree] at hnempty 
      cases hfilter : filter (outDegreeProp b) (E -l p) with 
      | nil => 
        rw [length_zero_iff_nil.mpr hfilter] at hnempty 
        cases hnempty 
      | cons e tail => 
        have hmem := Mem.head e tail 
        rw [← hfilter] at hmem 
        have heq := filterProp_of_mem hmem 
        have heq := ofDecideEqTrue heq
        exact ⟨e, mem_of_mem_filter hmem, heq⟩ 
    have hepath := path.trans e [] path.refl 
    rw [heq] at hepath 
    exact ⟨e, hmem, pathAppend hpath hepath⟩
  byCases hclaim : ∃ C : List (α × α), (e::C) ⊆ E ∧ circuit (e::C) e.1 
  case inl => 
    exact hclaim 
  case inr => 
    have hcontra : ∀ n : Nat, ∃ C : List (α × α), ∃ b : α, (e::C) ⊆ E ∧ path (e::C) e.1 b ∧ n < (e::C).length := by 
      intro n
      induction n with 
      | zero => 
        exact ⟨[], e.2, permSubSingleton h, path.trans e [] path.refl, consNonEmpty e []⟩ 
      | succ n ih => 
        have ⟨C', b, hsub, hpath, hlt⟩ := ih 
        match decEq e.1 b with 
        | isTrue hcirc => 
          rw [← hcirc] at hpath 
          cases hclaim ⟨C', hsub, hpath⟩ 
        | isFalse hncirc =>
          have ⟨e', hmem', hpath'⟩ := hpathextend (e::C') e.1 b ⟨hsub, hpath, hncirc⟩
          have hsub' := permSubExtend hsub hmem' 
          have hsub' := permSubEqvClosed (permEqvRotate [e'] (e::C')) hsub' 
          rw [cons_append] at hsub'
          have hlt' : n + 1 < (e :: C' ++ [e']).length := by 
            simp only [length_append, length_cons, length_nil]
            simp only [length_cons, Nat.succ_Eq_add_one] at hlt 
            exact hlt 
          simp only [cons_append e C' [e']] at hsub' 
          simp only [cons_append e C' [e']] at hpath'
          simp only [cons_append e C' [e']] at hlt'
          exact ⟨C'++[e'], e'.2, hsub', hpath', hlt'⟩
    have ⟨C, _, hsub, _, hlt⟩ := hcontra E.length 
    cases Nat.ltIrrefl E.length $ Nat.ltOfLtOfLe hlt $ permSubLeLength hsub

-- Corollary: If a graph has equal in- and out degrees and is non-empty, then it contains a non-empty circuit.
theorem existenceCircuit (E : List (α × α)) (hne : isNonEmpty E) (ed : hasEqualInOutDegrees E) 
  : ∃ C : List (α × α), ∃ a : α, C ⊆ E ∧ circuit C a ∧ isNonEmpty C := by 
  match E with 
  | nil => 
    simp only [isNonEmpty] at hne 
    simp_all 
  | cons e E' => 
    have ⟨C, hsub, hcirc⟩ := existenceCircuitWithStartEdge (Mem.head e E') ed 
    exact ⟨e::C, e.1, hsub, hcirc, consNonEmpty e C⟩  

-- We now prove that circuits adjacent to other circuits can be concatenated into a larger cirquit.
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

/- 
  The above theorems should have given you an idea of how we want to prove the main theorem:
  We can find a nonempty circuit in a given graph (assuming he has all the properties of the main theorem) 
  and can then add adjacent circuits to the one we found until we get an Eulerian circuit. 
-/

-- The actual main theorem.
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
        have hle := permSubLeLength hsub 
        byCases heq : C.length = E.length 
        case inl => 
          rw [← heq] at hlt
          exact ⟨C, a, hsub, hcirc, hlt⟩ 
        case inr => 
          have ⟨C', a', hsub', hcirc', hltc'⟩ := this C a ⟨hsub, hcirc, Nat.ltOfLeAndNe hle heq⟩ 
          have hltc' := Nat.ltOfLeOfLt (Nat.succLeOfLt hltc) hltc' 
          exact ⟨C', a', hsub', hcirc', hltc'⟩ 
    have ⟨C, a, hsub, hcirc, hltc⟩ := h (E.length - 1) $ Nat.subLt hne $ Nat.ltSuccSelf 0
    have heq := Nat.leAntisymm (permSubLeLength hsub) (Nat.leTrans Nat.leSuccSubOne (Nat.succLeOfLt hltc))
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
        byCases houter : ∃ a : α, filter (inDegreeProp a) C = [] 
        case inr => 
        -- If every vertex is in C, then there trivially is such an edge.
          have hall := fun a hempty => houter ⟨a, hempty⟩ 
          have hfilter := hall e'.1 
          cases hcfilter : filter (inDegreeProp e'.1) C with 
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
            have hfin : e ∈ filter (inDegreeProp a) C := mem_filter_of_prop hin (decideEqTrue hhead)
            rw [hfempty] at hfin
            simp [mem_nonzeroCount, count_empty] at hfin
          -- By strongly connectedness, there must still be a path p from the tail of c' to a.
          have hreachable := sc c'.2 a
          simp only [reachable] at hreachable 
          have ⟨p, hsub, hpath⟩ := hreachable 
          cases p with 
          | nil => 
            -- If p is empty, then c'.2 must be a, contradiction to hnexist. 
            cases hnexist ⟨c', by simp [Mem.head c' C', hc], pathNil hpath⟩ 
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
              exact ⟨c', z, by simp [hc, Mem.head c' C'], hprop', (by rw [hs] at hspath; exact pathNil hspath)⟩    
            | cons f s' =>  
              -- If s is non-empty, there must be an edge e in s s.t. it has the last vertex as tail.
              rw [hs] at hspath 
              have ⟨e, hin'', heq'''⟩  := pathLastEdge hspath
              -- As a member of p, it must by definition be in E but not in E -l C.
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
          simp only [isPermSubOf, count_append]
          intro a 
          apply Nat.addLeAddLeft 
          exact hsubrest a 
        have h' := permEqvSymm $ permEqvTrans heqv (permEqvRotate (E -l C) C)
        have h'' := permSubEqvClosed (permEqvSymm heqvcon) h
        simp only [isPermSubOf, count_append]
        intro a 
        rw [← (h' a)]
        exact h'' a 
      exact ⟨Ccon, a, hsubcon, hcirccon, hltcon⟩ 

end Eulerian