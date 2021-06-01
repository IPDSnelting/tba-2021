import TBA.Eulerian.Nat

open BEq Nat List Decidable

namespace Eq

protected theorem symm_iff {a b : α} : b = a ↔ a = b := ⟨Eq.symm, Eq.symm⟩ 

end Eq

namespace List

@[simp] theorem length_append {as bs : List α} :
  length (as ++ bs) = length as + length bs :=
  match as with
  | []      => by simp
  | a :: as => by simp [Nat.succ_add, length_append]

theorem length_zero_iff_nil {as : List α} : length as = 0 ↔ as = [] :=
⟨fun e => by cases as; rfl; simp [length_cons] at e, fun e => by rw [e]; rfl⟩

theorem length_cons_ne_zero {as : List α} {a : α} : length (a :: as) ≠ 0 := by
  rw [List.length_cons]; exact Nat.succNeZero _

-- Some lemmas about filters

@[simp] theorem filter_nil {p : α → Bool} : filter p [] = [] := by
  simp [filter, filterAux, reverse, reverseAux]

theorem cons_eq_append (a : α) (as : List α) : a :: as = [a] ++ as := rfl

theorem reverseAux_append {rs as : List α} : reverseAux rs as = reverseAux rs [] ++ as :=
  match rs with
  | []      => rfl
  | r :: rs => by
    simp only [reverseAux]
    rw [reverseAux_append, reverseAux_append (as := [r]), cons_eq_append r as, append_assoc]

theorem filterAux_aux {p : α → Bool} (as : List α) :
  (rs : List α) → filterAux p as rs = rs.reverse ++ (filterAux p as []) :=
  match as with
  | [] => by intros; simp [filterAux, reverse, reverseAux];
  | a :: as => by
    intro rs
    simp only [filterAux]
    cases p a
    case false => simp [filterAux_aux as rs]
    case true =>
      rw [filterAux_aux as (a :: rs), filterAux_aux as [a]]
      simp only [reverse, reverseAux, List.append, List.cons_append, List.nil_append]
      rw [reverseAux_append, cons_eq_append _ (filterAux p as []), append_assoc]

theorem filter_cons (a : α) (as : List α) :
  filter p (a :: as) = if p a then a :: filter p as else filter p as := by
  simp only [filter, filterAux]
  cases p a
  simp
  rw [filterAux_aux]; simp [reverse, reverseAux]

@[simp] theorem filter_append {as bs : List α} {p : α → Bool} :
  filter p (as ++ bs) = filter p as ++ filter p bs := by
  induction as with
  | nil      => simp
  | cons a as ih =>
    rw [filter_cons, cons_append, filter_cons]
    cases p a <;> simp [ih]

-- A membership predicate

inductive Mem : α → List α → Prop where
  | head (a : α) (as : List α)   : Mem a (a::as)
  | tail (a b : α) (bs : List α) : Mem a bs → Mem a (b::bs)

infix:50 " ∈ " => Mem

@[simp] theorem beq_refl [DecidableEq α] : ((a : α) == a) = true :=
  decideEqTrue rfl

@[simp] theorem beq_neq [DecidableEq α] {a b : α} (h : ¬ a = b) : (a == b) = false :=
  decideEqFalse h

theorem length_erase_mem [DecidableEq α] {a : α} {as : List α} (h : a ∈ as) :
  length (List.erase as a) + 1 = length as :=
  match a, as, h with
  | _, _, Mem.head a bs => by simp [List.erase]
  | _, _, Mem.tail a b bs h => by
    simp only [List.erase]
    match b == a with
    | true => simp
    | false => { simp only [length_cons]; rw [←length_erase_mem h] }

theorem mem_singleton [DecidableEq α] {a b : α} (h : a ∈ [b]) : a = b := by
  cases h with
  | head h       => rfl
  | tail _ _ _ h => cases h

def mem_of_nonzero_length [DecidableEq α] {as : List α} :
  (h : length as > 0) → { a // a ∈ as } :=
  match as with
  | []      => by { simp only [length_nil]; intro fa; cases fa }
  | a :: as => by { intros; apply Subtype.mk; apply Mem.head }

theorem mem_append {as bs : List α} : ∀ a, a ∈ (as ++ bs) → a ∈ as ∨ a ∈ bs :=
  match as with
  | [] => by intros; apply Or.inr; assumption
  | a :: as => by 
    simp only [List.cons_append]
    intros a h
    cases h with
    | head h => apply Or.inl; apply Mem.head
    | tail _ _ _ h =>
      cases mem_append (as := as) (bs := bs) a h
      case inl => apply Or.inl; apply Mem.tail; assumption
      case inr => apply Or.inr; assumption

theorem mem_of_mem_filter {as : List α} {a : α} {p : α → Bool} : a ∈ filter p as → a ∈ as :=
  match as with
  | [] => by intros; assumption
  | a' :: as => by 
      rw [filter_cons]; cases p a'
      case false => intro h; apply Mem.tail; apply mem_of_mem_filter h
      case true => 
        intro h
        cases h with
        | head => apply Mem.head
        | tail _ _ _ h => apply Mem.tail; apply mem_of_mem_filter h

theorem mem_filter_of_prop {as : List α} {a : α} {p : α → Bool} (ha : a ∈ as) (hpa : p a = true) :
  a ∈ filter p as := by
  induction ha with
  | head a as => rw [filter_cons, hpa]; simp; apply Mem.head
  | tail a b as ha' ih => 
    rw [filter_cons]
    cases hpb : p b
    case false => simp; exact ih hpa
    case true  => simp; apply Mem.tail; exact ih hpa

theorem filterProp_of_mem {as : List α} {p : α → Bool} {a : α} : a ∈ filter p as → p a = true :=
  match as with
  | [] => by intro h; cases h
  | a' :: as => by
      rw [filter_cons]; byCases hpa : p a'
      case inr => simp [hpa]; exact filterProp_of_mem
      case inl => simp [hpa]; intro h; cases h; assumption; apply filterProp_of_mem; assumption

theorem mem_split {a : α} {as : List α} (h : a ∈ as) : ∃ s t, as = s ++ a :: t :=
  match a, as, h with
  | _, _, Mem.head a bs     => ⟨[], ⟨bs, rfl⟩⟩
  | _, _, Mem.tail a b bs h =>
    match bs, mem_split h with
    | _, ⟨s, ⟨t, rfl⟩⟩ => ⟨b::s, ⟨t, List.cons_append .. ▸ rfl⟩⟩

-- Couting elements

section Count
variable [DecidableEq α] (as bs as' bs' : List α) (a b : α)

def count : Nat := (as.filter $ fun b => b == a).length

@[simp] theorem count_empty : count [] a = 0 := by simp [count]

@[simp] theorem count_self_cons : (a :: as).count a = Nat.succ (as.count a) := by
  simp [count, filter_cons]

theorem count_neq_cons {as} {a b : α} (h : ¬ b = a) : (b :: as).count a = as.count a := by
  simp [count, filter_cons, h]

@[simp] theorem count_append : (as ++ bs).count a = as.count a + bs.count a :=
  by simp [count]

--set_option trace.Meta.Tactic.simp true
theorem count_erase {as : List α} {a b : α} :
  (as.erase a).count b = if (a == b) then (as.count b) - 1 else as.count b :=
  match as with
  | [] => by simp only [List.erase]; cases (a == b) <;> simp
  | a' :: as => by
    simp only [List.erase]
    byCases h : a' = a
    case inl => 
      cases h
      simp only [beq_refl]
      byCases h' : a = b
      case inl => cases h'; simp only [beq_refl, Lean.Simp.ite_True, Nat.succ_sub_succ, count_self_cons]; apply Nat.sub_zero
      case inr => rw [beq_neq h']; simp [count_neq_cons h']
    case inr =>
      rw [beq_neq h]
      byCases h' : a' = b
      case inl => cases h'; simp [count_erase (as := as), beq_neq (Ne.symm h)]
      case inr => simp [count_neq_cons h', count_neq_cons h', count_erase]

theorem count_le_cons : as.count a ≤ (b :: as).count a := by
  byCases h : (b = a)
  case inl => cases h; simp [count_self_cons, Nat.leSucc]
  case inr => rw [count_neq_cons h]; simp [Nat.leRefl]

theorem mem_nonzeroCount {as : List α} {a : α}: a ∈ as ↔ as.count a > 0 := by
  apply Iff.intro
  case mp =>
    intro h
    induction h with
    | head a => simp [Nat.zeroLtSucc]
    | tail _ _ _ h ih => apply Nat.ltOfLtOfLe ih; apply count_le_cons
  case mpr =>
    intro h
    let ⟨a', ha'⟩ := mem_of_nonzero_length h
    let foo := filterProp_of_mem ha'
    cases ofDecideEqTrue foo
    apply mem_of_mem_filter ha'
    
-- Erasing elements from lists
  
theorem erase_comm {as : List α} : (as.erase a).erase b  = (as.erase b).erase a :=
  match as with
  | [] => rfl
  | a' :: as => by
    byCases h : a' = a
    case inl => 
      cases h; simp only [List.erase]
      byCases h' : b = a
      case inl => cases h'; simp
      case inr => rw [beq_neq (Ne.symm h')]; simp [List.erase]
    case inr =>
      simp only [List.erase]
      rw [beq_neq h]
      byCases h' : a' = b
      case inl => cases h'; simp [List.erase]
      case inr => simp [List.erase, beq_neq h', beq_neq h, erase_comm (as := as)]

theorem filter_erase_false {as : List α} {a : α} {p : α → Bool} (h : p a = false) :
  filter p (as.erase a) = filter p as :=
  match as with
  | [] => by simp [List.erase]
  | b :: as => by
    simp only [List.erase, filter_cons]
    byCases h' : b = a
    case inl => cases h'; simp [h]
    case inr => simp [h', filter_cons]; rw [filter_erase_false h]

theorem filter_erase_true {as : List α} {a : α} {p : α → Bool} (hpa : p a = true) :
  filter p (as.erase a) = (filter p as).erase a :=
  match as with
  | [] => rfl
  | b :: as => by
    simp
    byCases h : b = a
    case inl => cases h; simp [List.erase, filter_cons, hpa]
    case inr =>
      simp only [List.erase, beq_neq h, filter_cons]
      cases hpb : p b
      case false => exact filter_erase_true hpa
      case true => rw [filter_erase_true hpa]; simp [List.erase, h]

def eraseAll (as bs : List α) : List α :=
  match bs with
  | []      => as
  | b :: bs => eraseAll (as.erase b) bs

infixl:55 " -l " => eraseAll

theorem erase_eraseAll {as bs : List α} {a : α} : (as.erase a) -l bs = (as -l bs).erase a :=
  match bs with
  | [] => rfl
  | b :: bs => by simp only [eraseAll]; rw [←erase_eraseAll, erase_comm]

@[simp] theorem count_eraseAll (as bs : List α) (a : α) :
  (as -l bs).count a = as.count a - bs.count a :=
  match bs with
  | [] => rfl
  | b :: bs => by
    simp only [eraseAll]; rw [erase_eraseAll]; simp
    byCases hba : b = a;
    case inl => cases hba; rw [count_self_cons, count_erase, count_eraseAll as bs a, beq_refl]; rfl
    case inr => rw [count_erase, beq_neq hba, count_eraseAll as bs a, count_neq_cons]; repeat simp_all

-- Lists which are permutations of each other, and sublists modulo permutation

def isPermEqvTo : Prop := ∀ a, as.count a = bs.count a
infixl:50 " ≃ " => isPermEqvTo -- Type as \simeq

def isPermSubOf : Prop := ∀ a, as.count a ≤ bs.count a
infixl:50 " ⊆ " => isPermSubOf -- Type as \sub

theorem permSubOfEraseSub : (as -l bs) ⊆ as := fun a => by simp [Nat.subLe]

theorem mem_of_mem_eraseAll {as bs : List α} {a : α} : a ∈ (as -l bs) → a ∈ as := by
  rw [mem_nonzeroCount, mem_nonzeroCount, count_eraseAll]
  intro h; exact Nat.ltOfLtOfLe h (Nat.subLe _ _)

theorem permSubEraseAllLength {as bs : List α} : bs ⊆ as → length (as -l bs) = length as - length bs :=
  match bs with
  | [] => fun _ => rfl
  | b :: bs => fun hsub => by
    simp only [eraseAll, length_cons]
    have hbas : b ∈ as := by
      have hb := hsub b
      rw [count_self_cons] at hb
      rw [mem_nonzeroCount]
      exact Nat.ltOfLeOfLt (zeroLe _) (ltOfSuccLe hb)
    have hsub' : bs.isPermSubOf (as.erase b) := fun c => by
      have hc := hsub c
      byCases h : b = c
      case inl =>
        cases h
        rw [count_self_cons] at hc
        rw [count_erase]
        simp [leOfSuccLeSucc (Nat.leTrans hc leSuccSubOne)]
      case inr =>
        rw [count_neq_cons h] at hc
        apply Nat.leTrans hc
        rw [count_erase, beq_neq h]
        simp [Nat.leRefl]
    rw [permSubEraseAllLength hsub', ←length_erase_mem hbas, Nat.succ_sub_succ]

theorem permSubExtend {as bs : List α} {b} (hsub : bs ⊆ as) (ha : b ∈ (as -l bs)) : (b :: bs) ⊆ as := by
  intro a
  rw [mem_nonzeroCount, count_eraseAll, ←zeroLtIffSub] at ha
  byCases h : b = a
  case inl => cases h; simp; assumption
  case inr => rw [count_neq_cons h]; apply hsub

def permSubObtainComplement {as bs : List α} (hsub : bs ⊆ as) 
    (hlength : bs.length < as.length) : { e // e ∈ as -l bs} := by
  have hl : (as -l bs).length > 0 := by rw [permSubEraseAllLength hsub, ←zeroLtIffSub]; assumption
  revert hl; cases as -l bs
  case nil => simp only [length_nil]; intro hl'; cases hl'
  case cons => intros; exact ⟨_, Mem.head _ _⟩

theorem permSubEqvClosed {as bs bs' : List α} (heqv : bs ≃ bs') (hsub : bs ⊆ as) : bs' ⊆ as :=
  fun a => by rw [←heqv a]; exact hsub a

theorem permSubSingleton {as : List α} {a : α} : a ∈ as → [a] ⊆ as := by
  intros ha b
  rw [mem_nonzeroCount] at ha
  byCases h : a = b
  case inl => cases h; simp [count_self_cons]; assumption
  case inr => rw [count_neq_cons h]; simp [Nat.zeroLe]

theorem permEqvRotate : (as ++ bs) ≃ (bs ++ as) :=
  fun a => by simp [Nat.add_comm];

theorem permEqvRefl {as : List α} : as ≃ as :=
  fun a => rfl

theorem permEqvTrans {as bs cs : List α} (h : as ≃ bs) (h' : bs ≃ cs) : as ≃ cs :=
  fun a => Eq.trans (h a) (h' a)

theorem permEqvSymm {as bs : List α} (h : as ≃ bs) : bs ≃ as :=
  fun a => by simp [Nat.add_comm, h a]

theorem permEqvToEraseAppend {as bs : List α} (ps : bs ⊆ as) : as ≃ ((as -l bs) ++ bs) :=
  fun a => by simp only [count_append, count_eraseAll]; rw [←Nat.le_subAdd (ps a)]

theorem permEqvToEraseCons {as : List α} {a : α} (h : a ∈ as) : as ≃ (a :: (as.erase a)) := by
  exact permEqvTrans (permEqvToEraseAppend (permSubSingleton h)) (permEqvRotate _ _)

theorem permEqvCons {as bs : List α} {a : α} (h : as ≃ bs) : (a :: as) ≃ (a :: bs) := by
  intro b
  byCases hba : (a = b)
  case inl => cases hba; simp [count_self_cons, h a];
  case inr => rw [count_neq_cons hba, count_neq_cons hba, h b]

theorem permSubEraseOfpermEqvCons {as bs : List α} {a : α} (h : (a :: as) ⊆ bs) :
  as ⊆ (bs.erase a) := fun b => by
  let ha := h a
  byCases h' : a = b
  case inl =>
    cases h'
    rw [count_erase]
    rw [count_self_cons] at ha
    simp [Nat.leOfSuccLeSucc (Nat.leTrans ha leSuccSubOne)]
  case inr =>
    let hb := h b
    rw [count_neq_cons h'] at hb
    rw [count_erase, beq_neq h']
    exact hb

theorem permEqvOfPermSub {as bs : List α} : as ⊆ bs → as.length = bs.length → as ≃ bs :=
  match as with
  | [] => fun hsub hl => by
    rw [length_nil, Eq.symm_iff, length_zero_iff_nil] at hl
    rw [hl]; intro b; rfl
  | a :: as => fun hsub hl => by
    have habs : a ∈ bs := by
      rw [mem_nonzeroCount]
      let hsuba := hsub a
      simp only [count_self_cons] at hsuba
      exact Nat.ltOfLtOfLe (Nat.zeroLtSucc _) hsuba
    have hsub' : as.isPermSubOf (bs.erase a) := permSubEraseOfpermEqvCons hsub
    have hl' : as.length = (bs.erase a).length := by
      apply Nat.add_right_cancel (m := 1)
      rw [length_erase_mem habs, ←hl, length_cons]
    have hp : bs.isPermEqvTo (a :: (bs.erase a)) := permEqvToEraseCons habs
    exact permEqvTrans (permEqvCons (permEqvOfPermSub hsub' hl')) (permEqvSymm hp)

theorem permEqvMemClosed {as bs : List α} {a : α} (hp : as ≃ bs) : a ∈ as → a ∈ bs := by
  rw [mem_nonzeroCount, mem_nonzeroCount, hp a]; intros; assumption

theorem permEqvEraseOfpermEqvCons {as bs : List α} {a : α} (h : (a :: as) ≃ bs) : as ≃ (bs.erase a) := fun a' => by
  let ha := h a
  byCases h' : a = a'
  case inl => 
    cases h'
    rw [count_erase]
    simp only [beq_refl, Lean.Simp.ite_True]
    rw [←ha, count_self_cons, succ_sub_succ,  Nat.sub_zero]
  case inr =>
    let ha' := h a'
    rw [count_neq_cons h'] at ha'
    rw [count_erase, beq_neq h']
    exact ha'

theorem permEqvLength {as bs : List α} : as ≃ bs → as.length = bs.length :=
  match as with
  | [] =>
    match bs with
    | [] => fun _ => rfl
    | b :: bs => fun h => by
      let hb := h b
      simp only [count] at hb; rw [filter_cons, beq_refl] at hb
      simp at hb
  | a :: as => fun h => by
    let ha := h a
    rw [count_self_cons] at ha
    rw [length_cons, permEqvLength (permEqvEraseOfpermEqvCons h)]
    exact length_erase_mem (mem_nonzeroCount.mpr (Nat.ltOfLtOfEq (Nat.zeroLtSucc (count as a)) ha))

theorem permEqv_filter_erase_true {as : List α} {a : α} {p : α → Bool} (hpa : p a = true) (ha : a ∈ as) :
  (a :: filter p (List.erase as a)) ≃ (filter p as) := by
  intro b
  byCases h : a = b
  case inl =>
    cases h
    rw [count_self_cons, filter_erase_true hpa, count_erase]
    simp only [beq_refl, Lean.Simp.ite_True]
    have h' : 1 ≤ count (filter p as) a := by
      apply Nat.succLeOfLt
      apply mem_nonzeroCount.mp
      apply mem_filter_of_prop ha hpa
    exact Eq.symm (le_subAdd h')
  case inr =>
    rw [count_neq_cons h, filter_erase_true hpa, count_erase, beq_neq h]
    simp

theorem permEqvFilter {as bs : List α} (p : α → Bool) : as ≃ bs → (filter p as) ≃ (filter p bs) :=
  match as with
  | [] => by
    intro h
    rw [length_zero_iff_nil.mp $ Eq.symm (permEqvLength h)]
    exact permEqvRefl
  | a :: as => by
    intro h
    rw [filter_cons]
    have h' := permEqvFilter p (permEqvEraseOfpermEqvCons h)
    cases hpa : p a with
    | true =>
      simp only [beq_refl, Lean.Simp.ite_True]
      apply permEqvTrans (permEqvCons h')
      have ha : a ∈ bs := by rw [mem_nonzeroCount, ←h a]; simp [zeroLtSucc]
      exact permEqv_filter_erase_true (as := bs) hpa ha
    | false =>
      refine permEqvTrans h' ?_
      rw [filter_erase_false hpa]
      exact permEqvRefl

end Count

end List
