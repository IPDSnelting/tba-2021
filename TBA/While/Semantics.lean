/- Semantics -/
import TBA.While.Com

namespace While
open Com

abbrev Map (α β : Type) := α → Option β

namespace Map

def empty : Map α β := fun k => none

def update [DecidableEq α] (m : Map α β) (k : α) (v : Option β) : Map α β :=
  fun k' => if k = k' then v else m k'

notation:max m "[" k " ↦ " v "]" => update m k v

end Map

abbrev State := Map VName Val

namespace Expr

variable (σ : State) in
def eval : Expr → Option Val
  | Expr.const v => some v
  | Expr.var x   => σ x
  | Expr.binop e₁ op e₂ => match eval e₁, eval e₂ with
    | some v₁, some v₂ => op.eval v₁ v₂  -- BinOp.eval : BinOp → Val → Val → Option Val
    | _,       _       => none

def time : Expr → Nat
  | Expr.const v => 1
  | Expr.var x   => 1
  | Expr.binop e₁ op e₂ => time e₁ + time e₂ + 1

end Expr

open Expr

section
set_option hygiene false  -- HACK: allow forward reference in notation
-- note the `local` to make the hacky notation local to the current section
local notation:60 "⟨" c ", " σ "⟩"  " ⇓ " σ' " : " t:60 => Bigstep c σ σ' t

inductive Bigstep : Com → State → State → Nat → Prop where
  | skip :
    ⟨skip, σ⟩ ⇓ σ : 1
  | ass :
    ⟨x ::= e, σ⟩ ⇓ σ[x ↦ e.eval σ] : e.time + 1
  | seq (h₁ : ⟨c₁, σ⟩ ⇓ σ' : t₁) (h₂ : ⟨c₂, σ'⟩ ⇓ σ'' : t₂) :
    ⟨c₁;; c₂, σ⟩ ⇓ σ'' : t₁ + t₂ + 1
  | ifTrue (hb : eval σ b = true) (ht : ⟨cₜ, σ⟩ ⇓ σ' : t) :
    ⟨cond b cₜ cₑ, σ⟩ ⇓ σ' : b.time + t + 1
  | ifFalse (hb : eval σ b = false) (he : ⟨cₑ, σ⟩ ⇓ σ' : t) :
    ⟨cond b cₜ cₑ, σ⟩ ⇓ σ' : b.time + t + 1
  | whileTrue (hb : eval σ b = true) (hc : ⟨c, σ⟩ ⇓ σ' : t₁) (hind : ⟨while b c, σ'⟩ ⇓ σ'' : t₂) :
    ⟨while b c, σ⟩ ⇓ σ'' : b.time + t₁ + t₂ + 1
  | whileFalse (hb : eval σ b = false) :
    ⟨while b c, σ⟩ ⇓ σ : b.time + 1
end

-- redeclare "proper" notation with working pretty printer
notation:60 "⟨" c ", " σ "⟩"  " ⇓ " σ' " : " t:60 => Bigstep c σ σ' t

end While
