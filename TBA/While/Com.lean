/- The com Language -/
namespace While

/- Variables and Values -/

/-- names for variables -/
abbrev VName := String

inductive Val where
  | bool (b : Bool)
  | int  (i : Int)
  deriving DecidableEq

-- lets us use a `Bool/Int` where a `Val` is expected
instance : Coe Bool Val := ⟨Val.bool⟩
instance : Coe Int Val  := ⟨Val.int⟩
#check (true : Val)

/- Expressions and Commands -/

/-- binary operations -/
inductive BinOp where
  | eq | and | lt | add | sub

inductive Expr where
  | const (v : Val)
  | var (x : VName)
  | binop (l : Expr) (op : BinOp) (r : Expr)

instance : Coe Val   Expr := ⟨Expr.const⟩
instance : Coe VName Expr := ⟨Expr.var⟩

def BinOp.eval : BinOp → Val → Val → Option Val
  | BinOp.eq,  v₁,          v₂          => some (Val.bool (v₁ = v₂))
  | BinOp.and, Val.bool b₁, Val.bool b₂ => some (Val.bool (b₁ ∧ b₂))
  | BinOp.lt,  Val.int i₁,  Val.int i₂  => some (Val.bool (i₁ < i₂))
  | BinOp.add, Val.int i₁,  Val.int i₂  => some (Val.int (i₁ + i₂))
  | BinOp.sub, Val.int i₁,  Val.int i₂  => some (Val.int (i₁ - i₂))
  | _,         _,           _           => none

inductive Com where
  | skip
  | ass (x : VName) (e : Expr)
  | seq (c c' : Com)
  | cond (b : Expr) (cₜ cₑ : Com)
  | while (b : Expr) (c : Com)

open Com

infix:150 " ::= " => ass
infixr:130 ";; "   => seq

/- Prettier embedding of `Expr` and `Com` as term-level macros -/
/- (You can ignore this part, jump to the examples below to see its usage) -/

open Lean

syntax "`[Expr|" term "]" : term

macro_rules
  | `(`[Expr|true])      => `((true : Expr))
  | `(`[Expr|false])     => `((false : Expr))
  | `(`[Expr|$n:numLit]) => `(($n : Expr))
  | `(`[Expr|$x:ident])  => `(($(quote x.getId.toString) : Expr))
  | `(`[Expr|$x = $y])   => `(Expr.binop `[Expr|$x] BinOp.eq `[Expr|$y])
  | `(`[Expr|$x && $y])  => `(Expr.binop `[Expr|$x] BinOp.and `[Expr|$y])
  | `(`[Expr|$x < $y])   => `(Expr.binop `[Expr|$x] BinOp.lt `[Expr|$y])
  | `(`[Expr|$x + $y])   => `(Expr.binop `[Expr|$x] BinOp.add `[Expr|$y])
  | `(`[Expr|$x - $y])   => `(Expr.binop `[Expr|$x] BinOp.sub `[Expr|$y])
  | `(`[Expr|($x)])      => `(`[Expr|$x])

declare_syntax_cat com

syntax ident " := " term ";\n" : com
syntax "if " "(" term ")" " {\n" com* "\n}" (" else " "{\n" com* "\n}")? : com
syntax "while (" term ")" " {\n" com* "\n}" : com

syntax "`[Com|" com* "]" : term

macro_rules
  | `(`[Com|])                    => `(Com.skip)
  | `(`[Com|$x:ident := $e;])     => `($(quote x.getId.toString) ::= `[Expr|$e])
  | `(`[Com|if ($b) { $cts* } else { $cfs* }]) =>
    `(Com.cond `[Expr|$b] `[Com|$cts*] `[Com|$cfs*])
  | `(`[Com|if ($b) { $cts* }])   => `(`[Com|if ($b) { $cts* } else {}])
  | `(`[Com|while ($b) { $cs* }]) => `(Com.while `[Expr|$b] `[Com|$cs*])
  | `(`[Com|$c $cs*])             => `(Com.seq `[Com|$c] `[Com|$cs*])


def example1 := `[Com|
  x := 8;
  y := 10;
  if (x < y) {
    x := x + 1;
  } else {
    y := y + 3;
  }]
#reduce example1

def example2 := `[Com|
  x := 8;
  if (x < y) {
    x := x + 1;
  } else {
    y := y + 3;
    x := 9;
  }
  y := x;]
#reduce example2

def example3 := `[Com|
  if (x < 10) {
    x := 8;
  } else {
    x := 14;
  }
  while (x < 7) {
    x :=  x + x;
  }]
#reduce example3

def example4 := `[Com|
  x := 13;
  y := 7;
  while (y = x - 5) {
    x := x + 1;
  }]
#reduce example4

end While
