/- Eulerian circuits -/

/- 
We provide you with a formalization of some facts about lists being equal up to permutation and
lists being sublists of their permutation
-/
import TBA.Eulerian.List

open List

namespace Eulerian

-- We model graphs as lists of pairs on a type with decidable equality.
variable {α : Type} (E : List (α × α)) [DecidableEq α]

def isNonEmpty : Prop := E.length > 0

-- Now it's your turn to fill out the following definitions and prove the characterization!
def isStronglyConnected (E : List (α × α)) : Prop := _

def hasEqualInOutDegrees (E : List (α × α)) : Prop := _

def isEulerian (E : List (α × α)) : Prop := _

theorem eulerian_degrees
  (hne : isNonEmpty E)
  (sc : isStronglyConnected E)
  (ed : hasEqualInOutDegrees E)
  : isEulerian E := _

end Eulerian