import Types.SysFHOAS.Show
/- import Types.SysFHOAS.Denote -/

namespace SysFPHOAS

universe u

open Term' (var)

namespace Ex1

def a.t : Ty := .arr
  (.all fun α ↦ .var α) (.all fun β => .var β)

def a.e : Term a.t :=
  .lam fun x => .tlam fun β => .tapp (.var x) β

-- b cant exist because A is the function type

-- TODO: C , A₃ must be False, i.e. ∀ α, α
-- TODO: D , A₄ could be the constant false function,
--           but this cannot exist in the given context as (x α) isnt a type.

end Ex1

section Ex2

-- The eliminator for the Unit type is simply id, so its encoding is 

def unit : Ty := .all fun α => .arr (.var α) (.var α)
def unit.i : Term unit := .tlam fun _ => .lam fun v => .var v

def emp : Ty := .all fun α => .var α
def emp.e : Term (.all fun x => .arr emp (.var x)) :=
  .tlam fun β => .lam fun e => .tapp (.var e) β

variable (X : Ty) {rep : Type u} {rep2 : Type' rep → Type u}

def tree : Ty := .all fun α => 
  .arr (.var α) <| .arr
    (.arr (.var α) <| .arr X <| .arr (.var α) (.var α))
    (.var α)
def tree.leaf : Term (tree X) := 
  .tlam fun _ => .lam fun lf => .lam fun _ => .var lf
def tree.node : Term (.arr (tree X) <| .arr X <| .arr (tree X) (tree X)) := 
  .lam fun l => .lam fun c => .lam fun r =>
    .tlam fun β =>
      .lam fun bot =>
        .lam fun main =>
          have l : Term' _ (Type'.var β) :=
            var l |>.tapp β |>.app (.var bot) |>.app (.var main)
          have r : Term' _ (Type'.var β) :=
            var r |>.tapp β |>.app (.var bot) |>.app (.var main)
          var main |>.app l |>.app (.var c) |>.app r

/- def prod (A B : rep) : Type' rep := -/
/-   .all fun s => .arr (.arr (.var A) (.arr (.var B) (.var s))) (.var s) -/
/-  -/
/- def prod.fst (A B : rep) : Term' rep2 (.arr (prod A B) (.var A)) := -/
/-   .lam fun ab => -/
/-     var ab |>.tapp A |>.app -/
/-       (.lam fun v => .lam fun _ => .var v) -/
/-  -/
/- def prod.snd (A B : rep) : Term' rep2 (.arr (prod A B) (.var B)) := -/
/-   .lam fun ab => -/
/-     var ab |>.tapp B |>.app -/
/-       (.lam fun _ => .lam fun v => .var v) -/

end Ex2

end SysFPHOAS

