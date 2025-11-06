import Types.SysFHOAS.Stx
import Types.SysFHOAS.Denote
import Types.SysFHOAS.Show

namespace SysFPHOAS

universe u v

-- id_type : Type
-- id_type : ∀ α. α → α
def id_type : Ty :=
  Type'.all (fun α => Type'.arr (Type'.var α) (Type'.var α))

-- id : id_type =  ∀ α. α → α
-- id = Λ α. λ (x : α). x
def system_f_id : Term id_type :=
    .tlam (fun α => .lam (fun x => .var x))

def church_bool_type : Ty :=
  Type'.all (fun α => Type'.arr ((Type'.var α)) (Type'.arr (Type'.var α) (Type'.var α)))

def church_bool_true : Term church_bool_type :=
  .tlam (fun α  => .lam (fun t => .lam (fun f => .var t)))

def church_bool_false : Term church_bool_type :=
  .tlam (fun α => .lam (fun t => .lam (fun f => .var f)))

def church_if_type : Ty :=
  Type'.all fun α => Type'.arr church_bool_type (Type'.arr (Type'.var α) (Type'.arr (Type'.var α) (Type'.var α)))

def church_if : Term church_if_type :=
  .tlam fun α =>
    .lam fun b =>
      .lam fun t =>
        .lam fun f =>
          .app
            (.app
              (.tapp (.var b) α)
              (.var t))
            (.var f)

-- Λ α. λ X Y. (if α true X Y)
def church_if_true_syntax : Term church_bool_type :=
  fun {T} {rep} =>
    .tlam (fun α =>
      .lam (fun X =>
        .lam (fun Y =>
          .app
            (.app
              (.app
                (.tapp church_if α)
                (church_bool_true))
              (.var X))
            (.var Y))))

-- Λ α. λ X Y. X
def choose_left_syntax : Term church_bool_type :=
  .tlam (fun α => .lam (fun X => .lam (fun Y => .var X)))

-- Λ α. λ X Y. (if α false X Y)
def church_if_false_syntax : Term church_bool_type :=
  fun {T} {rep} =>
    .tlam (fun α =>
      .lam (fun X =>
        .lam (fun Y =>
          .app
            (.app
              (.app
                (.tapp (church_if (T:=T) (rep:=rep)) α)
                (church_bool_false (T:=T) (rep:=rep)))
              (.var X))
            (.var Y))))



example : Type'.denote id_type = ((T : _) → PLift T → PLift T) := rfl
example : Term'.denote system_f_id = (fun (x : _) (y : PLift x) => y) := rfl
example : Type'.denote church_bool_type = ((T : _) → PLift T → PLift T → PLift T) := rfl
example : Term'.denote church_bool_true = (fun x (t f : PLift x) => t) := rfl
example : Term'.denote church_bool_false = (fun x (t f : PLift x) => f) := rfl
example : Term'.denote church_if = (fun x b t f => b x t f) := rfl


/-- info: "∀α. (α → α)" -/
#guard_msgs in
#eval id_type.show

/-- info: "(Λα. (λa.a))" -/
#guard_msgs in
#eval system_f_id.show

/-- info: "(Λα. (λa.(λb.a)))" -/
#guard_msgs in
#eval church_bool_true.show

/-- info: "(Λα. (λa.(λb.b)))" -/
#guard_msgs in
#eval church_bool_false.show

/-- info: "(Λα. (λa.(λb.(λc.(((a [(α → (α → α))]) b) c)))))" -/
#guard_msgs in
#eval church_if.show

/--
info: "(Λα. (λa.(λb.(((((Λβ . (λc.(λd.(λe.(((c [(β  → (β  → β ))]) d) e))))) [(∀β . (β  → (β  → β )) → (α → (α → α)))]) (Λβ . (λc.(λd.c)))) a) b))))"
-/
#guard_msgs in
#eval church_if_true_syntax.show

/--
info: "(Λα. (λa.(λb.(((((Λβ . (λc.(λd.(λe.(((c [(β  → (β  → β ))]) d) e))))) [(∀β . (β  → (β  → β )) → (α → (α → α)))]) (Λβ . (λc.(λd.d)))) a) b))))"
-/
#guard_msgs in
#eval church_if_false_syntax.show

@[simp]
theorem church_if_true {A : Sort u} (X Y : PLift A) :
    church_if.denote A church_bool_true.denote X Y = X := rfl

@[simp]
theorem church_if_false {A : Sort u} (X Y : PLift A) :
    church_if.denote  A church_bool_false.denote X Y = Y := rfl

-- Λ α. λ X Y. Y
def choose_right_syntax : Term church_bool_type :=
  .tlam (fun α => .lam (fun X => .lam (fun Y => .var Y)))

-- Denotational equivalence theorems over the syntax
-- prove that Λ α. λ X Y. (if α true X Y) = Λ α. λ X Y. X
theorem if_true_equiv_left : same church_if_true_syntax choose_left_syntax := rfl

-- prove that Λ α. λ X Y. (if α false X Y) = Λ α. λ X Y. Y
theorem if_false_equiv_right : same church_if_false_syntax choose_right_syntax := rfl
