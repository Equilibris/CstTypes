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
    Term'.tlam (fun α => Term'.lam (fun x => Term'.var x))

def church_bool_type : Ty :=
  Type'.all (fun α => Type'.arr ((Type'.var α)) (Type'.arr (Type'.var α) (Type'.var α)))

def church_bool_true : Term church_bool_type :=
  Term'.tlam (fun α  => Term'.lam (fun t => Term'.lam (fun f => Term'.var t)))

def church_bool_false : Term church_bool_type :=
  Term'.tlam (fun α => Term'.lam (fun t => Term'.lam (fun f => Term'.var f)))

def church_if_type : Ty :=
  Type'.all fun α => Type'.arr church_bool_type (Type'.arr (Type'.var α) (Type'.arr (Type'.var α) (Type'.var α)))

def church_if : Term church_if_type :=
  Term'.tlam fun α =>
    Term'.lam fun b =>
      Term'.lam fun t =>
        Term'.lam fun f =>
          Term'.app
            (Term'.app
              (Term'.tapp (Term'.var b) α)
              (Term'.var t))
            (Term'.var f)

-- Λ α. λ X Y. (if α true X Y)
def church_if_true_syntax : Term church_bool_type :=
  fun {T} {rep} =>
    Term'.tlam (fun α =>
      Term'.lam (fun X =>
        Term'.lam (fun Y =>
          Term'.app
            (Term'.app
              (Term'.app
                (Term'.tapp (church_if (T:=T) (rep:=rep)) α)
                (church_bool_true (T:=T) (rep:=rep)))
              (Term'.var X))
            (Term'.var Y))))

-- Λ α. λ X Y. X
def choose_left_syntax : Term church_bool_type :=
  Term'.tlam (fun α => Term'.lam (fun X => Term'.lam (fun Y => Term'.var X)))

-- Λ α. λ X Y. (if α false X Y)
def church_if_false_syntax : Term church_bool_type :=
  fun {T} {rep} =>
    Term'.tlam (fun α =>
      Term'.lam (fun X =>
        Term'.lam (fun Y =>
          Term'.app
            (Term'.app
              (Term'.app
                (Term'.tapp (church_if (T:=T) (rep:=rep)) α)
                (church_bool_false (T:=T) (rep:=rep)))
              (Term'.var X))
            (Term'.var Y))))



example : Type'.denote id_type = ((T : _) → PLift T → PLift T) := rfl
example : Term'.denote system_f_id = (fun (x : _) (y : PLift x) => y) := rfl
example : Type'.denote church_bool_type = ((T : _) → PLift T → PLift T → PLift T) := rfl
example : Term'.denote church_bool_true = (fun x (t f : PLift x) => t) := rfl
example : Term'.denote church_bool_false = (fun x (t f : PLift x) => f) := rfl
example : Term'.denote church_if = (fun x b t f => b x t f) := rfl


/-- info: "∀α. (α → α)" -/
#guard_msgs in
#eval Type'.show id_type

/-- info: "(Λα. (λa.a))" -/
#guard_msgs in
#eval Term'.show (system_f_id)

/-- info: "(Λα. (λa.(λb.a)))" -/
#guard_msgs in
#eval Term'.show (church_bool_true)

/-- info: "(Λα. (λa.(λb.b)))" -/
#guard_msgs in
#eval Term'.show (church_bool_false)

/-- info: "(Λα. (λa.(λb.(λc.(((a [(α → (α → α))]) b) c)))))" -/
#guard_msgs in
#eval Term'.show (church_if)

/--
info: "(Λα. (λa.(λb.(((((Λβ . (λc.(λd.(λe.(((c [(β  → (β  → β ))]) d) e))))) [(∀β . (β  → (β  → β )) → (α → (α → α)))]) (Λβ . (λc.(λd.c)))) a) b))))"
-/
#guard_msgs in
#eval Term'.show church_if_true_syntax

/--
info: "(Λα. (λa.(λb.(((((Λβ . (λc.(λd.(λe.(((c [(β  → (β  → β ))]) d) e))))) [(∀β . (β  → (β  → β )) → (α → (α → α)))]) (Λβ . (λc.(λd.d)))) a) b))))"
-/
#guard_msgs in
#eval Term'.show church_if_false_syntax

@[simp]
theorem church_if_true {A : Sort u} (X Y : PLift A) :
    (Term'.denote church_if) A (Term'.denote church_bool_true) X Y = X := rfl

@[simp]
theorem church_if_false {A : Sort u} (X Y : PLift A) :
    (Term'.denote church_if) A (Term'.denote church_bool_false) X Y = Y := rfl

-- Λ α. λ X Y. Y
def choose_right_syntax : Term church_bool_type :=
  Term'.tlam (fun α => Term'.lam (fun X => Term'.lam (fun Y => Term'.var Y)))

-- Denotational equivalence theorems over the syntax
-- prove that Λ α. λ X Y. (if α true X Y) = Λ α. λ X Y. X
theorem if_true_equiv_left : same church_if_true_syntax choose_left_syntax := rfl

-- prove that Λ α. λ X Y. (if α false X Y) = Λ α. λ X Y. Y
theorem if_false_equiv_right : same church_if_false_syntax choose_right_syntax := rfl
