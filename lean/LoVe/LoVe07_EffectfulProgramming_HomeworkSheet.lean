/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe07_EffectfulProgramming_Demo


/- # LoVe Homework 7 (10 points + 1 bonus point): Monads

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (5 points): `map` for Monads

We will define a `map` function for monads and derive its so-called functorial
properties from the three laws.

1.1 (2 points). Define `map` on `m`. This function should not be confused
with `mmap` from the lecture's demo.

Hint: The challenge is to find a way to create a value of type `m β`. Follow the
types. Inventory all the arguments and operations available (e.g., `pure`,
`>>=`) with their types and see if you can plug them together like Lego
bricks. -/

def map {m : Type → Type} [LawfulMonad m] {α β : Type} (f : α → β) (ma : m α) :
    m β := ma >>= (fun a => pure (f a))
  -- do
  --   let x ← ma
  --   pure (f x)

/- 1.2 (1 point). Prove the identity law for `map`.

Hint: You will need `LawfulMonad.bind_pure`. -/

theorem map_id {m : Type → Type} [i: LawfulMonad m] {α : Type} (ma : m α) :
    map id ma = ma := by
  unfold id
  show ma >>= (fun a => pure a) = ma
  -- now it's obviously `bind_pure`
  apply i.bind_pure

/- 1.3 (2 points). Prove the composition law for `map`. -/

/-

(do
    let a ←
      do
        let a ← ma
        pure (f a)
    pure (g a)) =
  do
  let a ← ma
  pure (g (f a))

  ----

  do
    let a ← ma
    let a' ← pure (f a)
    pure (g a')

  =

  do
    let a ← ma
    pure (g (f a))

-/
theorem map_map {m : Type → Type} [i: LawfulMonad m] {α β γ : Type}
      (f : α → β) (g : β → γ) (ma : m α) :
    map g (map f ma) = map (fun x ↦ g (f x)) ma := by
  -- simp [map]
  show (ma >>= (fun a => pure (f a)) >>= (fun a => pure (g a))) =
    ma >>= (fun a => pure (g (f a)))
  rw [i.bind_assoc]
  /-
  ⊢ do
      let a ← ma
      let a ← pure (f a)
      pure (g a)
  =
    do
      let a ← ma
      pure (g (f a))
  -/
  -- stuck here originally.. could not reduce the goal
  -- but `apply?` suggests `bind_congr` which makes progress by
  -- splitting the LHS of the goal into a bind and the remaining hole
  -- is to prove that the overall binds are equal.
  refine bind_congr ?_
  intro
  apply i.pure_bind


/- ## Question 2 (5 points + 1 bonus point): Monadic Structure on Lists

`List` can be seen as a monad, similar to `Option` but with several possible
outcomes. It is also similar to `Set`, but the results are ordered and finite.
The code below sets `List` up as a monad. -/

#check List.append

namespace List

def bind {α β : Type} : List α → (α → List β) → List β
  | [],      _f => []
  | a :: as, f => f a ++ bind as f

#eval bind [1, 2, 3] (fun x => [x*x, x*x*x])

def pure {α : Type} (a : α) : List α :=
  [a]

/- 2.1 (1 point). Prove the following property of `bind` under the append
operation. -/

theorem bind_append {α β : Type} (f : α → List β) :
    ∀as as' : List α, bind (as ++ as') f = bind as f ++ bind as' f := by
  intros
  match as with
    | [] =>
      rw [List.nil_append]
      simp [bind]
      -- or, instead of `simp`
      -- conv =>
      --   rhs
      --   lhs
      --   unfold bind
      -- rw [List.nil_append]
    | hd :: tl =>
      rw [List.cons_append]
      simp [bind]
      rw [bind_append f _ _]

/- 2.2 (3 points). Prove the three laws for `List`. -/

theorem pure_bind {α β : Type} (a : α) (f : α → List β) :
    bind (pure a) f = f a := by
  simp [List.bind, List.pure]

theorem bind_pure {α : Type} :
    ∀as : List α, bind as pure = as := by
  intros
  match as with
    | [] => simp [List.bind]
    | hd :: tl =>
      simp [List.bind, List.pure]
      apply bind_pure tl

theorem bind_assoc {α β γ : Type} (f : α → List β) (g : β → List γ) :
    ∀as : List α, bind (bind as f) g = bind as (fun a ↦ bind (f a) g) := by
  intros
  match as with
    | [] => simp [List.bind]
    | hd :: tl =>
      simp [List.bind]
      rw [bind_append]
      -- append is left and right injective
      -- apply?
      refine (List.append_right_inj (bind (f hd) g)).mpr ?_
      -- ⊢ bind (bind tl f) g =
      --   bind tl (fun a => bind (f a) g)
      apply bind_assoc  -- recursive application for `tl`



/- 2.3 (1 point). Prove the following list-specific law. -/

theorem bind_pure_comp_eq_map {α β : Type} {f : α → β} :
    ∀as : List α, bind as (fun a ↦ pure (f a)) = List.map f as := by
  intros
  match as with
    | [] => simp [List.bind]
    | hd :: tl =>
      simp [List.bind, List.pure]
      apply bind_pure_comp_eq_map

/- 2.4 (1 bonus point). Register `List` as a lawful monad: -/

/-
class LawfulMonad (m : Type → Type)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
      (ma : m α) :
    ((ma >>= f) >>= g) = (ma >>= (fun a ↦ f a >>= g))
-/
instance LawfulMonad : LawfulMonad List :=
  {
    pure := List.pure,
    bind := List.bind,
    pure_bind := List.pure_bind,
    bind_pure := List.bind_pure,
    bind_assoc := List.bind_assoc,
  }

end List

end LoVe
