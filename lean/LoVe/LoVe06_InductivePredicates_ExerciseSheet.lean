/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Exercise 6: Inductive Predicates

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Even and Odd

The `Even` predicate is `True` for even numbers and `False` for odd numbers. -/

#check Even
#print Even

/- We define `Odd` as the negation of `Even`: -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. Prove that 1 is odd and register this fact as a simp rule.

Hint: `cases` or `induction` is useful to reason about hypotheses of the form
`Even …`. -/

@[simp] theorem Odd_1 :
    Odd 1 := by
  intro h
  cases h

/- 1.2. Prove that 3 and 5 are odd. -/

theorem Odd_3 : Odd 3 := by
  intro h
  cases h
  simp at a
  cases a

theorem Odd_5 : Odd 5 := by
  intro h
  cases h
  simp at a
  cases a
  cases a_1
  -- grind -- fails

/- 1.3. Complete the following proof by structural induction. -/

theorem Even_two_times :
    ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 => by
    rw [mul_add, mul_one]
    apply Even.add_two
    exact Even_two_times m


/- ## Question 2: Tennis Games

Recall the inductive type of tennis scores from the demo: -/

#check Score

/- 2.1. Define an inductive predicate that returns `True` if the server is
ahead of the receiver and that returns `False` otherwise. -/

inductive ServAhead : Score → Prop where
  | vs_ahead : ∀ (n m: Nat), n > m → ServAhead (Score.vs n m)
  | adv : ServAhead Score.advServ
  -- | not_disAdv : ¬ (ServAhead Score.advRecv)  -- isn't an application of `ServAhead`
  | game : ServAhead Score.gameServ

/- 2.2. Validate your predicate definition by proving the following theorems. -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
    ServAhead (Score.vs m n) :=
  ServAhead.vs_ahead _ _ hgt

theorem ServAhead_advServ :
    ServAhead Score.advServ := ServAhead.adv

theorem not_ServAhead_advRecv :
    ¬ ServAhead Score.advRecv := by
  intro h
  cases h

theorem ServAhead_gameServ :
    ServAhead Score.gameServ := ServAhead.game

theorem not_ServAhead_gameRecv :
    ¬ ServAhead Score.gameRecv := by
  intro h
  cases h

/- 2.3. Compare the above theorem statements with your definition. What do you
observe? -/

-- The positive theorems correspond to constructors of the inductive Prop and
-- the negative theorems correspond to omissions of constructors.


/- ## Question 3: Binary Trees

3.1. Prove the converse of `IsFull_mirror`. You may exploit already proved
theorems (e.g., `IsFull_mirror`, `mirror_mirror`). -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
    ∀t : Tree α, IsFull (mirror t) → IsFull t := by
  intro t
  intro hfm
  rw [← mirror_mirror t]
  apply IsFull_mirror
  assumption

/- 3.2. Define a `map` function on binary trees, similar to `List.map`. -/

/- NOTE: Tree.map conflicts with a def in mathlib which is compatible with
   our Tree, but simp uses the mathlib version which is very confusing
   below. -/
def treeMap {α β : Type} (f : α → β) : Tree α → Tree β
  | .nil => .nil
  | .node a l r => .node (f a) (treeMap f l) (treeMap f r)

/- 3.3. Prove the following theorem by case distinction. -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
    ∀t : Tree α, treeMap f t = Tree.nil ↔ t = Tree.nil := by
  intro t
  cases t
  { simp only [treeMap] }
  { constructor <;>
    /- both directions are ruled out by cases -/
    { intro h
      cases h } }

/- 3.4 (**optional**). Prove the following theorem by rule induction. -/

theorem Tree.IsFull_map {α β : Type} (f : α → β) :
    ∀t : Tree α, IsFull t → IsFull (treeMap f t) := by
  intro t
  induction t with
  | nil => intro _; simp only [treeMap]; exact IsFull.nil
  | node a l r hl hr =>
    intro h
    simp only [treeMap]
    cases h
    have hl' : IsFull (treeMap f l) := hl hl_1
    have hr' : IsFull (treeMap f r) := hr hr_1
    apply IsFull.node
    . exact hl'
    . exact hr'
    . constructor
      { intro hfl
        have : l = Tree.nil := by
          apply (Tree.map_eq_empty_iff f l).mp
          assumption
        apply (Tree.map_eq_empty_iff f r).mpr
        exact (hiff.mp this)
      }
      -- same but l |-> r and .mp |-> .mpr
      { intro hfl
        have : r = Tree.nil := by
          apply (Tree.map_eq_empty_iff f r).mp
          assumption
        apply (Tree.map_eq_empty_iff f l).mpr
        exact (hiff.mpr this)
      }

end LoVe
