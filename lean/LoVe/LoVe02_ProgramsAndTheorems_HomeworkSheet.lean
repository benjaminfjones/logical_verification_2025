/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe Homework 2 (10 points): Programs and Theorems

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (4 points): Snoc

1.1 (3 points). Define the function `snoc` that appends a single element to the
end of a list. Your function should be defined by recursion and not using `++`
(`List.append`). -/

-- [],            a => [a]              = [a]
-- x :: [],       a => x :: a :: []     = x :: (snoc [] a)
-- y :: x :: [], a => y :: x :: a :: [] = y :: (snoc xs a)
def snoc {α : Type} : List α → α → List α
  | [], a => [a]
  | x :: xs, a => x :: (snoc xs a)

/- 1.2 (1 point). Convince yourself that your definition of `snoc` works by
testing it on a few examples. -/

-- invoke `#eval` or `#reduce` here
#guard snoc [1] 2 == [1, 2]
#guard snoc [] 2 == [2]
#guard snoc [1,2,4] (-1 : ℤ) == [1, 2, 4, -1]

/- ## Question 2 (6 points): Sum

2.1 (3 points). Define a `sum` function that computes the sum of all the numbers
in a list. -/

def sum : List ℕ → ℕ
  | [] => 0
  | x :: xs => x + (sum xs)

#guard sum [1, 12, 3] == 16
#guard sum [1, 2, 3] == 6
#guard sum [] == 0

/- 2.2 (3 points). State (without proving them) the following properties of
`sum` as theorems. Schematically:

     sum (snoc ms n) = n + sum ms
     sum (ms ++ ns) = sum ms + sum ns
     sum (reverse ns) = sum ns

Try to give meaningful names to your theorems. Use `sorry` as the proof. -/

-- enter your theorem statements here

/-
def append (α : Type) : List α → List α → List α
  | List.nil,       ys => ys
  | List.cons x xs, ys => List.cons x (append α xs ys)
-/
theorem sum_append_eq_sum_add (ms ns : List ℕ) : sum (ms ++ ns) = sum ms + sum ns := by
  induction ms
  . unfold sum
    rw [zero_add]
    rfl
  . sorry

lemma cons_snoc_eq_snoc (x y : ℕ) (xs : List ℕ) : x :: snoc xs y = snoc (x :: xs) y := by
  induction xs generalizing x y
  . rfl
  . unfold snoc
    rw [tail_ih head y]

theorem eq_sum_snoc_add_sum (n : Nat) (ms : List Nat) : sum (snoc ms n) = n + sum ms := by
  induction ms
  . unfold snoc
    repeat (unfold sum)
    rfl
  . unfold snoc
    unfold snoc
    rcases tail with hd | tl
    . repeat (unfold sum)
      linarith
    . simp only
      unfold sum
      rw [cons_snoc_eq_snoc, tail_ih]
      linarith

theorem sum_reverse_eq_sum (ns : List ℕ) : sum (reverse ns) = sum ns := sorry


end LoVe
