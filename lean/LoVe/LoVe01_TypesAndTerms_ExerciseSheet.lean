/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a _b ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun f b a ↦ f a b

def projFst : α → α → α :=
  fun x _y ↦ x

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun _x y ↦ y

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  fun f a _ b ↦ (f a b)


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. Start with an empty context. You might find the
characters `–` (to draw horizontal bars) and `⊢` useful. -/

-- write your solution in a comment here or on paper

/-

Given by Cst:
f : α → (β → γ)
a : α
b : β

By App, f a : β → γ
By App, f a b : γ

By Curry, fun f a b ↦ τ is the anonymous function fun f ↦ (fun a ↦ (fun b ↦ f a b))

By Fun, fun b ↦ f a b : β → γ
By Fun, fun a ↦ (fun b ↦ f a b) : α → (β → γ)
By Fun, fun f ↦ (fun a ↦ (fun b ↦ f a b)) : (α → (β → γ)) → α → (β → γ)
                                          = (α → β → γ) → α → β → γ
QED

-/
end LoVe
