/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Homework 1 (10 points): Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1 (6 points): Terms

We start by declaring four new opaque types. -/

opaque α : Type
opaque β : Type
opaque γ : Type
opaque δ : Type

/- 1.1 (4 points). Complete the following definitions, by providing terms with
the expected type.

Please use reasonable names for the bound variables, e.g., `a : α`, `b : β`,
`c : γ`.

Hint: A procedure for doing so systematically is described in Section 1.4 of the
Hitchhiker's Guide. As explained there, you can use `_` as a placeholder while
constructing a term. By hovering over `_`, you will see the current logical
context. -/

def B : (α → β) → (γ → α) → γ → β :=
  fun f g c ↦ f (g c)

def S : (α → β → γ) → (α → β) → α → γ :=
  fun f g a ↦ f a (g a)

def moreNonsense : ((α → β) → γ → δ) → γ → β → δ :=
  fun f c b ↦ f (fun _ ↦ b) c

def evenMoreNonsense : (α → β) → (α → γ) → α → β → γ :=
  -- sorry for even more nonsense
  fun _f g a _b ↦ g a

/- 1.2 (2 points). Complete the following definition.

This one looks more difficult, but it should be fairly straightforward if you
follow the procedure described in the Hitchhiker's Guide.

Note: Peirce is pronounced like the English word "purse". -/

def weakPeirce : ((((α → β) → α) → α) → β) → β :=
  fun f ↦ f (fun g ↦ g (fun a ↦ f (fun _ ↦ a)))

/- ## Question 2 (4 points): Typing Derivation

Show the typing derivation for your definition of `B` above, using ASCII or
Unicode art. Start with an empty context. You might find the characters `–` (to
draw horizontal bars) and `⊢` useful.

Feel free to introduce abbreviations to avoid repeating large contexts `C`. -/

-- write your solution here

/-

def B : (α → β) → (γ → α) → γ → β :=
  fun f g c ↦ f (g c)

By Cst:
f : α → β
g : γ → α
c : γ
let C0 := {f : α → β, g : γ → α, c : γ ⊢ g c}

By App:
g : γ → α, c : γ ⊢ g c : α
g c : α, f : α → β ⊢ f (g c) : β

Derivation:

{}
---- Cst
C0

C0
---------------------- App
C0 ⊢ C_gc := g c : α

C1 := C0 ∪ C_gc
--------------------------- App
C1 ⊢ C_fgc := f (g c) : β

By def/curry: fun f g c => f (g c) is notation for:
              fun f => (fun g => (fun c => f (g c)))

C2 := C1 ∪ C_fgc
-------------------------------------------- Fun
C2 ⊢ C_fun_c := (fun c => f (g c)) : γ → β

C3 := C2 ∪ C_fun_c
------------------------------------------------------------------- Fun
C3 ⊢ C_fun_g := (fun g => (fun c => f (g c))) : (γ → α) → (γ → β)
                                              ≡ (γ → α) → γ → β

C4 := C3 ∪ C_fun_g
-------------------------------------------------------------------------- Fun
C4 ⊢ fun f => (fun g => (fun c => f (g c))) : (α → β) → ((γ → α) → γ → β)
                                            ≡ (α → β) → (γ → α) → g → β

Q.E.D

-/

end LoVe
