/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVelib


/- # LoVe Exercise 4: Forward Proofs -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Question 1: Connectives and Quantifiers

1.1. Supply structured proofs of the following theorems. -/

theorem I (a : Prop) :
    a → a :=
  assume ha : a
  show a from ha

theorem K (a b : Prop) :
    a → b → b := fun _ha hb => hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  assume hf : a → b → c
  assume hb : b
  assume ha : a
  show c from
    hf ha hb

theorem proj_fst (a : Prop) :
    a → a → a := fun ha _ => ha

/- Please give a different answer than for `proj_fst`. -/

theorem proj_snd (a : Prop) :
    a → a → a := fun ha _ => ha

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  fun _ ha hg _ => hg ha

/- 1.2. Supply a structured proof of the contraposition rule. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  assume hf : a → b
  assume hnb : b → False
  show a → False from
    fun ha => hnb (hf ha)

/- 1.3. Supply a structured proof of the distributivity of `∀` over `∧`. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by grind
  -- sorry  -- no thank you

/- 1.4 (**optional**). Supply a structured proof of the following property,
which can be used to pull a `∀` quantifier past an `∃` quantifier. -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume h : ∃x, ∀y, p x y
  let ⟨ x, hx ⟩ := h
  assume y : α
  have hepoxy : p x y := hx y
  show ∃x, p x y from
    Exists.intro x hepoxy

/- ## Question 2: Chain of Equalities

2.1. Write the following proof using `calc`.

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

Hint: This is a difficult question. You might need the tactics `simp` and
`ac_rfl` and some of the theorems `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, , and `Nat.two_mul`. -/

theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  grind  -- oh yeah

/- 2.2 (**optional**). Prove the same argument again, this time as a structured
proof, with `have` steps corresponding to the `calc` equations. Try to reuse as
much of the above proof idea as possible, proceeding mechanically. -/

theorem binomial_square₂ (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  by grind


/- ## Question 3 (**optional**): One-Point Rules

3.1 (**optional**). Prove that the following wrong formulation of the one-point
rule for `∀` is inconsistent, using a structured proof. -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

-- use `Bool` as the model to show inconsistency
theorem All.proof_of_False :
    False :=
  let α : Type := Bool
  let P : α → Prop := fun x => x = false
  have hp : P false := rfl
  have : P false → ∀x : α, x=false ∧ P x := (@All.one_point_wrong Bool false P).mpr
  have : ∀x : α, x=false ∧ P x := this hp
  have htf : true=false ∧ P true := this true
  have : ¬ (true = false) := by decide  -- how to avoid decide or simp?
  show False from
    this htf.1

/- 3.2 (**optional**). Prove that the following wrong formulation of the
one-point rule for `∃` is inconsistent, using a structured proof. -/

#check Empty

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

-- use `Bool` as the model to show inconsistency
theorem Exists.proof_of_False :
    False :=
  let α : Type := Bool
  let P : α → Prop := fun _ => False
  have h : (∃x: Bool, ¬ (x=true)) -> False := (Exists.one_point_wrong true P).mp
  have hf : ∃x: Bool, ¬ (x=true) := Exists.intro false (by decide)
  show False from
    h hf

end LoVe
