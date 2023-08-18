import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Std.CodeAction
import Tactics

namespace Natu

inductive Natu where
  | zero : Natu
  | succ : Natu -> Natu
  deriving Repr

abbrev ℕ' := Natu

open Natu

def nat_into_natu : Nat -> Natu
  | .zero => zero
  | .succ n => succ (nat_into_natu n)

def nat_from_natu : Natu -> Nat
  | zero => Nat.zero
  | succ n => Nat.succ (nat_from_natu n)

instance: ToString Natu where
  toString n := toString (nat_from_natu n)

@[default_instance]
instance : OfNat Natu n where
  ofNat := nat_into_natu n

-- Axiom 2.3
axiom zero_is_not_succ : ∀ m : ℕ', succ m ≠ zero

-- Axiom 2.4
axiom succ_elim (m n : ℕ') : succ m = succ n → m = n

def Pred (t : Type u) : Type u := t → Prop
-- Axiom 2.5
axiom math_induction (n : ℕ') (P: ℕ' → Prop) (hzero : P zero): (P n → P (succ n)) -> P n

example : 3 ≠ 2 := by
  rw [Ne, Not]
  intro h
  have h1 : 2 = 1 := succ_elim _ _ h
  have h2 : 1 = 0 := succ_elim _ _ h1
  exact zero_is_not_succ zero h2
  qed

-- Definition 2.2.7
def Pos (n: ℕ'): Prop := n ≠ 0

axiom is_positive: ∀ (n: ℕ'), (Pos n) ↔ n ≠ 0
