import Mathlib.Tactic.Basic
import Mathlib.Tactic.Cases
import Std.CodeAction

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

instance : OfNat Natu n where
  ofNat := nat_into_natu n

-- Axiom 2.3
axiom zero_is_not_succ : ∀ m : ℕ', succ m ≠ zero

-- Axiom 2.4
axiom succ_elim (m n : ℕ') : succ m = succ n → m = n

-- Axiom 2.5
axiom math_induction (n : ℕ') (P: ℕ' → Prop) (hzero : P zero): (P n → P (succ n)) -> P n


example : (3:ℕ') ≠ 2 := by
  rw [Ne, Not]
  have three_is_3: 3 = nat_into_natu 3 := by rfl
  have two_is_2: 2 = nat_into_natu 2 := by rfl
  rw [two_is_2, three_is_3]
  intro h
  have h1 : 2 = 1 := succ_elim _ _ h
  have h2 : 1 = 0 := succ_elim _ _ h1
  exact zero_is_not_succ zero h2
  done
