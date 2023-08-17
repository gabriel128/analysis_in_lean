import Natu.Defs

namespace Natu

open Natu

def add : Natu -> Natu -> Natu
  | zero, m => m
  | (succ n), m => Natu.succ (Natu.add n m)

instance : Add Natu where
  add := Natu.add

-- Adding the definitions as lemma 
lemma zero_add (m: Natu) : 0 + m = m := by rfl

lemma add_def (n: Natu) (m: Natu) : succ n + m = succ (n + m) := by rfl

lemma zero_is_0 : zero = 0:= by rfl

-- Lemma 2.2.2
lemma add_zero (n : Natu) : n + 0 = n := by
  apply math_induction n
  · rfl
  · intro ih
    rw [add_def, ih]
  qed

-- Lemma 2.2.3
lemma add_succ (n m : Natu) : n + succ m = succ (n + m) := by
  apply math_induction n
  · rfl
  · intro ih
    rw [add_def, ih]
    rfl
  qed

-- Corolaries from above
lemma one_succ_zero : 1 = succ 0 := by rfl

lemma succ_eq_plus_one (n : Natu) : succ n = n + 1 := by
  rw [one_succ_zero, add_succ, add_zero]
  qed

-- Proposition 2.2.4
theorem add_comm (n m : Natu) : n + m = m + n := by
  apply math_induction n
  · rw [zero_is_0, add_zero, zero_add]
  · intro ih
    rw [add_succ, <-ih, add_def]
  qed

-- Proposition 2.2.4
theorem add_assoc (a b c : Natu) : (a + b) + c = a + (b + c) := by
  apply math_induction c
  · rw [zero_is_0, add_zero, add_zero]
  · intro ih
    rw [add_succ, add_succ, add_succ, ih]
  qed

-- Proposition 2.2.6
theorem cancellation_law (a b c : Natu) : a + b = a + c -> b = c := by
  apply math_induction a
  · rw [zero_is_0, zero_add, zero_add]
    intro h
    exact h
  · intro ih
    intro h
    have h2 := succ_elim (a + b) (a + c)
    have h3 := h2 h
    exact ih h3
  qed
