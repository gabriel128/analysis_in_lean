import Natu.Defs

namespace Natu

open Natu

def add : Natu -> Natu -> Natu
  | zero, m => m
  | (succ n), m => Natu.succ (Natu.add n m)

instance : Add Natu where
  add := Natu.add

-- Adding the definitions as lemma 
lemma zero_add (m: ℕ') : 0 + m = m := by rfl

lemma add_def (n: ℕ') (m: Natu) : succ n + m = succ (n + m) := by rfl

lemma zero_is_0 : zero = 0:= by rfl

-- Lemma 2.2.2
lemma add_zero (n : ℕ') : n + 0 = n := by
  apply math_induction n
  · rfl
  · intro ih
    rw [add_def, ih]
  qed

-- Lemma 2.2.3
lemma add_succ (n m : ℕ') : n + succ m = succ (n + m) := by
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
theorem add_comm (n m : ℕ') : n + m = m + n := by
  apply math_induction n
  · rw [zero_is_0, add_zero, zero_add]
  · intro ih
    rw [add_succ, <-ih, add_def]
  qed

-- Proposition 2.2.4
theorem add_assoc (a b c : ℕ') : (a + b) + c = a + (b + c) := by
  apply math_induction c
  · rw [zero_is_0, add_zero, add_zero]
  · intro ih
    rw [add_succ, add_succ, add_succ, ih]
  qed

-- Proposition 2.2.6
theorem cancellation_law (a b c : ℕ') : a + b = a + c -> b = c := by
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

-- Proposition 2.2.8
theorem positive_closure (a b : ℕ') (h1 : Pos a) : Pos (a + b) := by
  apply math_induction b
  · rw [zero_is_0, add_zero]
    exact h1
  · intro _
    rw [add_succ, Pos]
    by_contra h2
    apply zero_is_not_succ (a + b)
    exact h2
  qed

-- Corollary 2.2.9
lemma zero_sum_implies_a_zero (a b : ℕ'): a + b = 0 -> a = 0 := by
  intro (h: a + b = 0)
  by_contra h1
  have h2: Pos a := by
    rw [is_positive]
    exact h1
  have h3: Pos (a + b) := positive_closure a b h2
  exact h3 h
  qed

lemma zero_sum_implies_b_zero (a b : ℕ'): a + b = 0 -> b = 0 := by
  intro (h: a + b = 0)
  rw [add_comm] at h
  apply zero_sum_implies_a_zero b a
  assumption
  qed

theorem zero_sum_implies_zero (a b : ℕ'): a + b = 0 -> a = 0 ∧ b = 0 := by
  intro h
  have a' := zero_sum_implies_a_zero _ _ h
  have b' := zero_sum_implies_b_zero _ _ h
  exact ⟨a', b'⟩
  qed

lemma add_zero_implies_zero (a b : ℕ'): a = a + b -> b = 0 := by
  intro h
  rw [<-add_zero a, add_assoc, add_comm 0 b, <-add_assoc, add_zero (a + b)] at h
  have h1 := cancellation_law a 0 b h
  apply Eq.symm
  exact h1
  qed
