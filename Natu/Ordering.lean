import Natu.Defs
import Natu.Add

namespace Natu

open Natu

def lte (a b : ℕ'): Prop :=  ∃ (c : ℕ'), b = a + c
def lt (a b : ℕ'): Prop :=  ∃ (c : ℕ'), b = a + c ∧ a ≠ b

instance: LE Natu where
  le := lte

instance: LT Natu where
  lt := lt

theorem lte_def_test : Natu.lte = (.≤.) := by rfl

theorem lte_def (a b : ℕ'): a ≤ b ↔ ∃ (c : ℕ'), b = a + c := by rfl

theorem lt_def (a b : ℕ'): a < b ↔ ∃ (c : ℕ'), b = a + c ∧ a ≠ b := by rfl

theorem gte_def (n m : ℕ'): m ≤ n ↔ ∃ (a : ℕ'), n = m + a := by rfl

theorem three_less_than_equal_four : (3: ℕ') ≤ 4 := by
  rw [lte_def]
  exists 1
  qed

theorem three_less_than_four : (3: ℕ') < 4 := by
  rw [lt_def]
  exists 1
  constructor
  · rfl
  · rw [Ne, Not]
    intro h
    have h1 : 2 = 3 := succ_elim _ _ h
    have h2 : 3 = 2 := Eq.symm h1
    exact three_not_eq_two h2
  qed

-- Proposition 2.2.12
-- a
theorem order_refl (a : ℕ') : a ≤ a := by
  rw [lte_def]
  exists 0
  rw [add_zero]
  qed

-- b
theorem order_trans (a b c : ℕ') (h1: a ≤ b) (h2: b ≤ c): a ≤ c := by
  rw [lte_def] at h1
  rw [lte_def] at h2
  rw [lte_def]
  let ⟨x, (h1': b = a + x)⟩ := h1
  let ⟨y, (h2': c = b + y)⟩ := h2
  rw [h1'] at h2'
  exists (x + y)
  rw [<-add_assoc]
  exact h2'
  qed

-- c
theorem order_antysymm (a b : ℕ') (h1: a ≤ b) (h2: b ≤ a) : a = b := by
  rw [lte_def] at h1
  rw [lte_def] at h2
  let ⟨x, (h1': b = a + x)⟩ := h1
  let ⟨y, (h2': a = b + y)⟩ := h2
  rw [h1', h2']
  have h3: x = 0 := by
    rw [h1', add_assoc] at h2'
    have h4 := add_zero_implies_zero a (x + y) h2'
    rw [zero_sum_implies_a_zero y, add_zero] at h4
    apply h4
    exact x
    rw [add_comm] at h4
    exact h4
  rw [h3, add_zero]
  qed
