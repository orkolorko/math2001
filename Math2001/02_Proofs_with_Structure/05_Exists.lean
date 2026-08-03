/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' :=
      calc
        0 < -x * t := by addarith [hxt]
        _ = -1 * x * t := by ring
        _ = x * -t := by ring
    cancel x at hxt'
    apply ne_of_lt
    have : t < 0 := by addarith [hxt']

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6
  use 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a+1
  use a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q)/2
  constructor
  calc
    p = (p + p)/2 := by ring
    _ < (p + q)/2 := by rel [h]
  calc
    q = (q + q)/2 := by ring
    _ > (p + q)/2 := by rel [h]

example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 13/10
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 6
  use 7
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2
  constructor
  numbers
  numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 0
  use 0
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1/2
  calc
    (x+1/2)^2 = x^2 + 1/4 + x := by ring
    _ > x := by extra

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
sorry
--   obtain ⟨a, ha⟩ := h
--   have h3:= le_or_gt a 0
--   obtain le | gt := h3
--   calc

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  have h3:= le_or_succ_le a 2
  obtain le | gt := h3
  apply ne_of_lt
  calc
      m = 2 * a := by rw [ha]
      _ ≤ 2 * 2 := by rel [le]
      _ = 4 := by numbers
  numbers
  apply ne_of_gt
  calc
      m = 2 * a := by rw [ha]
      _ ≥ 2 * 3 := by rel [gt]
      _ = 6 := by numbers


example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  sorry
