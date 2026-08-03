import Mathlib

open_locale big_operators

example {a r : ℝ} (n : ℕ) (h : r ≠ 1) : ∑ i ∈ range (n+1), a * r^i = (a * r^(n+1) - a) / (r-1) := by
  sorry