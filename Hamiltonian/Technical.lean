import Mathlib

#check Subgroup.center
#check commutatorElement_def
#check Subgroup.closure

open scoped commutatorElement

/--
If `a, b ∈ G` and `⁅a, b⁆` lies in the center of `G`,
then for all `n ∈ ℕ`, `⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n`.
-/
lemma technical₁
    {G : Type*}
    [Group G]
    (a b : G)
    (h : ⁅a, b⁆ ∈ Subgroup.center G)
    (n : ℕ)
  : ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n := by
  induction n
  · simp
  · case succ n' in' =>
    rw [Subgroup.mem_center_iff] at h
    calc ⁅a ^ (n' + 1), b⁆
        = a ^ (n' + 1) * b * (a ^ (n' + 1))⁻¹ * b⁻¹ := by
          rw [commutatorElement_def]
      _ = a ^ n' * a * b * (a⁻¹ * (a ^ n')⁻¹) * b⁻¹ := by
          rw [pow_succ, mul_inv_rev]
      _ = a ^ n' * (a * b) * a⁻¹ * (a ^ n')⁻¹ * b⁻¹ := by
          simp only [mul_assoc]
      _ = a ^ n' * (a * b) * a⁻¹ * b⁻¹ * b * (a ^ n')⁻¹ * b⁻¹ := by
          rw [inv_mul_cancel_right]
      _ = a ^ n' * (a * b * a⁻¹ * b⁻¹) * b * (a ^ n')⁻¹ * b⁻¹ := by
          simp only [mul_assoc]
      _ = a ^ n' * ⁅a, b⁆ * b * (a ^ n')⁻¹ * b⁻¹ := by
          rw [commutatorElement_def a b]
      _ = ⁅a, b⁆ * a ^ n' * b * (a ^ n')⁻¹ * b⁻¹ := by
          rw [h]
      _ = ⁅a, b⁆ * (a ^ n' * b * (a ^ n')⁻¹ * b⁻¹) := by
          simp only [mul_assoc]
      _ = a ^ n' * b * (a ^ n')⁻¹ * b⁻¹ * ⁅a, b⁆ := by
          rw [h]
      _ = ⁅a ^ n', b⁆ * ⁅a, b⁆ := by
          rw [commutatorElement_def (a ^ n') b]
      _ = ⁅a, b⁆ ^ n' * ⁅a, b⁆ ^ 1 := by
          rw [in', pow_one]
      _ = ⁅a, b⁆ ^ (n' + 1) := by
          rw [pow_add]

/--
If `a, b ∈ G` and `⁅a, b⁆` lies in the center of `G`,
then for all `n ∈ ℕ`, `(a * b) ^ n = a ^ n * b ^ n * ⁅b, a⁆ ^ (n * (n - 1) / 2)`.

NOTE: proof done by Claude.
-/
lemma technical₂
    {G : Type*}
    [Group G]
    (a b : G)
    (h : ⁅a, b⁆ ∈ Subgroup.center G)
    (n : ℕ)
  : (a * b) ^ n = a ^ n * b ^ n * ⁅b, a⁆ ^ (n * (n - 1) / 2) := by
  have hba : ⁅b, a⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ h
  have exp_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n + n * (n - 1) / 2 := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ,
      Nat.choose_one_right]
  induction n
  · simp
  · case succ n' in' =>
    -- the powers of `⁅b, a⁆` we need are central
    have hk := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hba (n' * (n' - 1) / 2))
    have hn := Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hba n')
    calc (a * b) ^ (n' + 1)
        = (a * b) ^ n' * (a * b) := by
          rw [pow_succ]
      _ = a ^ n' * b ^ n' * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) * (a * b) := by
          rw [in']
      _ = a ^ n' * b ^ n' * (a * b) * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          rw [mul_assoc _ (⁅b, a⁆ ^ _), ← hk]
          simp only [mul_assoc]
      _ = a ^ n' * (⁅b ^ n', a⁆ * a * b ^ n') * b * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          simp only [commutatorElement_def]
          group
      _ = a ^ n' * (⁅b, a⁆ ^ n' * a * b ^ n') * b * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          rw [technical₁ b a hba n']
      _ = a ^ n' * ⁅b, a⁆ ^ n' * a * b ^ n' * b * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          simp only [mul_assoc]
      _ = ⁅b, a⁆ ^ n' * a ^ n' * a * b ^ n' * b * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          rw [hn]
      _ = ⁅b, a⁆ ^ n' * (a ^ n' * a * (b ^ n' * b)) * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          simp only [mul_assoc]
      _ = a ^ n' * a * (b ^ n' * b) * ⁅b, a⁆ ^ n' * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          rw [← hn]
      _ = a ^ (n' + 1) * b ^ (n' + 1) * ⁅b, a⁆ ^ (n' + n' * (n' - 1) / 2) := by
          rw [pow_succ, pow_succ, pow_add]
          simp only [mul_assoc]
      _ = a ^ (n' + 1) * b ^ (n' + 1) * ⁅b, a⁆ ^ ((n' + 1) * (n' + 1 - 1) / 2) := by
          rw [exp_succ]
