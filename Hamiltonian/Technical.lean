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

def squares (A : Type u) [CommGroup A] : Subgroup A where
  carrier := { x | ∃ a : A, a ^ 2 = x }
  mul_mem' := by
    intro a b ⟨a', ha⟩ ⟨b', hb⟩
    use a' * b'
    rw [mul_pow, ha, hb]
  one_mem' := by
    use 1
    rw [one_pow]
  inv_mem' := by
    intro x ⟨x', hx⟩
    use x'⁻¹
    rw [inv_pow, hx]

def two_torsion (A : Type u) [CommGroup A] : Subgroup A where
  carrier := { x | x ^ 2 = 1 }
  mul_mem' := by
    intro a b ha hb
    change (a * b) ^ 2 = 1
    change a ^ 2 = 1 at ha
    change b ^ 2 = 1 at hb
    rw [mul_pow, ha, hb, one_mul]
  one_mem' := by
    change 1 ^ 2 = 1
    rw [one_pow]
  inv_mem' := by
    intro x hx
    change (x⁻¹) ^ 2 = 1
    change x ^ 2 = 1 at hx
    rw [inv_pow, inv_eq_one, hx]



/--
If `A` is an abelian group such that
· orders of all elements are finite
· `A` does not contain an element of order `4`
then `A = U × V` where
· `U` is an abelian group in which all elements have odd orders
· `V` is an abelian group in which all elements have order `≤ 2`
-/
lemma technical₃
  (A : Type u)
  [CommGroup A]
  (h : ∀ a : A, orderOf a ≠ 0 ∧ orderOf a ≠ 4)
  :  ∃ U V : Subgroup A,
      (∀ x ∈ U, Odd (orderOf x)) ∧
      (∀ x ∈ V, x ^ 2 = 1) ∧
      Nonempty (A ≃* U × V) := by
  -- `A^2 = { a ^ 2 | a ∈ A }`
  use squares A
  -- `{ a | a ^ 2 = 1 }`
  use two_torsion A
  have hodd : ∀ x ∈ squares A, Odd (orderOf x) := by
    intro x ⟨ x', hx ⟩
    cases Nat.even_or_odd (orderOf x)
    · case inl heven =>
      obtain ⟨ k, hk ⟩ := even_iff_two_dvd.mp heven
      rcases k with _ | k
      · rw [mul_zero] at hk
        obtain ⟨ hfin, _ ⟩ := h x
        exfalso
        apply hfin
        exact hk
      · let z := x' ^ (k + 1)
        suffices hz : orderOf z = 4 by
          obtain ⟨ _, hz4 ⟩ := h z
          exfalso
          apply hz4
          exact hz
        rw [show 4 = 2 ^ (1 + 1) by omega]
        apply orderOf_eq_prime_pow
        · rw [pow_one]
          simp only [z]
          rw [← pow_mul, mul_comm, pow_mul, hx]
          exact pow_ne_one_of_lt_orderOf (Nat.succ_ne_zero k) (by omega)
        · simp only [z]
          rw [show 2 ^ (1 + 1) = 2 * 2 by omega]
          rw [
            ← pow_mul, 
            ← mul_assoc, 
            mul_comm, 
            ← mul_assoc, 
            pow_mul, 
            pow_mul, 
            hx, 
            ← pow_mul, 
            mul_comm, 
            ← hk
          ]
          exact pow_orderOf_eq_one x
    · assumption
  and_intros
  · exact hodd
  · intro x hx
    change x ^ 2 = 1 at hx
    exact hx
  · let μ : squares A × two_torsion A →* A := {
      toFun := fun p => (p.1 : A) * (p.2 : A)
      map_one' := by
        rw [Prod.fst_one, Prod.snd_one, OneMemClass.coe_one, OneMemClass.coe_one, mul_one]
      map_mul' := by
        intro p q
        rw [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, Subgroup.coe_mul]
        exact mul_mul_mul_comm _ _ _ _
    }
    suffices hμ : Function.Bijective μ by
      exact ⟨(MulEquiv.ofBijective μ hμ).symm⟩ 
    constructor
    · rw [injective_iff_map_eq_one]
      intro p hp
      obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := p
      change u * v = 1 at hp
      simp only [Prod.mk_eq_one, Subgroup.mk_eq_one]
      have hu₁ : u = 1 := by 
        have huv := eq_inv_of_mul_eq_one_left hp
        have hsq := congrArg (· ^ 2) huv
        change v ^ 2 = 1 at hv
        rw [inv_pow, hv, inv_one] at hsq
        have hordu := orderOf_dvd_of_pow_eq_one hsq
        have hordu' : orderOf u = 1 ∨ orderOf u = 2 := (Nat.dvd_prime Nat.prime_two).mp hordu
        cases hordu'
        · case inl h =>
          rw [← orderOf_eq_one_iff]
          exact h
        · case inr h => 
          have hodd₁ : Odd (orderOf u) := by apply hodd; assumption
          rw [h] at hodd₁
          contradiction
      constructor
      · exact hu₁
      · rw [hu₁, one_mul] at hp
        exact hp
    · intro x
      rcases Nat.even_or_odd (orderOf x) with heven | hodd'
      · obtain ⟨m, hm⟩ := heven
        rcases Nat.even_or_odd m with hmeven | hmodd
        · obtain ⟨j, hj⟩ := hmeven 
          rw [hj, show j + j + (j + j) = 4 * j by omega] at hm
          let z := x ^ j 
          have hordz : orderOf z = 4 := by
            simp only [z]
            rcases j with _ | j'
            · rw [mul_zero] at hm 
              specialize h x
              exfalso
              exact h.1 hm
            · rw [
                orderOf_pow_of_dvd (Nat.succ_ne_zero j') (by rw [hm]; exact Dvd.intro_left 4 rfl), 
                hm
              ]
              exact Nat.mul_div_cancel 4 (Nat.succ_pos j')
          exfalso
          specialize h z
          exact h.2 hordz
        · obtain ⟨j, hj⟩ := hmodd 
          have hu : x ^ (m + 1) ∈ squares A := by 
            use x ^ (j + 1)
            rw [← pow_mul, show (j + 1) * 2 = m + 1 by omega]
          have hv: x ^ m ∈ two_torsion A := by 
            change (x ^ m) ^ 2 = 1
            rw [← pow_mul, show m * 2 = orderOf x by omega, pow_orderOf_eq_one]
          use ⟨⟨x ^ (m + 1), hu⟩, ⟨x ^ m, hv⟩⟩ 
          change x ^ (m + 1) * x ^ m = x
          rw [
            ← pow_add, 
            show m + 1 + m = orderOf x + 1 by omega, 
            pow_succ, 
            pow_orderOf_eq_one, 
            one_mul
          ]
      · obtain ⟨m, hm⟩ := hodd'
        have hx : x ∈ squares A := by 
          use x ^ (m + 1)
          rw [
            ← pow_mul,  
            show (m + 1) * 2 = orderOf x + 1 by omega,
            pow_succ, 
            pow_orderOf_eq_one, one_mul
          ]
        use ⟨⟨x, hx⟩, 1⟩ 
        change x * 1 = x
        rw [mul_one]
