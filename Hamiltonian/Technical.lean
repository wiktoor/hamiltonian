module

public import Mathlib

/-!
Technical lemmas used in the classification of Hamiltonian groups.
-/

@[expose] public section

#check commutatorElement_def
#check Subgroup.closure

open scoped commutatorElement

/--
If `a, b ∈ G` and `⁅a, b⁆` commutes with `a` and `b`,
then for all `n ∈ ℕ`, `⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n`.
-/
lemma technical₁
    {G : Type*}
    [Group G]
    (a b : G)
    (ha : Commute ⁅a, b⁆ a)
    (hb : Commute ⁅a, b⁆ b)
    (n : ℕ)
  : ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n := by
  induction n
  · simp
  · case succ n' in' =>
    have hX : Commute ⁅a, b⁆ (a ^ n' * b * (a ^ n')⁻¹ * b⁻¹) :=
      (((ha.pow_right n').mul_right hb).mul_right (ha.pow_right n').inv_right).mul_right
        hb.inv_right
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
          rw [← (ha.pow_right n').eq]
      _ = ⁅a, b⁆ * (a ^ n' * b * (a ^ n')⁻¹ * b⁻¹) := by
          simp only [mul_assoc]
      _ = a ^ n' * b * (a ^ n')⁻¹ * b⁻¹ * ⁅a, b⁆ := by
          rw [hX.eq]
      _ = ⁅a ^ n', b⁆ * ⁅a, b⁆ := by
          rw [commutatorElement_def (a ^ n') b]
      _ = ⁅a, b⁆ ^ n' * ⁅a, b⁆ ^ 1 := by
          rw [in', pow_one]
      _ = ⁅a, b⁆ ^ (n' + 1) := by
          rw [pow_add]

/--
If `a, b ∈ G` and `⁅a, b⁆` commutes with `a` and `b`,
then for all `n ∈ ℕ`, `(a * b) ^ n = a ^ n * b ^ n * ⁅b, a⁆ ^ (n * (n - 1) / 2)`.

NOTE: proof done by Claude.
-/
lemma technical₂
    {G : Type*}
    [Group G]
    (a b : G)
    (ha : Commute ⁅a, b⁆ a)
    (hb : Commute ⁅a, b⁆ b)
    (n : ℕ)
  : (a * b) ^ n = a ^ n * b ^ n * ⁅b, a⁆ ^ (n * (n - 1) / 2) := by
  have hba : Commute ⁅b, a⁆ b := by
    rw [← commutatorElement_inv]
    exact hb.inv_left
  have hba' : Commute ⁅b, a⁆ a := by
    rw [← commutatorElement_inv]
    exact ha.inv_left
  have exp_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n + n * (n - 1) / 2 := by
    rw [← Nat.choose_two_right, ← Nat.choose_two_right, Nat.choose_succ_succ,
      Nat.choose_one_right]
  induction n
  · simp
  · case succ n' in' =>
    -- the powers of `⁅b, a⁆` commute with everything we need
    have hk : Commute (⁅b, a⁆ ^ (n' * (n' - 1) / 2)) (a * b) :=
      (hba'.mul_right hba).pow_left _
    have hn : Commute (⁅b, a⁆ ^ n') (a ^ n' * a * (b ^ n' * b)) :=
      (((hba'.pow_left n').pow_right n').mul_right (hba'.pow_left n')).mul_right
        (((hba.pow_left n').pow_right n').mul_right (hba.pow_left n'))
    calc (a * b) ^ (n' + 1)
        = (a * b) ^ n' * (a * b) := by
          rw [pow_succ]
      _ = a ^ n' * b ^ n' * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) * (a * b) := by
          rw [in']
      _ = a ^ n' * b ^ n' * (a * b) * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          rw [mul_assoc _ (⁅b, a⁆ ^ _), hk.eq]
          simp only [mul_assoc]
      _ = a ^ n' * (⁅b ^ n', a⁆ * a * b ^ n') * b * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          simp only [commutatorElement_def]
          group
      _ = a ^ n' * (⁅b, a⁆ ^ n' * a * b ^ n') * b * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          rw [technical₁ b a hba hba' n']
      _ = a ^ n' * ⁅b, a⁆ ^ n' * a * b ^ n' * b * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          simp only [mul_assoc]
      _ = ⁅b, a⁆ ^ n' * a ^ n' * a * b ^ n' * b * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          rw [← ((hba'.pow_left n').pow_right n').eq]
      _ = ⁅b, a⁆ ^ n' * (a ^ n' * a * (b ^ n' * b)) * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          simp only [mul_assoc]
      _ = a ^ n' * a * (b ^ n' * b) * ⁅b, a⁆ ^ n' * ⁅b, a⁆ ^ (n' * (n' - 1) / 2) := by
          rw [hn.eq]
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

lemma technical₄ (A : Type u)
    [CommGroup A]
    (h : ∀ a : A, orderOf a ≠ 4)
    (a : A)
    (ha : orderOf a = 2)
  : ∃ B : Subgroup A, Subgroup.IsComplement' B (Subgroup.zpowers a) := by
    -- NOTE: done by Claude
    -- idea: `A ⧸ A²` is a vector space over `ZMod 2` in which `a` is nonzero,
    -- so some linear functional `φ` has `φ a ≠ 0`; then `B = ker φ` works
    classical
    have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha; omega
    have ha2 : a ^ 2 = 1 := ha ▸ pow_orderOf_eq_one a
    -- `a` is not a square, otherwise its square root would have order `4`
    have ha_sq : a ∉ squares A := by
      rintro ⟨x, hx⟩
      apply h x
      have hx4 : x ^ 4 = 1 := by rw [show 4 = 2 * 2 by rfl, pow_mul, hx, ha2]
      have hd : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
      have hnd : ¬ orderOf x ∣ 2 := fun hd2 => ha1 (hx ▸ orderOf_dvd_iff_pow_eq_one.mp hd2)
      have hle : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hd
      interval_cases (orderOf x) <;> simp_all
    -- `V = A ⧸ A²`, written additively, is a vector space over `ZMod 2`
    let V := Additive (A ⧸ squares A)
    have h2 : ∀ v : V, 2 • v = 0 := by
      intro v
      obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
      have hv : v = Additive.ofMul (QuotientGroup.mk y) := by rw [hy]; rfl
      rw [hv]
      change Additive.ofMul ((QuotientGroup.mk y : A ⧸ squares A) ^ 2) = Additive.ofMul 1
      rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff (y ^ 2)).mpr
        (show y ^ 2 ∈ squares A from ⟨y, rfl⟩)]
    let : Module (ZMod 2) V := AddCommGroup.zmodModule h2
    -- a linear functional `φ` not vanishing on `a`
    let π : A → V := fun x => Additive.ofMul (QuotientGroup.mk x)
    have hπmul : ∀ x y : A, π (x * y) = π x + π y := fun _ _ => rfl
    have hπa : π a ≠ 0 := fun h0 => ha_sq ((QuotientGroup.eq_one_iff a).mp h0)
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hπa
    let χ : A → ZMod 2 := fun x => φ (π x)
    have hχmul : ∀ x y : A, χ (x * y) = χ x + χ y := fun x y => by
      simp only [χ, hπmul, map_add]
    have hχ1 : χ 1 = 0 := by
      have : π 1 = 0 := rfl
      simp only [χ, this, map_zero]
    have hχa : χ a = 1 := by
      have : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
      exact this _ hφ
    -- `B = ker χ`
    let B : Subgroup A :=
      { carrier := { x | χ x = 0 }
        mul_mem' := fun {x y} hx hy => by
          have hx : χ x = 0 := hx
          have hy : χ y = 0 := hy
          change χ (x * y) = 0
          rw [hχmul, hx, hy, add_zero]
        one_mem' := hχ1
        inv_mem' := fun {x} hx => by
          have hx : χ x = 0 := hx
          change χ x⁻¹ = 0
          have := hχmul x x⁻¹
          rw [mul_inv_cancel, hχ1, hx, zero_add] at this
          exact this.symm }
    refine ⟨B, Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_⟩
    · -- `B ∩ ⟨a⟩ = 1`, since `⟨a⟩ = {1, a}` and `a ∉ B`
      rw [Subgroup.disjoint_def]
      intro x hxB hxa
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxa
      rw [← zpow_mod_orderOf, ha]
      rcases Int.emod_two_eq_zero_or_one k with hk | hk
      · rw [show ((2 : ℕ) : ℤ) = 2 by rfl, hk, zpow_zero]
      · exfalso
        change χ (a ^ k) = 0 at hxB
        rw [← zpow_mod_orderOf, ha, show ((2 : ℕ) : ℤ) = 2 by rfl, hk, zpow_one, hχa] at hxB
        exact one_ne_zero hxB
    · -- every `x` is `x * 1` or `(x * a) * a` with the first factor in `B`
      refine Set.eq_univ_of_forall fun x => ?_
      by_cases hx : χ x = 0
      · exact ⟨x, hx, 1, Subgroup.one_mem _, mul_one x⟩
      · refine ⟨x * a, ?_, a, Subgroup.mem_zpowers a, ?_⟩
        · change χ (x * a) = 0
          have : ∀ z : ZMod 2, z ≠ 0 → z = 1 := by decide
          rw [hχmul, this _ hx, hχa]
          rfl
        · change x * a * a = x
          rw [mul_assoc, ← sq, ha2, mul_one]
