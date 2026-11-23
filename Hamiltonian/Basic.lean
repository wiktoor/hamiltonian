import Mathlib
import Hamiltonian.Technical

/-!
A group is `Hamiltonian` if
- it is non-abelian
- all its subgroups are normal.

The goal is each Hamiltonian group `H` is of form `Q × U × V` where
· `Q` is eight element quaternion group
· `U` is an abelian group such that all its elements have odd orders
· `V` is an abelian group with elements of orders at most `2`
-/

abbrev Q8 := QuaternionGroup 2

def i : Q8 := QuaternionGroup.a 1
def j : Q8 := QuaternionGroup.xa 0
def k : Q8 := QuaternionGroup.xa 1
def minus_one : Q8 := QuaternionGroup.a 2
def one : Q8 := QuaternionGroup.a 0

class NonAbelianGroup (G : Type*) [Group G] : Prop where
  exists_noncomm : ∃ a b : G, a * b ≠ b * a

class Hamiltonian (H : Type*) [Group H] extends NonAbelianGroup H where
  all_subgroups_normal : ∀ G : Subgroup H, G.Normal

theorem conj_eq_or_inv (x g : Q8) :
  g * x * g⁻¹ = x ∨ g * x * g⁻¹ = x⁻¹ := by
  revert x g
  -- proof by considering all 64 cases, decide does that for us
  decide

instance : Hamiltonian Q8 where
  exists_noncomm := by
    use i
    use j
    intro h
    injection h
    contradiction

  all_subgroups_normal := by
    intro G
    constructor
    intro n hn g
    cases conj_eq_or_inv n g
    · case inl h =>
      rw [h]
      exact hn
    · case inr h =>
      rw [h]
      exact G.inv_mem hn

section Hamiltonian

universe u

variable (H : Type u) [hgroup : Group H] [hamil : Hamiltonian H]

open scoped commutatorElement

/--
A group is Hamiltonian iff all its cyclic subgroups are Hamiltonian.
-/
theorem hamiltonian_iff (G : Type u) [Group G] :
    Hamiltonian G ↔ NonAbelianGroup G ∧ ∀ g : G, (Subgroup.zpowers g).Normal := by
  constructor
  · intro h
    constructor
    · exact h.toNonAbelianGroup
    · intro g
      exact h.all_subgroups_normal (Subgroup.zpowers g)
  · intro ⟨h, hcyc⟩
    constructor
    intro G
    constructor
    intro n hn g
    apply Subgroup.zpowers_le.mpr hn
    exact (hcyc n).conj_mem n (Subgroup.mem_zpowers n) g

/--
If every conjugate of `g` lies in `⟨g⟩`, then `⟨g⟩` is normal.
-/
lemma zpowers_normal_of_conj_mem {G : Type*} [Group G] (g : G)
    (h : ∀ x : G, x * g * x⁻¹ ∈ Subgroup.zpowers g) :
    (Subgroup.zpowers g).Normal := by
  constructor
  intro n hn x
  rw [Subgroup.mem_zpowers_iff] at hn
  rcases hn with ⟨ k, rfl ⟩
  rw [← conj_zpow]
  apply Subgroup.zpow_mem
  exact h x

/--
If a group is of form `Q₈ × U × V`, where
· `U` is abelian and all its elements have odd orders,
· `V` is abelian and all its elements have orders `≤ 2`,
then it is Hamiltonian.
-/
theorem hamiltonian_classification' (U V : CommGrpCat.{u})
    (hU : ∀ u : U, Odd (orderOf u))
    (hV : ∀ v : V, v ^ 2 = 1) :
    Hamiltonian (Q8 × U × V) := by
  rw [hamiltonian_iff]
  constructor
  · constructor
    use (i, 1, 1)
    use (j, 1, 1)
    -- too much calculation, used `simp?`
    simp only [Prod.mk_mul_mk, mul_one, ne_eq, Prod.mk.injEq, and_true]
    intro
    contradiction
  · intro ⟨ q, u, v ⟩
    apply zpowers_normal_of_conj_mem
    intro ⟨ q', u', v' ⟩
    simp only [Prod.mk_mul_mk, Prod.inv_mk, mul_inv_cancel_comm]
    cases conj_eq_or_inv q q'
    · case inl h =>
      rw [h]
      exact Subgroup.mem_zpowers (q, u, v)
    · case inr h =>
      rw [h]
      rw [Subgroup.mem_zpowers_iff]
      -- in the original proof, we use CRT to find the solution for `r ≡ -1 mod 4, r ≡ 1 mod ord u`
      -- it is easy to show that  `2 * ord u + 1` is a solution for this
      use ((2 * orderOf u + 1 : ℕ) : ℤ)
      simp only [zpow_natCast, Prod.pow_mk, Prod.mk.injEq]
      and_intros
      · obtain ⟨ l, hl ⟩ := hU u
        calc q ^ (2 * orderOf u + 1)
            _ = (q ^ 4) ^ l * q ^ 3 := by rw [hl, ← pow_mul, ← pow_add]; ring_nf
            _ = q⁻¹ := by
              rw [show ∀ q : Q8, q ^ 4 = 1 by decide, one_pow, one_mul,
                show ∀ q : Q8, q ^ 3 = q⁻¹ by decide]
      · calc u ^ (2 * orderOf u + 1)
            _ = (u ^ orderOf u) ^ 2 * u := by rw [pow_succ, pow_mul']
            _ = u := by rw [pow_orderOf_eq_one, one_pow, one_mul]
      · calc v ^ (2 * orderOf u + 1)
            _ = (v ^ 2) ^ orderOf u * v := by rw [pow_succ, pow_mul]
            _ = v := by rw [hV v, one_pow, one_mul]

/--
If `a ∈ H`, then for all `b ∈ H`, `⁅a, b⁆ ∈ ⟨a⟩`
-/
lemma hamiltonian_commutator_zpowers (a : H) : ∀ b : H, ⁅a, b⁆ ∈ Subgroup.zpowers a := by 
  intro b
  have zpowers_normal := hamil.all_subgroups_normal (Subgroup.zpowers a)
  obtain ⟨ hconj ⟩ := zpowers_normal
  rw [commutatorElement_def]
  specialize hconj a⁻¹ ((Subgroup.zpowers a).inv_mem (Subgroup.mem_zpowers a)) b
  rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
  exact (Subgroup.zpowers a).mul_mem (Subgroup.mem_zpowers a) hconj

/--
If `a, b ∈ H`, then `⁅a, b⁆` and `a` commute.
-/
lemma hamiltonian_commutator_comm_left (a b : H) : Commute ⁅a, b⁆ a := by
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (hamiltonian_commutator_zpowers H a b)
  rw [← hr]
  exact (Commute.refl a).zpow_left r

/--
Elements of a hamiltonian group that do not commute have finite orders.

NOTE: in the original proof, I proved that `c ^ |r| = 1` which would require handling cases when
`r > 0` and `r < 0` separately and messing with ℤ and ℕ at the same time. This approach appears to
be more readable.
-/
lemma hamiltonian_noncomm_finite_orders (a b : H) (hab : a * b ≠ b * a) : orderOf a ≠ 0 := by 
  let c := ⁅a, b⁆
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp (hamiltonian_commutator_zpowers H a b)
  have hca : Commute c a := by
    change Commute ⁅a, b⁆ a
    rw [← hr]
    exact (Commute.refl a).zpow_left r
  have hcb : Commute c b := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hamiltonian_commutator_zpowers H b a)
    rw [← commutatorElement_inv] at hk
    rw [← Commute.inv_left_iff]
    change Commute ⁅a, b⁆⁻¹ b
    rw [← hk]
    exact (Commute.refl b).zpow_left k
  have h : b * a * b⁻¹ = c⁻¹ * a := by
    simp only [c, commutatorElement_def]
    group
  have hcr : c ^ r = 1 := by
    have h' : c ^ (-r) * c = c := calc
      c ^ (-r) * c = c ^ (-r) * a ^ r := by rw [hr]
      _ = (c⁻¹ * a) ^ r := by rw [hca.inv_left.mul_zpow, inv_zpow']
      _ = b * a ^ r * b⁻¹ := by rw [← h, conj_zpow]
      _ = c := by rw [hr, ← hcb.eq, mul_inv_cancel_right]
    rw [mul_eq_right, zpow_neg, inv_eq_one] at h'
    exact h'
  have hr0 : r ≠ 0 := by
    intro rfl
    rw [zpow_zero, eq_comm, commutatorElement_eq_one_iff_mul_comm] at hr
    exact hab hr
  rw [orderOf_ne_zero_iff, isOfFinOrder_iff_zpow_eq_one]
  use r * r
  and_intros
  · exact mul_ne_zero hr0 hr0
  · rw [zpow_mul, hr]
    change c ^ r = 1
    assumption

/--
Each element of a hamiltonian group has finite order.
-/
lemma hamiltonian_finite_orders : ∀ h : H, orderOf h ≠ 0 := by 
  obtain ⟨a, b, hab⟩ := NonAbelianGroup.exists_noncomm (G := H)
  intro h
  by_cases hha : h * a = a * h
  · by_cases hhb : h * b = b * h 
    · have hhab : h * a * b ≠ b * (h * a) := by 
        intro hc
        apply hab
        apply mul_left_cancel (a := h)
        rw [← mul_assoc, hc, ← mul_assoc, ← hhb, mul_assoc]
      have h₁ := hamiltonian_noncomm_finite_orders H (h * a) b hhab
      have h₂ := hamiltonian_noncomm_finite_orders H a b hab
      rw [orderOf_ne_zero_iff] at h₁
      rw [orderOf_ne_zero_iff] at h₂
      have hc : Commute (h * a) a⁻¹ := (Commute.mul_left (a := h) hha (Commute.refl a)).inv_right
      have hfin := hc.isOfFinOrder_mul h₁ h₂.inv
      rw [mul_inv_cancel_right] at hfin
      rw [orderOf_ne_zero_iff]
      exact hfin
    · exact hamiltonian_noncomm_finite_orders H h b hhb
  · exact hamiltonian_noncomm_finite_orders H h a hha

theorem hamiltonian_classification : ∃ U V : Subgroup H,
    IsMulCommutative U ∧
    IsMulCommutative V ∧
    (∀ x : U, Odd (orderOf x)) ∧
    (∀ x : V, x ^ 2 = 1) ∧
    Nonempty (H ≃* Q8 × U × V) := by 
  -- define `a, b` as elements of `H` with minimal `ord a + ord b`
  -- we will argue that `a` and `b` are generators of `Q8`
  -- we need classical to make `hex` decidable
  classical 
  have hex : ∃ n, ∃ a b : H, a * b ≠ b * a ∧ orderOf a + orderOf b = n := by
    obtain ⟨a, b, hab⟩ := NonAbelianGroup.exists_noncomm (G := H)
    exact ⟨_, a, b, hab, rfl⟩
  obtain ⟨a, b, hab, hn⟩ := Nat.find_spec hex
  have hmin : ∀ x y : H, x * y ≠ y * x → orderOf a + orderOf b ≤ orderOf x + orderOf y := by
    intro x y hxy
    rw [hn]
    exact Nat.find_min' hex ⟨x, y, hxy, rfl⟩
  -- we proceed to prove that `ord ⁅a,b⁆ = p` for some prime `p`
  let c := ⁅a, b⁆
  have hc1 : c ≠ 1 := by
    rw [ne_eq, commutatorElement_eq_one_iff_mul_comm]
    exact hab
  have ha0 : orderOf a ≠ 0 := 
    hamiltonian_finite_orders H a
  have hb0 : orderOf b ≠ 0 :=
    hamiltonian_finite_orders H b
  have ha1 : orderOf a ≠ 1 := by
    rw [ne_eq, orderOf_eq_one_iff]
    intro ha
    rw [ha] at hab
    simp at hab
  obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
  have hap : a ^ p * b = b * a ^ p := by
    by_contra hne
    have h := hmin (a ^ p) b hne
    rw [orderOf_pow_of_dvd hp.ne_zero hpa] at h
    simp at h
    have h' := Nat.div_lt_self (Nat.pos_of_ne_zero ha0) hp.one_lt
    omega
  have hcq : ∀ q : ℕ, q.Prime → (q ∣ orderOf a) → c ^ q = 1 := by
    intro q hq hqa
    have h : b * a * b⁻¹ = ⁅a, b⁆⁻¹ * a := by
      rw [commutatorElement_def]
      group
    have haq : a ^ q * b = b * a ^ q := by
      by_contra hne
      have h := hmin (a ^ q) b hne
      rw [orderOf_pow_of_dvd hq.ne_zero hqa] at h
      simp at h
      have h' := Nat.div_lt_self (Nat.pos_of_ne_zero ha0) hq.one_lt
      omega
    have h' : ⁅a, b⁆⁻¹ ^ q * a ^ q = a ^ q := by
      rw [
        ← (Commute.inv_left (hamiltonian_commutator_comm_left H a b)).mul_pow,
        ← h,
        conj_pow,
        ← haq,
        mul_inv_cancel_right
      ]
    change ⁅a, b⁆ ^ q = 1
    rw [mul_eq_right, inv_pow, inv_eq_one] at h'
    exact h'
  have hcq' : ∀ q : ℕ, q.Prime → q ∣ orderOf b → c ^ q = 1 := by
    intro q hq hqb
    have hbq : a * b ^ q = b ^ q * a := by
      by_contra hne
      have h := hmin a (b ^ q) hne
      rw [orderOf_pow_of_dvd hq.ne_zero hqb] at h
      have h' := Nat.div_lt_self (Nat.pos_of_ne_zero hb0) hq.one_lt
      omega
    have hcb : Commute ⁅a, b⁆ b := by
      have := hamiltonian_commutator_comm_left H b a
      rwa [← commutatorElement_inv, Commute.inv_left_iff] at this
    have h : a * b * a⁻¹ = ⁅a, b⁆ * b := by
      rw [commutatorElement_def]; group
    have h' : ⁅a, b⁆ ^ q * b ^ q = b ^ q := by
      rw [← hcb.mul_pow, ← h, conj_pow, hbq, mul_inv_cancel_right]
    rwa [mul_eq_right] at h'
  have hcp : c ^ p = 1 := hcq p hp hpa 
  -- I don't really understand why it's needed but without it, hcp' won't work
  have := Fact.mk hp
  have hcp' : orderOf c = p := 
    orderOf_eq_prime hcp hc1
  -- now we will proceed to prove that `ord a = p ^ n` for some `n ∈ ℕ`
  -- and `ord b = p ^ m` for some `m ∈ ℕ`
  have hapow : ∃ n : ℕ, orderOf a = p ^ n := by
    use (orderOf a).primeFactorsList.length
    apply Nat.eq_prime_pow_of_unique_prime_dvd ha0
    intro q hq hqa
    have hpq : p ∣ q := hcp' ▸ orderOf_dvd_of_pow_eq_one (hcq q hq hqa)
    exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq).symm
  have hbpow : ∃ n : ℕ, orderOf b = p ^ n := by
    use (orderOf b).primeFactorsList.length
    apply Nat.eq_prime_pow_of_unique_prime_dvd hb0
    intro q hq hqb
    have hpq : p ∣ q := hcp' ▸ orderOf_dvd_of_pow_eq_one (hcq' q hq hqb)
    exact ((Nat.prime_dvd_prime_iff_eq hp hq).mp hpq).symm
  obtain ⟨n, hn⟩ := hapow
  obtain ⟨m, hm⟩ := hbpow
  sorry

