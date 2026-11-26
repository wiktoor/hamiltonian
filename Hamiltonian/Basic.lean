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

open scoped commutatorElement in
/--
Another presentation of the quaternion group
`Q8 = ⟨x, y | x ^ 2 = y ^ 2 = ⁅x, y⁆, ⁅x, y⁆ ^ 2 = 1⟩`.
The extra assumption `⁅x, y⁆ ≠ 1` makes the homomorphism injective
(otherwise e.g. `x = y = 1` satisfies the relations).

NOTE: proof done by Claude.
-/
lemma quaternion_embedding {G : Type*} [Group G] (x y : G)
    (h1 : x ^ 2 = y ^ 2) (h2 : x ^ 2 = ⁅x, y⁆) (h3 : ⁅x, y⁆ ^ 2 = 1) (h4 : ⁅x, y⁆ ≠ 1) :
    ∃ φ : Q8 →* G, Function.Injective φ ∧ φ i = x ∧ φ j = y := by
  -- first we derive `x ^ 4 = 1`, `x ^ 2 = y ^ 2` and `y * x * y⁻¹ = x⁻¹`
  have hx : orderOf x = 4 := by
    rw [show 4 = 2 ^ (1 + 1) by norm_num]
    apply orderOf_eq_prime_pow
    · rw [pow_one, h2]
      exact h4
    · rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, h2, h3]
  have hy : y ^ 2 = x ^ 2 := h1.symm
  have hxy : y * x * y⁻¹ = x⁻¹ := by
    have h : x * y * x⁻¹ * y⁻¹ = x ^ 2 := by rw [← commutatorElement_def, h2]
    calc y * x * y⁻¹ = (x⁻¹ * (x * y * x⁻¹ * y⁻¹))⁻¹ := by group
      _ = x⁻¹ := by rw [h]; group
  -- powers of `x` only depend on the exponent mod `4`
  have key : ∀ m n : ℕ, (m : ZMod (2 * 2)) = n → x ^ m = x ^ n := by
    intro m n h
    rw [pow_eq_pow_iff_modEq, hx]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h
  have hinv : x⁻¹ = x ^ 3 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', show 3 + 1 = orderOf x by omega, pow_orderOf_eq_one]
  -- moving `y` past powers of `x`
  have hs1 : SemiconjBy y x x⁻¹ := by
    unfold SemiconjBy
    rw [← hxy]
    group
  have hs2 : SemiconjBy y x⁻¹ x := by
    simpa using hs1.inv_right
  have hB : ∀ n : ℕ, y * x⁻¹ ^ n = x ^ n * y := fun n => (hs2.pow_right n).eq
  let φ : Q8 →* G := {
    toFun := fun q => match q with
      | .a k => x ^ k.val
      | .xa k => y * x ^ k.val
    map_one' := by
      change x ^ (0 : ZMod (2 * 2)).val = 1
      rw [ZMod.val_zero, pow_zero]
    map_mul' := by
      rintro (i | i) (j | j)
      · change x ^ (i + j).val = x ^ i.val * x ^ j.val
        rw [← pow_add]
        apply key
        revert i j
        decide
      · change y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
        rw [← mul_assoc, ← hB, hinv, ← pow_mul, mul_assoc, ← pow_add]
        congr 1
        apply key
        revert i j
        decide
      · change y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
        rw [mul_assoc, ← pow_add]
        congr 1
        apply key
        revert i j
        decide
      · change x ^ ((2 : ℕ) + j - i : ZMod (2 * 2)).val = y * x ^ i.val * (y * x ^ j.val)
        rw [← mul_assoc, mul_assoc y, ← hB, ← mul_assoc y y, ← sq y, hy, hinv, ← pow_mul,
          ← pow_add, ← pow_add]
        apply key
        revert i j
        decide
  }
  refine ⟨φ, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    rintro (k | k) h
    · -- `x ^ k = 1` with `k < 4 = orderOf x` forces `k = 0`
      change x ^ k.val = 1 at h
      have hdvd := orderOf_dvd_of_pow_eq_one h
      rw [hx] at hdvd
      have hlt := ZMod.val_lt k
      have hk : k.val = 0 := by omega
      rw [ZMod.val_eq_zero] at hk
      rw [hk]
      rfl
    · -- `y * x ^ k = 1` would make `y` a power of `x`, so `x = x⁻¹`, contradicting `orderOf x = 4`
      exfalso
      change y * x ^ k.val = 1 at h
      rw [eq_inv_of_mul_eq_one_left h] at hxy
      have hxx : x = x⁻¹ := by
        rw [← hxy]
        group
      have h2 : x ^ 2 = 1 := by
        calc x ^ 2 = x * x := sq x
          _ = x * x⁻¹ := by rw [← hxx]
          _ = 1 := mul_inv_cancel x
      have hdvd := orderOf_dvd_of_pow_eq_one h2
      rw [hx] at hdvd
      omega
  · change x ^ (1 : ZMod (2 * 2)).val = x
    rw [show (1 : ZMod (2 * 2)).val = 1 from rfl, pow_one]
  · change y * x ^ (0 : ZMod (2 * 2)).val = y
    rw [ZMod.val_zero, pow_zero, mul_one]

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

/--
A hamiltonian group `H` contains `a` and `b` such that `⟨a, b⟩ = Q8` and `c = ⁅a, b⁆`.
-/
lemma hamiltonian_contains_quaternion : ∃ a b c : H, 
    a * b ≠ b * a ∧
    (∀ (x y : H), x * y ≠ y * x → orderOf a + orderOf b ≤ orderOf x + orderOf y) ∧
    c = ⁅a, b⁆ ∧
    c ≠ 1 ∧
    orderOf c = 2 ∧
    orderOf a = 4 ∧
    orderOf b = 4 ∧
    c = a ^ 2 ∧
    c = b ^ 2 := by 
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
  clear hn
  -- WLOG, we assume that `ord b ≤ ord a`. 
  -- otherwise, we would have to follow the same reasoning twice
  wlog hle : orderOf b ≤ orderOf a generalizing a b
  · apply this b a (Ne.symm hab)
    · intro x y hxy
      rw [add_comm]
      exact hmin x y hxy
    · omega
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
  have hb1 : orderOf b ≠ 1 := by
    rw [ne_eq, orderOf_eq_one_iff]
    intro hb
    rw [hb] at hab
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
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, pow_zero] at hn
    exact ha1 hn
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, pow_zero] at hm
    exact hb1 hm
  have hcj : ∃ j : ℕ, ¬ p ∣ j ∧ c = a ^ (j * p ^ (n - 1)) := by
    have hmem : c ∈ Submonoid.powers a := 
      (orderOf_ne_zero_iff.mp ha0).mem_powers_iff_mem_zpowers.mpr 
        (hamiltonian_commutator_zpowers H a b)
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
    have hdvd : p ^ (n - 1) * p ∣ k * p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), ← hn]
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, hk, hcp]
    obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd
    use j
    and_intros
    · rintro ⟨ i, rfl ⟩ 
      apply hc1
      rw [
        ← hk, 
        hj, 
        ← mul_assoc, 
        ← pow_succ, 
        Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0), 
        ← hn, 
        pow_mul, 
        pow_orderOf_eq_one, 
        one_pow
      ]
    · rw [← hk, hj, mul_comm]
  have hck : ∃ k : ℕ, ¬ p ∣ k ∧ c = b ^ (k * p ^ (m - 1)) := by
    have hmem : c ∈ Submonoid.powers b := by
      have h := Subgroup.inv_mem _ (hamiltonian_commutator_zpowers H b a)
      rw [commutatorElement_inv] at h
      exact (orderOf_ne_zero_iff.mp hb0).mem_powers_iff_mem_zpowers.mpr h
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp hmem
    have hdvd : p ^ (m - 1) * p ∣ k * p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← hm]
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, hk, hcp]
    obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_right hp.pos hdvd
    use j
    and_intros
    · rintro ⟨ i, rfl ⟩ 
      apply hc1
      rw [
        ← hk, 
        hj, 
        ← mul_assoc, 
        ← pow_succ, 
        Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), 
        ← hm, 
        pow_mul, 
        pow_orderOf_eq_one, 
        one_pow
      ]
    · rw [← hk, hj, mul_comm]
  obtain ⟨j, ⟨hjp, hjc⟩⟩ := hcj
  obtain ⟨k, ⟨hkp, hkc⟩⟩ := hck
  let b' := a⁻¹ ^ (j * p ^ (n - m)) * b ^ k
  -- the orginal work shows that `⟨a, b⟩ = ⟨a, b'⟩` from which it easily follows that 
  -- a and b' do not commute. it turned out to be lengthy and Claude found a much
  -- more concise argument
  -- NOTE: done by Claude (but the statement)
  have hab'_noncomm : a * b' ≠ b' * a := by
    intro h
    apply hab
    have hx : Commute a (a⁻¹ ^ (j * p ^ (n - m))) :=
      (Commute.refl a).inv_right.pow_right _
    have hbk : Commute a (b ^ k) := by
      have h' : Commute a ((a⁻¹ ^ (j * p ^ (n - m)))⁻¹ * (a⁻¹ ^ (j * p ^ (n - m)) * b ^ k)) :=
        hx.inv_right.mul_right h
      rwa [inv_mul_cancel_left] at h'
    have hcop : Nat.Coprime k (orderOf b) := by
      rw [hm]
      exact Nat.Coprime.pow_right m 
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hkp))
    have hb1' : 1 < orderOf b := by omega
    obtain ⟨l, -, hl⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hb1'
    have h'' := hbk.pow_right l
    rw [← pow_mul, ← pow_mod_orderOf, hl, pow_one] at h''
    exact h''
  -- an extremely messy and technical, but simple: straighforwardly apply `technical₂` and then 
  -- perform basic algebra
  -- NOTE: done by Claude (but the statement)
  have heq : b' ^ (p ^ (m - 1)) = c ^ (j * k * p ^ (n - 1) * (p ^ (m - 1) - 1) / 2) := by
    have hca : Commute c a := hamiltonian_commutator_comm_left H a b
    have hcb : Commute c b := by
      have := hamiltonian_commutator_comm_left H b a
      rwa [← commutatorElement_inv, Commute.inv_left_iff] at this
    have hmn : m ≤ n := by
      rw [hm, hn] at hle
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    -- `⁅a⁻¹, b⁆ = c⁻¹`
    have h1 : ⁅a⁻¹, b⁆ = c⁻¹ := by
      calc ⁅a⁻¹, b⁆ = a⁻¹ * (c⁻¹ * a) := by
            simp only [c, commutatorElement_def]; group
        _ = c⁻¹ := by rw [hca.inv_left.eq, inv_mul_cancel_left]
    -- `⁅b, a⁻¹ ^ J⁆ = c ^ J`
    have h2 : ⁅b, a⁻¹ ^ (j * p ^ (n - m))⁆ = c ^ (j * p ^ (n - m)) := by
      rw [← commutatorElement_inv, technical₁ a⁻¹ b (h1 ▸ hca.inv_left.inv_right)
        (h1 ▸ hcb.inv_left), h1, inv_pow, inv_inv]
    -- `⁅b ^ k, a⁻¹ ^ J⁆ = c ^ (J * k)`
    have h3 : ⁅b ^ k, a⁻¹ ^ (j * p ^ (n - m))⁆ = c ^ (j * p ^ (n - m) * k) := by
      rw [technical₁ b _ (h2 ▸ hcb.pow_left _)
        (h2 ▸ (hca.inv_right.pow_right _).pow_left _), h2, ← pow_mul]
    have hx : Commute (c ^ (j * p ^ (n - m) * k)) (a⁻¹ ^ (j * p ^ (n - m))) :=
      (hca.inv_right.pow_right _).pow_left _
    have hy : Commute (c ^ (j * p ^ (n - m) * k)) (b ^ k) := (hcb.pow_right _).pow_left _
    have hexp : p ^ (n - m) * p ^ (m - 1) = p ^ (n - 1) := by
      rw [← pow_add]; congr 1; omega
    change (a⁻¹ ^ (j * p ^ (n - m)) * b ^ k) ^ p ^ (m - 1) = _
    rw [technical₂ _ _ (by rw [← commutatorElement_inv, h3]; exact hx.inv_left)
      (by rw [← commutatorElement_inv, h3]; exact hy.inv_left), h3]
    -- the `a`- and `b`-parts cancel
    rw [← pow_mul, ← pow_mul, inv_pow, mul_assoc j, hexp, ← hjc, ← hkc, inv_mul_cancel,
      one_mul, ← pow_mul]
    -- exponent arithmetic
    congr 1
    have h2 : 2 ∣ p ^ (m - 1) * (p ^ (m - 1) - 1) := (Nat.even_mul_pred_self _).two_dvd
    rw [← Nat.mul_div_assoc _ h2]
    congr 1
    rw [← hexp]
    ring
  -- NOTE: done by Claude (but the statement)
  have hp_nmid : ¬ p ∣ j * k * p ^ (n - 1) * (p ^ (m - 1) - 1) / 2 := by
    intro hdvd
    -- by minimality, `orderOf b ≤ orderOf b'`
    have hmin' := hmin a b' hab'_noncomm
    -- if `p` divides the exponent, then `b' ^ (p ^ (m - 1)) = c ^ (p * t) = 1`
    have hb'1 : b' ^ (p ^ (m - 1)) = 1 := by
      obtain ⟨t, ht⟩ := hdvd
      rw [heq, ht, pow_mul, hcp, one_pow]
    -- so `orderOf b' ≤ p ^ (m - 1) < p ^ m = orderOf b`
    have hle' : orderOf b' ≤ p ^ (m - 1) :=
      Nat.le_of_dvd (pow_pos hp.pos _) (orderOf_dvd_of_pow_eq_one hb'1)
    have hlt : p ^ (m - 1) < p ^ m := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega
  -- NOTE: done by Claude (but the statement)
  have hn2m2p2 : n = 2 ∧ m = 2 ∧ p = 2 := by
    have hmn : m ≤ n := by
      rw [hm, hn] at hle
      exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    -- `m = 1` (and in particular `n = 1`) is impossible: the exponent is `0`
    have hm2 : 2 ≤ m := by
      by_contra hm1
      apply hp_nmid
      rw [show m = 1 by omega]
      simp
    -- `p` odd is impossible: `p ^ (m - 1) - 1` is even, so `p ∣ p ^ (n - 1)` divides the exponent
    have hp2 : p = 2 := by
      by_contra hp2
      apply hp_nmid
      have h2 : 2 ∣ p ^ (m - 1) - 1 :=
        (Nat.Odd.sub_odd ((hp.odd_of_ne_two hp2).pow) odd_one).two_dvd
      rw [Nat.mul_div_assoc _ h2]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow_self p (by omega)) _) _
    -- `p = 2` and `n ≥ 3` is impossible: `2 ^ (n - 1) / 2` is still even
    have hn2 : n = 2 := by
      by_contra hn2
      apply hp_nmid
      rw [hp2]
      have h : j * k * 2 ^ (n - 1) * (2 ^ (m - 1) - 1)
          = (j * k * 2 ^ (n - 3) * (2 ^ (m - 1) - 1) * 2) * 2 := by
        rw [show n - 1 = n - 3 + 2 by omega, pow_add]
        ring
      rw [h, Nat.mul_div_cancel _ two_pos]
      exact dvd_mul_left 2 _
    -- `2 ≤ m ≤ n = 2`
    exact ⟨hn2, by omega, hp2⟩

  -- assumption decluttering -> replace n, m, p with 2 and j, k with 1
  -- from now on `n = m = p = 2`
  obtain ⟨rfl, rfl, rfl⟩ := hn2m2p2
  norm_num at hn hm hjc hkc heq hcp hcp'
  -- `b'` simplifies to `a⁻¹ ^ j * b ^ k`; we forget its definition and keep only this equation
  have hb'_def : b' = a⁻¹ ^ j * b ^ k := by
    simp only [b', Nat.sub_self, pow_zero, mul_one]
  clear_value b'
  -- these were only needed to derive `n = m = p = 2`, or follow from `hn` and `hm`
  clear hn0 hm0 hp_nmid hpa hap hcq hcq' this hp ha0 hb0 ha1 hb1 hle hex
  -- `j` and `k` are odd, so they only matter mod `4` (for `a`, `b`) or mod `2` (for `c`)
  have hc_a : c = a ^ 2 := by
    rw [hjc, pow_eq_pow_iff_modEq, hn]
    unfold Nat.ModEq
    omega
  have hc_b : c = b ^ 2 := by
    rw [hkc, pow_eq_pow_iff_modEq, hm]
    unfold Nat.ModEq
    omega
  have hb'2 : b' ^ 2 = a ^ 2 := by
    have hjk : j * k % 2 = 1 :=
      Nat.odd_iff.mp (Nat.odd_mul.mpr ⟨Nat.odd_iff.mpr (by omega), Nat.odd_iff.mpr (by omega)⟩)
    rw [heq, ← pow_mod_orderOf, hcp', hjk, pow_one, hc_a]
  have hcomm : ⁅a, b'⁆ = c := by
    have hca : Commute c a := hamiltonian_commutator_comm_left H a b
    have hcb : Commute c b := by
      have := hamiltonian_commutator_comm_left H b a
      rwa [← commutatorElement_inv, Commute.inv_left_iff] at this
    have hck : c ^ k = c := by
      rw [← pow_mod_orderOf, hcp', show k % 2 = 1 by omega, pow_one]
    have h1 : ⁅b ^ k, a⁆ = c⁻¹ ^ k := by
      rw [technical₁ b a (by rw [← commutatorElement_inv]; exact hcb.inv_left)
        (by rw [← commutatorElement_inv]; exact hca.inv_left) k, ← commutatorElement_inv]
    have h2 : ⁅a, b ^ k⁆ = c := by
      rw [← commutatorElement_inv, h1, inv_pow, inv_inv, hck]
    rw [hb'_def]
    calc ⁅a, a⁻¹ ^ j * b ^ k⁆ = a⁻¹ ^ j * ⁅a, b ^ k⁆ * (a⁻¹ ^ j)⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = c := by rw [h2, ← (hca.inv_right.pow_right j).eq, mul_inv_cancel_right]
  -- `j`, `k` are no longer needed
  clear hb'_def heq hjc hkc hjp hkp j k
  use a
  use b
  use c

theorem hamiltonian_classification : ∃ U V : Subgroup H,
    IsMulCommutative U ∧
    IsMulCommutative V ∧
    (∀ x : U, Odd (orderOf x)) ∧
    (∀ x : V, x ^ 2 = 1) ∧
    Nonempty (H ≃* Q8 × U × V) := by 
  obtain ⟨ a, b, c, hab, hmin, hc, hc1, hcp, hn, hm, hc_a, hc_b ⟩ := 
    hamiltonian_contains_quaternion H

  -- `Q` is the quaternion subgroup in H
  -- `Z` is its centralizer
  let Q : Subgroup H := Subgroup.closure { a, b }
  let Z : Subgroup H := Subgroup.centralizer { a, b }

  -- we want to show that `H = Q · Z = { q · z | q ∈ Q, z ∈ Z } `
  -- note that `Q · Z` must not be a group in general
  -- therefore we use `Q ⊔ Z` which is the smallest subgroup containing Q and Z
  -- the two are the same if one of the two subgroups is normal
  -- which is true for `Z`
  -- NOTE: done by Claude
  have hcomm_of : ∀ z g : H, z⁻¹ * g * z = g → Commute z g := by
    intro z g h
    change z * g = g * z
    calc z * g = z * (z⁻¹ * g * z) := by rw [h]
      _ = g * z := by group
  -- step 1: an element of order `4` is inverted by everything it does not commute with
  have hinv : ∀ g x : H, g ^ 2 ≠ 1 → g ^ 4 = 1 → ¬ Commute x g → x⁻¹ * g * x = g⁻¹ := by
    intro g x hg2 hg4 hxg
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp
      ((hamil.all_subgroups_normal (Subgroup.zpowers g)).conj_mem g (Subgroup.mem_zpowers g) x⁻¹)
    have ht' : g ^ (t % 4) = x⁻¹ * g * x⁻¹⁻¹ := by
      rw [← ht]
      conv_rhs => rw [← Int.emod_add_ediv_mul t 4]
      rw [zpow_add, zpow_mul', show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast, hg4,
        one_zpow, mul_one]
    rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with h | h | h | h <;>
      rw [h] at ht'
    · have hg : g = 1 := conj_eq_one_iff.mp (by rw [← ht', zpow_zero])
      exact absurd (by rw [hg, one_pow]) hg2
    · rw [zpow_one, inv_inv] at ht'
      exact absurd (hcomm_of x g ht'.symm) hxg
    · exfalso
      apply hg2
      have : x⁻¹ * g ^ 2 * x⁻¹⁻¹ = 1 := by
        rw [← conj_pow, ← ht', ← zpow_natCast, ← zpow_mul]
        norm_num
        exact hg4
      exact conj_eq_one_iff.mp this
    · rw [inv_inv] at ht'
      rw [← ht']
      apply eq_inv_of_mul_eq_one_left
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, ← pow_succ, hg4]
  have hc2 : c ^ 2 = 1 := hcp ▸ pow_orderOf_eq_one c
  have ha2 : a ^ 2 ≠ 1 := hc_a ▸ hc1
  have ha4 : a ^ 4 = 1 := by rw [show 4 = 2 * 2 by rfl, pow_mul, ← hc_a, hc2]
  have hb2 : b ^ 2 ≠ 1 := hc_b ▸ hc1
  have hb4 : b ^ 4 = 1 := by rw [show 4 = 2 * 2 by rfl, pow_mul, ← hc_b, hc2]
  have hab_b : a⁻¹ * b⁻¹ * a = b := by
    rw [show a⁻¹ * b⁻¹ * a = (a⁻¹ * b * a)⁻¹ by group,
      hinv b a hb2 hb4 (fun h => hab h.eq), inv_inv]
  have hba_a : b⁻¹ * a⁻¹ * b = a := by
    rw [show b⁻¹ * a⁻¹ * b = (b⁻¹ * a * b)⁻¹ by group,
      hinv a b ha2 ha4 (fun h => hab h.eq.symm), inv_inv]
  have hmemZ : ∀ z : H, z ∈ Z ↔ Commute z a ∧ Commute z b := by
    intro z
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1.eq.symm, h2.eq.symm⟩⟩

  have hqz : Q ⊔ Z = ⊤ := by
    -- step 2: one of `x`, `x * a`, `x * b`, `x * b * a` lies in `Z`
    have hstep2 : ∀ x : H, x ∈ Z ∨ x * a ∈ Z ∨ x * b ∈ Z ∨ x * b * a ∈ Z := by
      intro x
      by_cases hxa : Commute x a <;> by_cases hxb : Commute x b
      · exact Or.inl ((hmemZ x).mpr ⟨hxa, hxb⟩)
      · refine Or.inr (Or.inl ((hmemZ _).mpr ⟨hxa.mul_left (Commute.refl a), ?_⟩))
        apply hcomm_of
        rw [show (x * a)⁻¹ * b * (x * a) = a⁻¹ * (x⁻¹ * b * x) * a by group,
          hinv b x hb2 hb4 hxb, hab_b]
      · refine Or.inr (Or.inr (Or.inl ((hmemZ _).mpr ⟨?_, hxb.mul_left (Commute.refl b)⟩)))
        apply hcomm_of
        rw [show (x * b)⁻¹ * a * (x * b) = b⁻¹ * (x⁻¹ * a * x) * b by group,
          hinv a x ha2 ha4 hxa, hba_a]
      · refine Or.inr (Or.inr (Or.inr ((hmemZ _).mpr ⟨?_, ?_⟩))) <;> apply hcomm_of
        · rw [show (x * b * a)⁻¹ * a * (x * b * a) = a⁻¹ * (b⁻¹ * (x⁻¹ * a * x) * b) * a by group,
            hinv a x ha2 ha4 hxa, hba_a]
          group
        · rw [show (x * b * a)⁻¹ * b * (x * b * a) = a⁻¹ * (b⁻¹ * (x⁻¹ * b * x) * b) * a by group,
            hinv b x hb2 hb4 hxb, show b⁻¹ * b⁻¹ * b = b⁻¹ by group, hab_b]
    -- step 3: if `x * w ∈ Z` for some `w ∈ Q`, then `x = (x * w) * w⁻¹ ∈ Q ⊔ Z`
    have ha_mem : a ∈ Q := Subgroup.subset_closure (by simp)
    have hb_mem : b ∈ Q := Subgroup.subset_closure (by simp)
    have hw : ∀ x w : H, w ∈ Q → x * w ∈ Z → x ∈ Q ⊔ Z := by
      intro x w hw hz
      rw [show x = x * w * w⁻¹ by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hz) (Subgroup.mem_sup_left (Q.inv_mem hw))
    rw [eq_top_iff]
    intro x _
    rcases hstep2 x with h | h | h | h
    · exact Subgroup.mem_sup_right h
    · exact hw x a ha_mem h
    · exact hw x b hb_mem h
    · exact hw x (b * a) (Q.mul_mem hb_mem ha_mem) (by rwa [mul_assoc] at h)

  -- Z is abelian. proof by contradiction:
  -- 1. Z does not contain an element of order 4
  -- 2. is Z is non-abelian, then it is Hamiltonian
  -- 3. a Hamiltonian group contains an element of order 4 (consequence of `hamiltonian_contains_quaternion`)
  -- 4. contradiction
  -- NOTE: done by Claude
  have hz_abelian : IsMulCommutative Z := by
    -- step 1: `Z` has no element of order `4`
    -- if `z ∈ Z` has order `4`, then `b` conjugates `a * z` to `a⁻¹ * z ∉ ⟨a * z⟩`
    have hno4 : ∀ z : H, z ∈ Z → orderOf z ≠ 4 := by
      intro z hzZ hz4
      have hza : Commute a z := ((hmemZ z).mp hzZ).1.symm
      have hzb : Commute z b := ((hmemZ z).mp hzZ).2
      have hz4' : z ^ 4 = 1 := hz4 ▸ pow_orderOf_eq_one z
      have hz2 : z ^ 2 ≠ 1 := fun h => by
        have := orderOf_le_of_pow_eq_one (by norm_num) h
        omega
      -- `z = a` is impossible, since `z` commutes with `b` and `a` does not
      have hza' : z ≠ a := fun h => hab (h ▸ hzb.eq)
      have hconj : b⁻¹ * (a * z) * b⁻¹⁻¹ = a⁻¹ * z := by
        rw [inv_inv, show b⁻¹ * (a * z) * b = (b⁻¹ * a * b) * (b⁻¹ * (z * b)) by group,
          hinv a b ha2 ha4 (fun h => hab h.eq.symm), hzb.eq, inv_mul_cancel_left]
      obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.mp
        ((hamil.all_subgroups_normal (Subgroup.zpowers (a * z))).conj_mem _
          (Subgroup.mem_zpowers _) b⁻¹)
      rw [hconj] at ht
      have ht' : (a * z) ^ (t % 4) = a⁻¹ * z := by
        rw [← ht]
        conv_rhs => rw [← Int.emod_add_ediv_mul t 4]
        rw [zpow_add, zpow_mul', show (4 : ℤ) = ((4 : ℕ) : ℤ) by rfl, zpow_natCast,
          hza.mul_pow, ha4, hz4', mul_one, one_zpow, mul_one]
      rcases (by omega : t % 4 = 0 ∨ t % 4 = 1 ∨ t % 4 = 2 ∨ t % 4 = 3) with h | h | h | h <;>
        rw [h] at ht'
      · -- `1 = a⁻¹ * z`, so `z = a`
        apply hza'
        rw [zpow_zero] at ht'
        rw [← mul_left_cancel_iff (a := a⁻¹), ← ht', inv_mul_cancel]
      · -- `a * z = a⁻¹ * z`, so `a ^ 2 = 1`
        rw [zpow_one, mul_left_inj] at ht'
        exact ha2 (by rw [sq, mul_eq_one_iff_eq_inv]; exact ht')
      · -- `a ^ 2 * z ^ 2 = a⁻¹ * z`, so `z = a`
        rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, zpow_natCast, hza.mul_pow] at ht'
        apply hza'
        calc z = a ^ 4 * z := by rw [ha4, one_mul]
          _ = a * a * (a ^ 2 * z ^ 2) * z⁻¹ := by group
          _ = a * a * (a⁻¹ * z) * z⁻¹ := by rw [ht']
          _ = a := by group
      · -- `a ^ 3 * z ^ 3 = a⁻¹ * z`, so `z ^ 2 = 1`
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by rfl, zpow_natCast, hza.mul_pow] at ht'
        apply hz2
        calc z ^ 2 = a ^ 4 * z ^ 2 := by rw [ha4, one_mul]
          _ = a * (a ^ 3 * z ^ 3) * z⁻¹ := by group
          _ = a * (a⁻¹ * z) * z⁻¹ := by rw [ht']
          _ = 1 := by group
    -- step 2: if `Z` were non-abelian, it would be Hamiltonian
    -- (subgroups of `Z` are normal in `H`, hence in `Z`), so it would contain an element of order `4`
    by_contra hnc
    have : Hamiltonian Z :=
      { exists_noncomm := by
          by_contra h
          push Not at h
          exact hnc ⟨⟨h⟩⟩
        all_subgroups_normal := fun K => by
          have := (hamil.all_subgroups_normal (K.map Z.subtype)).comap Z.subtype
          rwa [Subgroup.comap_map_eq_self_of_injective Z.subtype_injective] at this }
    obtain ⟨x, -, -, -, -, -, -, -, hx4, -, -, -⟩ := hamiltonian_contains_quaternion Z
    exact hno4 x x.2 (by rw [Subgroup.orderOf_coe]; exact hx4)
  sorry

