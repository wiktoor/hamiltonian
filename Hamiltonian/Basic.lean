import Mathlib

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

universe u

/--
A group is Hamiltonian iff all its cyclic subgroups are Hamiltonian.
-/
theorem hamiltonian_iff (H : Type u) [Group H] :
    Hamiltonian H ↔ NonAbelianGroup H ∧ ∀ g : H, (Subgroup.zpowers g).Normal := by
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

theorem hamiltonian_classification (H : Type u) [Group H] [Hamiltonian H] :
    ∃ U V : CommGrpCat.{u},
      (∀ x : U, Odd (orderOf x)) ∧
      (∀ x : V, x ^ 2 = 1) ∧
      Nonempty (H ≃* Q8 × U × V) := by
  sorry
