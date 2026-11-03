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

theorem hamiltonian_classification' (U V : CommGrpCat.{u})
    (hU : ∀ x : U, Odd (orderOf x))
    (hV : ∀ x : V, x ^ 2 = 1) :
    Hamiltonian (Q8 × U × V) := by
  sorry

theorem hamiltonian_classification (H : Type u) [Group H] [Hamiltonian H] :
    ∃ U V : CommGrpCat.{u},
      (∀ x : U, Odd (orderOf x)) ∧
      (∀ x : V, x ^ 2 = 1) ∧
      Nonempty (H ≃* Q8 × U × V) := by
  sorry
