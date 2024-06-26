import Mathlib.Tactic

namespace One

class Semigroup (G: Type) (f : G → G → G) where
  assoc : ∀ (a b c : G), f (f a b) c = f a (f b c)

class Monoid (G: Type) (f : G → G → G) where
  e : G
  assoc : ∀ (a b c : G), f (f a b) c = f a (f b c)
  identity : ∀ a : G, f a e = a ∧ f e a = a

class Group (G : Type) (f : G → G → G) where
  e : G
  assoc : ∀ (a b c : G), f (f a b) c = f a (f b c)
  identity : ∀ a : G, f a e = a ∧ f e a = a
  inverse : ∀ a : G, ∃ i : G, f a i = e ∧ f i a = e

class AbelianGroup (G : Type) (f : G → G → G) where
  e : G
  assoc : ∀ (a b c : G), f (f a b) c = f a (f b c)
  identity : ∀ a : G, f a e = a ∧ f e a = a
  inverse : ∀ a : G, ∃ i : G, f a i = e ∧ f i a = e
  commutative : ∀ (a b : G), f a b = f b a

theorem mul_id_eq_self {G : Type} {f : G → G → G} (a : G)  [Monoid G f] : f a (Monoid.e f) = a ∧ f (Monoid.e f) a = a :=
by exact Monoid.identity a

#check Monoid.e
theorem Monoid_id_unique (G : Type) (f : G → G → G) (i : G) (a : G) [Monoid G f]:
  f a i = a ∧ f i a = a → (i = Monoid.e f) := by sorry
  /-intro h
  have h₀ : f a (Monoid.e f) = a ∧ f (Monoid.e f) a = a := by rw [mul_id_eq_self a]
  specialize h₀ a
  rcases h with ⟨h₁, h₂⟩
  rcases h₀ with ⟨ h₃, h₄ ⟩-/

end One
namespace Trial123

class Group (G : Type*) extends Mul G, One G, Inv G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(mul_one : ∀ a : G, a * 1 = a)
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

variable {G : Type} [Group G] (a b c : G)

theorem mul_left_inv :  a⁻¹ * a = 1 := Group.mul_left_inv a
theorem mul_assoc  : a * b * c = a * (b * c) := Group.mul_assoc a b c
theorem one_mul: 1 * a = a := Group.one_mul a
theorem mul_one : a * 1 = a := Group.mul_one a

theorem mul_left_cancel (h : a * b = a * c) : b = c := by
  have h₀ : a⁻¹ * (a * b) = a⁻¹ * (a * c) := by
    rw [h]
  rw [← mul_assoc, ← mul_assoc] at h₀
  repeat rw [mul_left_inv, one_mul, one_mul] at h₀
  exact h₀

theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by
  have : a⁻¹ * a * b = a⁻¹ * c := by
    rw [mul_left_inv, one_mul, h]
  rw [mul_assoc] at this
  exact mul_left_cancel a⁻¹ (a*b) c this

theorem mul_right_inv : a * a⁻¹ = 1 := by
  apply mul_eq_of_eq_inv_mul
  rw [mul_one]

theorem id_unique (h : a * e = a) : e = 1 := by
  have h₀ := mul_one a
  have h₁ : a * e = a * 1 := by rw [h₀]; exact h
  have h₂ : a⁻¹ * (a * e) = a⁻¹ * (a * 1) := by rw [h₁]
  repeat rw [← mul_assoc, mul_left_inv, one_mul] at h₂
  exact h₂

theorem id_unique' (h : e * a = a) : e = 1 := by sorry

theorem inv_unique (h : a * i = 1) : i = a⁻¹ := by
  have h₀: a⁻¹ * (a * i) = a⁻¹ := by rw [h, mul_one]
  rw [← mul_assoc, mul_left_inv, one_mul] at h₀
  exact h₀

theorem inv_unique' (h : i * a = 1) : i = a⁻¹ := by sorry

end Trial123
